#!/usr/bin/env python3
"""Transfer only frozen normal-record metadata after the successful physical read.
No source/object/log/snapshot body is read; no Lean, subprocess or remote writes.
"""
from pathlib import Path
import base64, hashlib, io, json, lzma, re, tarfile
CACHE_SCHEMA = 2
EXTERNAL_CACHE_SCHEMA = 3
ROOT = Path('/workspace/p2-saving16-20261125')
REGISTRY = ROOT / '.lake/p2-private/records.json'
FIRST_TASK = '667d7b5d62ff404fa57631ddc579db9f'
FIRST_STDOUT_SHA256 = 'fd2bec4a1734d8fa93a90a67960b532d14ed7d68c3dfd581ab731557fd85bfa2'
FIRST_STDOUT_BLOB = 'fdb52b4b39dd3e0ce3a93680d6ca20b23d66e1aa'
FIRST_SCRIPT_BLOB = '081b951c2f40d8f300e3fc504a91e3729cbe7bc3'
TARGETS = {
 'ImbalancedChen.ActualPrimePolyhedralTestFunctions': {
   'canonical_record_sha256':'8a420f88c97482a5949f51821e748a8fc219f4c135dc0dff91c530fd86fd9e95',
   'closure_signature':'144bbc68377dd301ff84bdd6d404b43686fe2653d7a8599703a2b2b89621def4'},
 'ImbalancedChen.AffinePrimeWallReserve': {
   'canonical_record_sha256':'f6978a7a65cc13f45d39ee81e5b9ce70ffc06873d346573ed87c3129a43d0899',
   'closure_signature':'9c662c0a50da62b2649208afdf57dbab944d48348912fca2eeb7f11c1b11c91e'}
}
FIRST_SUMMARY = json.loads('{"archive_bytes": 3353860, "archive_sha256": "98da0a90ff9138985b8f28b06df6bff4dca5a0cc010a8c88fca58afb0384991c", "errors_count": 0, "external_snapshot_sha256": "ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27", "manifest_sha256": "66af25ddf940986b0cfb8939ed65306d053de0ac9debd6aefcd66d9dbdc3670a", "members": 65, "module_count": 54, "no_new_lean": true, "registry_sha256": "8a62e3f63345dfc78a9eb94ce5ef6f6da28500255caf14451efe2bbcba803e69", "remote_writes": 0, "schema": "p29-affine-existing-closure-readonly-v1", "status": "EXACT_ORIGINAL_CLOSURE_RECONSTRUCTED", "target_reconstructions": {"ImbalancedChen.ActualPrimePolyhedralTestFunctions": {"current_files_digest": "d74c3438bc6173f6f5cbef2caff5ff2ab4306e45236acb1a2d738aacb8dd131c", "modules": 52, "records_digest": "d74c3438bc6173f6f5cbef2caff5ff2ab4306e45236acb1a2d738aacb8dd131c", "records_match_current": true}, "ImbalancedChen.AffinePrimeWallReserve": {"current_files_digest": "6c1afc8e6ebb6763c450877d9ddcf52ffd5ff06770364f11d923cf00ab994422", "modules": 53, "records_digest": "6c1afc8e6ebb6763c450877d9ddcf52ffd5ff06770364f11d923cf00ab994422", "records_match_current": true}}}')

def json_digest(payload: dict) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()

def closure_signature(record: dict) -> str:
    """Bind the source/object to the recursively frozen dependency environment.

    A parent's .olean bytes can remain identical when an imported definition
    changes. Object hashes alone therefore do not identify the proof context.
    This helper must only be called for actual compilation snapshots or an
    explicitly evidenced historical migration, never to backfill an old probe
    with whatever dependency objects happen to exist now.
    """
    payload = {key: record[key] for key in (
        "module", "source_sha256", "object_sha256", "toolchain", "dependency_signatures")}
    payload["cache_schema"] = record.get("cache_schema", CACHE_SCHEMA)
    if payload["cache_schema"] == EXTERNAL_CACHE_SCHEMA:
        payload["external_snapshot"] = record["external_snapshot"]
    return json_digest(payload)


def sha(data):
    return hashlib.sha256(data).hexdigest()

def stamp(path):
    s=path.stat()
    return [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]

start=stamp(REGISTRY)
raw=REGISTRY.read_bytes()
assert stamp(REGISTRY)==start, 'Registry changed during the record-only read'
registry_sha=sha(raw)
all_records=json.loads(raw)
del raw
picked={}
nodes={}
active=set()
order=[]
toolchain=all_records['ImbalancedChen.AffinePrimeWallReserve']['toolchain']
for module,pin in TARGETS.items():
    assert json_digest(all_records[module])==pin['canonical_record_sha256'], ('Original target record changed',module)
    assert all_records[module]['closure_signature']==pin['closure_signature']

def visit(module, required_signature=None):
    if module in active:
        raise RuntimeError('Cycle in the already source-verified project record closure: '+module)
    if module in picked:
        assert required_signature is None or picked[module]['closure_signature']==required_signature
        return
    assert len(picked)<54 and re.fullmatch(r"ImbalancedChen\.[A-Za-z_][A-Za-z0-9_.']*",module)
    record=all_records[module]
    assert record['module']==module and record['exit_code']==0
    assert record['toolchain']==toolchain
    assert record['closure_signature']==closure_signature(record)
    assert required_signature is None or record['closure_signature']==required_signature
    assert set(record['deps'])==set(record['dependency_signatures'])
    if record.get('cache_schema')==EXTERNAL_CACHE_SCHEMA:
        binding=record['external_snapshot']
        assert binding['snapshot_sha256']==FIRST_SUMMARY['external_snapshot_sha256']
        assert record['external_check']['status']=='PASSED_BATCH_PRE_POST'
        assert record['external_check']['before']==binding==record['external_check']['after']
    else:
        assert record.get('cache_schema')==CACHE_SCHEMA
    picked[module]=record
    active.add(module)
    for dep,signature in record['dependency_signatures'].items():
        visit(dep,signature)
        assert record['deps'][dep]==picked[dep]['object_sha256']
    active.remove(module)
    closure=set(record['deps'])
    for dep in record['deps']:
        closure.update(nodes[dep]['dependency_closure'])
    files={dep:{key:picked[dep][key] for key in ('source_sha256','object_sha256')}for dep in closure}
    original=record.get('dependency_file_check')
    if original is not None:
        assert original['modules']==len(closure)
        assert original['before_matches_records'] is True and original['after_matches_records'] is True
        assert original['expected_sha256']==original['before_sha256']==original['after_sha256']==json_digest(files)
    nodes[module]={
      'module':module,
      'source_verified_in_first_read':str(ROOT/(module.replace('.','/')+'.lean')),
      'source_sha256':record['source_sha256'],
      'object_verified_in_first_read':str(ROOT/'.lake/p2-private/lib'/(module.replace('.','/')+'.olean')),
      'object_sha256':record['object_sha256'],
      'original_record_source':record['source'], 'original_record_object':record['object'],
      'record_canonical_sha256':json_digest(record),
      'closure_signature':record['closure_signature'],
      'direct_project_imports_verified_in_first_read':list(record['deps']),
      'dependency_signatures':record['dependency_signatures'],
      'dependency_closure':sorted(closure),
      'dependency_file_map_digest':json_digest(files),
      'normal_log_path_from_original_record':record.get('log'),
      'normal_attempts_from_original_record':record.get('attempts',[]),
      'new_strict_compile_in_original_record':record.get('new_strict_compile'),
      'provenance':record.get('provenance'),
    }
    order.append(module)

for module,pin in TARGETS.items():
    visit(module,pin['closure_signature'])
assert len(picked)==54 and len(order)==54
for module in TARGETS:
    old=FIRST_SUMMARY['target_reconstructions'][module]
    node=nodes[module]
    assert len(node['dependency_closure'])==old['modules']
    assert node['dependency_file_map_digest']==old['records_digest']==old['current_files_digest']
    assert old['records_match_current'] is True
assert stamp(REGISTRY)==start
with REGISTRY.open('rb') as f:
    assert hashlib.file_digest(f,'sha256').hexdigest()==registry_sha
assert stamp(REGISTRY)==start

report={
 'schema':'p29_affine_frozen_record_map_transport_v1',
 'status':'EXPORTED_54_FROZEN_RECORDS_REUSING_FIRST_PHYSICAL_READ',
 'first_physical_read':{'task':FIRST_TASK,'stdout_git_blob':FIRST_STDOUT_BLOB,
   'stdout_sha256':FIRST_STDOUT_SHA256,'script_git_blob':FIRST_SCRIPT_BLOB,
   'exit_code':4,'exit4_reason':'Output-size gate only after zero-error physical closure validation.',
   'summary':FIRST_SUMMARY,
   'original_65_member_archive_received':False,'original_external_snapshot_body_received':False},
 'this_transport':{'only_remote_file_read':str(REGISTRY),'registry_sha256':registry_sha,
   'registry_stat':start,'registry_same_bytes_as_first_read':registry_sha==FIRST_SUMMARY['registry_sha256'],
   'selected_original_target_record_pins':TARGETS,
   'semantic_binding':'Both exact target records and recursively frozen source/object/toolchain/closure signatures match the first source-verified graph. Other original normal metadata is transferred as read, with per-record canonical SHA256.',
   'project_sources_read':0,'project_objects_read':0,'normal_logs_read':0,
   'external_snapshot_bodies_read':0,'Lean_invocations':0,'remote_writes':0},
 'toolchain':toolchain,'module_count':54,'topological_order':order,'modules':nodes,
 'external_binding_from_original_targets':picked['ImbalancedChen.AffinePrimeWallReserve']['external_snapshot'],
 'current_physical_stability_rechecked':False,
 'current_receiving_qualification':False,'new_manuscript_credit':0,
 'target_kernel_full_owned_missing_from_prior_canonical_locations':True,
 'absence_scope':'Prior bounded two-key read only; not a global absence claim.'}
members={
 'RECORD_MAP.json':(json.dumps(report,sort_keys=True,indent=2)+'\n').encode(),
 'SELECTED_ORIGINAL_NORMAL_RECORDS.json':(json.dumps(picked,sort_keys=True,indent=2)+'\n').encode(),
}
manifest={name:{'bytes':len(data),'sha256':sha(data)}for name,data in members.items()}
members['MANIFEST.json']=(json.dumps(manifest,sort_keys=True,indent=2)+'\n').encode()
stream=io.BytesIO()
with tarfile.open(fileobj=stream,mode='w')as tf:
    for name,data in sorted(members.items()):
        item=tarfile.TarInfo(name);item.size=len(data);item.mtime=0;item.mode=0o444
        tf.addfile(item,io.BytesIO(data))
archive=lzma.compress(stream.getvalue(),preset=6)
meta={'schema':report['schema'],'status':report['status'],'archive_bytes':len(archive),
 'archive_sha256':sha(archive),'manifest':manifest,'module_count':54,
 'registry_sha256':registry_sha,'first_physical_read_stdout_sha256':FIRST_STDOUT_SHA256,
 'project_sources_objects_logs_or_external_bodies_reread':0,'Lean_invocations':0,'remote_writes':0}
print('P29_AFFINE_RECORD_MAP_META '+json.dumps(meta,sort_keys=True),flush=True)
assert len(archive)<1400000, 'Metadata-only compressed transport exceeds output bound'
print('P29_AFFINE_RECORD_MAP_ARCHIVE_BASE64 '+base64.b64encode(archive).decode(),flush=True)
