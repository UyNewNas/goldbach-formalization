from pathlib import Path
import base64,hashlib,io,json,tarfile
root=Path('/workspace/p2-9-20261125')
module='ImbalancedChen.P2FiniteMarkedGamma5UnitTailProduct'
rel=Path(*module.split('.'))
registry=root/'.lake/p2-private/records.json'
expected_object='5f696bded2b42517cec47376df4f941277673109a526ae53260fa40883e987a2'
sha=lambda b:hashlib.sha256(b).hexdigest()
regbytes=registry.read_bytes()
assert sha(regbytes)=='e95c1c2aeaad29c651c897ec0c2ec6669f0719a5554148c68c4421745f3b5ed8'
record=json.loads(regbytes)[module]
src=root/rel.with_suffix('.lean')
obj=root/'.lake/p2-private/lib'/rel.with_suffix('.olean')
members={}
origins={}
def take(name,path,expected=None):
    path=Path(path);b=path.read_bytes()
    assert expected is None or sha(b)==expected,(str(path),sha(b),expected)
    assert name not in members and not name.startswith('/') and '..' not in Path(name).parts
    members[name]=b
    origins[name]={'origin':str(path),'bytes':len(b),'sha256':sha(b)}
take('source/'+str(rel.with_suffix('.lean')),src,record['source_sha256'])
take('objects/'+str(rel.with_suffix('.olean')),obj,expected_object)
assert record['object_sha256']==expected_object
receipt_path=root/'.lake/p2-private/audit'/module/'latest.json'
receipt=None
if receipt_path.is_file():
    take('original-audit/latest.json',receipt_path)
    receipt=json.loads(members['original-audit/latest.json'])
    assert receipt.get('accepted')is True and receipt['object_sha256']==expected_object
    for name,digest in receipt['artifacts'].items():
        take('original-artifacts/'+name,root/name,digest)
members['ORIGINAL_RECORD.json']=(json.dumps(record,sort_keys=True,indent=2)+'\n').encode()
binding={
 'schema':'p29_unittailproduct_existing_object_export_v1',
 'module':module,'object_sha256':expected_object,
 'source_sha256':record['source_sha256'],
 'source_git_blob':hashlib.sha1(b'blob '+str(len(members['source/'+str(rel.with_suffix('.lean'))])).encode()+b'\0'+members['source/'+str(rel.with_suffix('.lean'))]).hexdigest(),
 'registry_origin':str(registry),'registry_sha256':sha(regbytes),
 'original_audit_exists':receipt is not None,
 'original_audit_accepted':receipt.get('accepted')if receipt else None,
 'original_record_copied_without_field_change':True,
 'origin_files':origins,
 'source_recompilations':0,'kernel_replays':0,'new_manuscript_credit':0,
 'scope':'Read-only transfer of the existing qualified UnitTailProduct object; receiver must retain original proof/runtime/dependency acceptance boundaries.'}
for name,meta in origins.items():
    assert sha(Path(meta['origin']).read_bytes())==meta['sha256'],'origin changed '+name
assert sha(registry.read_bytes())==sha(regbytes),'original registry changed during read-only export'
binding['all_origin_bytes_and_registry_unchanged']=True
members['BINDING_RECEIPT.json']=(json.dumps(binding,sort_keys=True,indent=2)+'\n').encode()
manifest={'schema':'p29_unittailproduct_object_archive_manifest_v1','module':module,
 'files':{n:{'bytes':len(b),'sha256':sha(b)}for n,b in sorted(members.items())},
 'source_recompilations':0,'kernel_replays':0,'new_manuscript_credit':0}
members['FILE_MANIFEST.json']=(json.dumps(manifest,sort_keys=True,indent=2)+'\n').encode()
buffer=io.BytesIO()
with tarfile.open(fileobj=buffer,mode='w:gz')as tf:
    for name,b in sorted(members.items()):
        ti=tarfile.TarInfo(name);ti.size=len(b);ti.mtime=0;ti.mode=0o644;tf.addfile(ti,io.BytesIO(b))
archive=buffer.getvalue()
print(json.dumps({'archive_format':'tar.gz','archive_bytes':len(archive),'archive_sha256':sha(archive),
 'members':len(members),'file_manifest_sha256':sha(members['FILE_MANIFEST.json']),
 'binding_receipt_sha256':sha(members['BINDING_RECEIPT.json']),'object_sha256':expected_object,'no_lean_invocation':True}))
print('P29_UNITTAILPRODUCT_ARCHIVE_BASE64')
print(base64.b64encode(archive).decode())
