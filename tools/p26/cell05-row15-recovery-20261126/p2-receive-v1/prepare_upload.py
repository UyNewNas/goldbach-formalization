#!/usr/bin/env python3
"""Prepare immutable P2 source controls and private upload commands; submit nothing."""
from pathlib import Path
import ast
import base64
import hashlib
import importlib.util
import json
import os
import sys
import tarfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PRIVATE = Path('/tmp/p26-row15-transfer-557a12f3bcd7')
CAPSULE = PRIVATE / 'rows15-provider-v1.tar.xz'
COMMANDS = PRIVATE / 'p2-upload-v1'
REMOTE = '/workspace/p26-continuation-557a12f3bcd7/cell05-rows15-private-receive-v1'
EXPECTED = {'bytes': 2397884, 'sha256': 'b41f83e3ec17764d06cfbd6b095c7cc499594de0c5060f78327fa0ffd351dfdd'}


def pin(body):
    return {'bytes': len(body), 'sha256': hashlib.sha256(body).hexdigest()}


def json_bytes(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def save(path, body, private=False):
    if path.is_symlink():
        raise RuntimeError('Symlink output rejected')
    if path.exists():
        if path.read_bytes() != body:
            raise RuntimeError('Refuse conflicting prepared file: ' + str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True, mode=0o700 if private else 0o755)
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                             0o600 if private else 0o644)
        with os.fdopen(descriptor, 'wb') as stream:
            stream.write(body)
    if path.read_bytes() != body:
        raise RuntimeError('Prepared file readback differs')
    return {'path': str(path), **pin(body)}


BOOTSTRAP = '''from pathlib import Path
import base64, hashlib, json, os, stat, sys
sys.dont_write_bytecode = True
def need(value, message):
    if not value: raise RuntimeError(message)
def pin(body): return {'bytes':len(body),'sha256':hashlib.sha256(body).hexdigest()}
def safe(path):
    need(path.is_absolute() and '..' not in path.parts, 'Noncanonical new root')
    for p in [*reversed(path.parents),path]:
        if not p.exists() and not p.is_symlink(): continue
        mode=p.lstat().st_mode
        need(not stat.S_ISLNK(mode), 'Symlink rejected')
        if p!=path: need(stat.S_ISDIR(mode), 'Nondirectory ancestor')
    return path
need(sys.flags.optimize==0,'Run without Python optimization')
root=safe(Path(REMOTE)); control=root/'control'
need(set(PAYLOAD)=={'receive_rows15.py','evidence_io.py','RECEIVE_MANIFEST.json','ORIGINAL_REPORT.json','SOURCE_MANIFEST.json'},'Wrong control members')
bodies={name:base64.b64decode(row['base64'],validate=True) for name,row in PAYLOAD.items()}
for name,body in bodies.items(): need(pin(body)=={k:PAYLOAD[name][k] for k in ('bytes','sha256')},'Control transport pin differs')
need(pin(bodies['SOURCE_MANIFEST.json'])==SOURCE_PIN,'Source manifest differs')
source=json.loads(bodies['SOURCE_MANIFEST.json'])
need(source['remote_root']==REMOTE and source['schema']=='cell05_rows15_receive_source_v1','Wrong source root')
need({r['relative_path'] for r in source['files']}==set(bodies)-{'SOURCE_MANIFEST.json'} and len(source['files'])==4,'Wrong source inventory')
for row in source['files']: need(pin(bodies[row['relative_path']])=={k:row[k] for k in ('bytes','sha256')},'Source member pin differs')
if root.exists():
    need(root.is_dir(),'Non-directory receive root')
    for p in root.rglob('*'):
        safe(p)
        if p.is_dir(): need(p==control,'Refuse redeployment after receiver data exists')
        else:
            need(p.is_file() and p.parent==control and p.name in bodies,'Unknown existing receive file')
            need(p.read_bytes()==bodies[p.name],'Conflicting existing control file')
fs=os.statvfs(root if root.exists() else root.parent)
need(fs.f_bavail*fs.f_frsize>=6*1024*1024,'Need 6 MiB free for bounded receiver storage; no cleanup performed')
root.mkdir(mode=0o700,exist_ok=True); control.mkdir(mode=0o700,exist_ok=True)
for name,body in sorted(bodies.items()):
    path=safe(control/name)
    if path.exists(): need(path.read_bytes()==body,'Existing control bytes differ')
    else:
        fd=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)
        with os.fdopen(fd,'wb') as stream:
            stream.write(body); stream.flush(); os.fsync(stream.fileno())
    need(path.read_bytes()==body,'Control readback differs')
print(json.dumps({'status':'EXACT_RECEIVER_CONTROLS_INSTALLED','remote_root':REMOTE,'source_manifest':SOURCE_PIN,'source_members':5,'Lean_commands':0},sort_keys=True))
'''

LAUNCHER = '''from pathlib import Path
import hashlib,json,runpy,stat,sys
sys.dont_write_bytecode=True
def need(value,message):
    if not value: raise RuntimeError(message)
def body(path):
    for p in [*reversed(path.parents),path]:
        mode=p.lstat().st_mode
        need(not stat.S_ISLNK(mode),'Source symlink rejected')
        if p!=path: need(stat.S_ISDIR(mode),'Nondirectory source ancestor')
    need(stat.S_ISREG(path.lstat().st_mode),'Nonregular source file')
    return path.read_bytes()
def pin(data): return {'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
need(sys.flags.optimize==0,'Run without Python optimization')
control=Path(REMOTE)/'control'
raw=body(control/'SOURCE_MANIFEST.json')
need(pin(raw)==SOURCE_PIN,'Frozen source manifest changed')
source=json.loads(raw)
need(source['remote_root']==REMOTE and len(source['files'])==4,'Wrong source scope')
need({r['relative_path'] for r in source['files']}=={'receive_rows15.py','evidence_io.py','RECEIVE_MANIFEST.json','ORIGINAL_REPORT.json'},'Wrong source inventory')
for row in source['files']: need(pin(body(control/row['relative_path']))=={k:row[k] for k in ('bytes','sha256')},'Frozen source member changed')
sys.path.insert(0,str(control))
sys.argv=[str(control/'receive_rows15.py')]+ARGS
runpy.run_path(str(control/'receive_rows15.py'),run_name='__main__')
'''


def command(script):
    ast.parse(script)
    data = ("python3 -B - <<'P26_CELL05_PRIVATE_RECEIVE'\n" + script +
            "\nP26_CELL05_PRIVATE_RECEIVE\n").encode()
    if len(data) >= 120000:
        raise RuntimeError('Prepared command approaches the single-argument size limit')
    return data


def main():
    raw = CAPSULE.read_bytes()
    if pin(raw) != EXPECTED:
        raise RuntimeError('Private capsule pin differs')
    transferred = json.loads((HERE.parent / 'TRANSFER_RESULT.json').read_bytes())
    if transferred['status'] != 'PASS_EXACT_CAPSULE_RECOVERED_OUTSIDE_REPOSITORY':
        raise RuntimeError('Missing actual local transfer verification')
    with tarfile.open(CAPSULE, 'r:xz') as archive:
        archive_members = archive.getmembers()
        manifest_raw = archive.extractfile('CAPSULE_MANIFEST.json').read()
        manifest = json.loads(manifest_raw)
    chunks = [{'index': index, 'offset': offset, **pin(raw[offset:offset + 75000])}
              for index, offset in enumerate(range(0, len(raw), 75000))]
    mappings_raw = (json.dumps(manifest['mappings'], sort_keys=True, separators=(',', ':')) + '\n').encode()
    request = {'schema': 'cell05_rows15_receive_request_v1', 'remote_root': REMOTE, 'archive': EXPECTED,
               'chunk_bytes_max': 75000, 'chunks': chunks, 'capsule_manifest': pin(manifest_raw),
               'canonical_mappings': pin(mappings_raw), 'original_mappings': 496,
               'source_anchors': {key: manifest[key] for key in
                                  ('source_archive', 'source_export_manifest', 'source_run', 'source_success')},
               'archive_expanded_bytes': sum(row.size for row in archive_members),
               'original_report': pin((HERE / 'ORIGINAL_REPORT.json').read_bytes()),
               'local_verified_transfer_result': pin((HERE.parent / 'TRANSFER_RESULT.json').read_bytes()),
               'regular_members': 267, 'payload_members': 266, 'archive_extraction_authorized': False,
               'provider_installation_authorized': False, 'Lean_commands': 0, 'new_Lean_acceptance': 0}
    save(HERE / 'RECEIVE_MANIFEST.json', json_bytes(request))
    sys.path.insert(0, str(HERE))
    spec = importlib.util.spec_from_file_location('rows15_receive_candidate', HERE / 'receive_rows15.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    actual_members = module.verify_capsule(CAPSULE, request)
    if len(actual_members) != 267:
        raise RuntimeError('Local final verification did not cover 267 members')
    source = {'schema': 'cell05_rows15_receive_source_v1', 'remote_root': REMOTE,
              'files': [{'relative_path': name, **pin((HERE / name).read_bytes())}
                        for name in sorted(module.SOURCE_NAMES)], 'Lean_commands': 0}
    source_pin = save(HERE / 'SOURCE_MANIFEST.json', json_bytes(source))
    identity = {key: source_pin[key] for key in ('bytes', 'sha256')}
    payload = {name: {**pin((HERE / name).read_bytes()), 'base64': base64.b64encode((HERE / name).read_bytes()).decode()}
               for name in sorted(module.SOURCE_NAMES | {'SOURCE_MANIFEST.json'})}
    prefix = 'REMOTE=' + repr(REMOTE) + '\nSOURCE_PIN=' + repr(identity) + '\n'
    prepared = []
    deploy = prefix + 'PAYLOAD=' + repr(payload) + '\n' + BOOTSTRAP
    prepared.append({'operation': 'deploy_controls', **save(COMMANDS / '000_DEPLOY_CONTROLS.sh', command(deploy), private=True)})
    for row in chunks:
        part = raw[row['offset']:row['offset'] + row['bytes']]
        args = ['chunk', str(row['index']), base64.b64encode(part).decode()]
        cmd = command(prefix + 'ARGS=' + repr(args) + '\n' + LAUNCHER)
        prepared.append({'operation': 'upload_chunk', 'index': row['index'],
                         **save(COMMANDS / ('%03d_UPLOAD_%03d.sh' % (row['index'] + 1, row['index'])), cmd, private=True)})
    for filename, operation in [('033_FINALIZE.sh', 'finalize'), ('READONLY_INSPECT.sh', 'inspect')]:
        cmd = command(prefix + 'ARGS=' + repr([operation]) + '\n' + LAUNCHER)
        prepared.append({'operation': operation, **save(COMMANDS / filename, cmd, private=True)})
    plan = {'schema': 'cell05_rows15_P2_upload_plan_v1', 'status': 'LOCAL_PREPARED_NOT_SUBMITTED_REQUIRES_ROOT_REVIEW',
            'remote_root': REMOTE, 'remote_archive': REMOTE + '/rows15-provider-v1.tar.xz',
            'private_local_archive': str(CAPSULE), 'archive': EXPECTED, 'source_manifest': source_pin,
            'commands': prepared, 'upload_chunk_count': len(chunks), 'largest_chunk_bytes': 75000,
            'max_command_bytes': max(row['bytes'] for row in prepared), 'command_bytes_upper_bound': 120000,
            'payload_bytes_on_P2_at_completion': 2 * len(raw), 'expanded_members_written_to_disk': 0,
            'source_control_bytes': sum(row['bytes'] for row in source['files']) + source_pin['bytes'],
            'deployment_requires_free_bytes': 6 * 1024 * 1024,
            'limits': {'timeout_seconds': 120, 'memory_mb': 512, 'cpu_threads': 1},
            'queue_policy': {'capacity': 8, 'reserve_at_least_slots': 2, 'max_global_outstanding_before_submit': 5,
                             'check_fresh_system_info_before_each_submit': True, 'cancel_existing_tasks': False,
                             'priority': 'Root Shape repair task first; upload only after explicit root confirmation'},
            'unknown_submission_requires_read_only_recovery_before_any_resubmission': True,
            'automatic_approval_rejection_requires_stop_and_report': True,
            'P1_original_retained_until_P2_confirmed': True, 'P2_tasks_submitted': 0, 'Lean_commands': 0,
            'new_Lean_acceptance': 0, 'local_final_member_verifier': {'status': 'PASS', 'regular_members': 267,
                                                                  'source_anchors': 4, 'original_mappings': 496},
            'repo_contains_capsule_payload_or_payload_commands': False}
    plan_pin = save(HERE / 'P2_UPLOAD_PLAN.json', json_bytes(plan))
    print(json.dumps({'status': plan['status'], 'remote_root': REMOTE, 'source_manifest': source_pin,
                      'plan': plan_pin, 'commands': len(prepared), 'chunks': len(chunks),
                      'max_command_bytes': plan['max_command_bytes'], 'P2_tasks_submitted': 0}, sort_keys=True))


if __name__ == '__main__':
    main()
