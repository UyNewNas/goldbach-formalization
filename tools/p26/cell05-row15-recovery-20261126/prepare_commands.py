#!/usr/bin/env python3
"""Prepare exact local-authored upload/deployment commands; do not contact a cloud."""
from pathlib import Path
import ast
import base64
import hashlib
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).absolute().parent
REPO = HERE.parents[2]
SOURCE = REPO / 'docs/verification/20261126-p26/scalable-geometry-cell05-connections/workflow-v1/row-capsule-builder-v1/row-capsule-builder-source-v1.tar.xz'


def pin(body):
    return {'bytes': len(body), 'sha256': hashlib.sha256(body).hexdigest()}


def publish(name, body):
    body = body.encode() if isinstance(body, str) else body
    path = HERE / name
    if path.exists():
        if path.is_symlink() or path.read_bytes() != body:
            raise RuntimeError('Refuse differing prepared command: ' + name)
    else:
        with path.open('xb') as stream:
            stream.write(body)
    return {'file': name, **pin(body)}


def command(body, destination, execute=False):
    encoded = base64.b64encode(body).decode()
    identity = pin(body)
    code = '''from pathlib import Path
import base64,hashlib,json,os,stat,subprocess,sys
sys.dont_write_bytecode=True
p=Path(%r)
data=base64.b64decode(%r,validate=True)
expected=%r
if {'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}!=expected:raise RuntimeError('Local prepared payload pin mismatch')
for q in [*reversed(p.parents),p]:
 try:mode=q.lstat().st_mode
 except FileNotFoundError:continue
 if stat.S_ISLNK(mode) or (q!=p and not stat.S_ISDIR(mode)):raise RuntimeError('Unsafe upload/control path')
if p.exists():
 if not p.is_file() or p.read_bytes()!=data:raise RuntimeError('Refusing different existing payload')
else:
 p.parent.mkdir(parents=True,exist_ok=True)
 for q in [*reversed(p.parents),p.parent]:
  if q.is_symlink():raise RuntimeError('Symlink ancestor appeared')
 with p.open('xb') as f:f.write(data)
if p.read_bytes()!=data:raise RuntimeError('Payload readback mismatch')
''' % (str(destination), encoded, identity)
    if execute:
        code += "subprocess.run([sys.executable,'-B',str(p)],check=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})\n"
    else:
        code += "print(json.dumps({'status':'EXACT_SOURCE_PART_STORED','path':str(p),**expected}))\n"
    ast.parse(code)
    return "python3 -B - <<'PY'\n" + code + 'PY\n'


def main():
    spec = importlib.util.spec_from_file_location('rows15_deployment_local_validation', HERE / 'deploy_and_build.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    raw = SOURCE.read_bytes()
    payload = module.package_payload(raw)
    files = []
    for row in module.PARTS:
        start = row['index'] * 40000
        body = raw[start:start + row['bytes']]
        if pin(body) != {key: row[key] for key in ('bytes', 'sha256')}:
            raise RuntimeError('Source part differs')
        name = 'UPLOAD_%03d.sh' % row['index']
        files.append(publish(name, command(body, module.UPLOAD / ('part-%03d' % row['index']))))
    deploy = (HERE / 'deploy_and_build.py').read_bytes()
    ast.parse(deploy)
    files.append(publish('DEPLOY_AND_BUILD.sh', command(deploy, module.CONTROL / 'deploy_and_build.py', execute=True)))
    plan = {'schema': 'cell05_rows15_recovery_local_deployment_plan_v1',
            'status': 'LOCAL_AUTHORED_EXACT_SOURCE_COMMANDS_NOT_SUBMITTED',
            'source_archive': {'path': str(SOURCE), **pin(raw)},
            'source_member_count': len(payload), 'source_member_pins': [
                {'member': name, **pin(body)} for name, body in sorted(payload.items())],
            'source_build_manifest': module.MANIFEST_PIN,
            'deployment_script': {'file': 'deploy_and_build.py', **pin(deploy)},
            'upload_parts': module.PARTS, 'prepared_commands': files,
            'cloud_code_root': str(module.CODE), 'cloud_upload_root': str(module.UPLOAD),
            'cloud_control_root': str(module.CONTROL), 'cloud_capsule_output': str(module.OUTPUT),
            'original_Cell05_stage': str(module.ORIGIN),
            'builder_limits': {'timeout_seconds': 600, 'memory_mb': 2048, 'cpu_threads': 2},
            'expected_old_steps_rechecked': 45, 'expected_owned_declarations_rechecked': 5147,
            'expected_capsule_members': 267, 'expected_row_object_bodies': 15,
            'local_source_package_member_validation': True, 'local_Python_syntax_validation': True,
            'old_tests_rerun': 0, 'Lean_commands': 0, 'cloud_commands_by_preparation': 0,
            'new_Lean_acceptance': 0, 'capsule_body_transfer_authorized_in_this_step': False,
            'P2_deployment_authorized_in_this_step': False,
            'unknown_submission_or_automatic_approval_rejection_requires_stop': True}
    saved = publish('DEPLOYMENT_PLAN.json', json.dumps(plan, indent=2) + '\n')
    print(json.dumps({'plan': saved, 'deployment_script': plan['deployment_script'],
                      'prepared_commands': files, 'source_members': len(payload),
                      'old_tests_rerun': 0, 'Lean_commands': 0}, sort_keys=True))


if __name__ == '__main__':
    main()
