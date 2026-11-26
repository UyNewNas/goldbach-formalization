#!/usr/bin/env python3
"""Deploy the already reviewed Cell05 rows15 builder; read old proof, pack new capsule."""
from pathlib import Path, PurePosixPath
import hashlib
import io
import json
import os
import stat
import subprocess
import sys
import tarfile

sys.dont_write_bytecode = True
BASE = Path('/workspace/p26-continuation-557a12f3bcd7')
CODE = BASE / 'cell05-row15-builder-v1'
UPLOAD = BASE / 'cell05-row15-builder-upload-v1'
CONTROL = BASE / 'cell05-row15-recovery-control-v1'
OUTPUT = BASE / 'cell05-rows15-capsule-v1/rows15-provider-v1.tar.xz'
ORIGIN = Path('/workspace/p26-continuation-59264dd64286/scalable-geometry-cell05-complete-v3')
TOOL = PurePosixPath('tools/p26/scalable-cell05-connections-run')
ARCHIVE_PIN = {'bytes': 101404, 'sha256': '43c3c0a0358a8be6b419a3d30df426df1fe3ee3fcd756e6cd49e9fad931332ef'}
MANIFEST_PIN = {'bytes': 3503, 'sha256': 'f409a1f841f992aa1cc7debe81f5ae15c73c78f2d6e271f3e9691836b2e0e5b0'}
PARTS = [
    {'index': 0, 'bytes': 40000, 'sha256': '216143e78e936054982a26ff40b78130d6a770ac81ea123256376fd6f93c433b'},
    {'index': 1, 'bytes': 40000, 'sha256': 'e4e93f4c5b459a46decb634361da08c16f23661629a2ec0f98693f8ea5c50898'},
    {'index': 2, 'bytes': 21404, 'sha256': '056ff8fda625b4463bdb836e6a0b51349f426c8135dac426c0942efbb01d0a85'},
]


def require(value, message):
    if not value:
        raise RuntimeError(message)


def pin(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def canonical(path):
    require(path.is_absolute() and '..' not in path.parts, 'Noncanonical path')
    for ancestor in [*reversed(path.parents), path]:
        try:
            info = ancestor.lstat()
        except FileNotFoundError:
            continue
        require(not stat.S_ISLNK(info.st_mode), 'Symlink rejected: ' + str(ancestor))
        if ancestor != path:
            require(stat.S_ISDIR(info.st_mode), 'Nondirectory ancestor')
    return path


def regular_bytes(path):
    canonical(path)
    require(stat.S_ISREG(path.lstat().st_mode), 'Nonregular input: ' + str(path))
    return path.read_bytes()


def fp(path):
    return {'path': str(path), **pin(regular_bytes(path))}


def safe_member(name):
    value = PurePosixPath(name)
    require(name and not value.is_absolute() and '..' not in value.parts and str(value) == name,
            'Unsafe archive member')
    return value


def create_or_same(path, body):
    canonical(path)
    if path.exists():
        require(regular_bytes(path) == body, 'Refusing different existing file: ' + str(path))
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    canonical(path.parent)
    with path.open('xb') as stream:
        stream.write(body)
        stream.flush()
        os.fsync(stream.fileno())
    require(regular_bytes(path) == body, 'Created file readback differs')


def package_payload(raw):
    require(pin(raw) == ARCHIVE_PIN, 'Full reviewed source archive differs')
    payload = {}
    with tarfile.open(fileobj=io.BytesIO(raw), mode='r:xz') as archive:
        for member in archive:
            name = safe_member(member.name)
            require(member.isfile() and name.is_relative_to(TOOL) and member.name not in payload,
                    'Nonregular, out-of-scope or duplicate source member')
            body = archive.extractfile(member).read()
            require(len(body) == member.size, 'Truncated source member')
            payload[member.name] = body
    require(len(payload) == 19, 'Expected exactly nineteen source/control members')
    manifest_name = str(TOOL / 'CAPSULE_BUILD_MANIFEST.json')
    require(pin(payload[manifest_name]) == MANIFEST_PIN, 'Original builder manifest differs')
    manifest = json.loads(payload[manifest_name])
    require(manifest['schema'] == 'cell05_row_capsule_builder_source_package_v1'
            and manifest['Lean_commands'] == manifest['Git_commands'] == 0,
            'Wrong source-only builder scope')
    expected = {}
    for row in manifest['files']:
        relative = safe_member(row['relative_path'])
        name = str(TOOL / relative)
        require(name not in expected and name != manifest_name, 'Duplicate source manifest member')
        expected[name] = {key: row[key] for key in ('bytes', 'sha256')}
    require(set(payload) == set(expected) | {manifest_name} and len(expected) == 18,
            'Manifest does not describe the exact reviewed source package')
    for name, identity in expected.items():
        require(pin(payload[name]) == identity, 'Source member identity differs: ' + name)
        require(not name.endswith(('.olean', '.ilean')), 'Source package contains a proof object')
    return payload


def verify_capsule(path, report):
    require(report['schema'] == 'cell05_rows15_capsule_build_report_v1'
            and report['status'] == 'PASS_EXACT_ROW_SUPPLIER_CAPSULE', 'Original builder did not pass')
    for key, value in {'members': 267, 'new_object_bodies': 15, 'old_supplier_object_bodies': 0,
                       'fields_object_bodies': 0, 'accepted_steps_rechecked': 45,
                       'owned_declarations_rechecked': 5147, 'Lean_commands': 0, 'Git_commands': 0,
                       'regular_archive_readback': True, 'original_inputs_unchanged': True,
                       'full_evidence_archive_transferred': False}.items():
        require(report.get(key) == value, 'Unexpected original report field: ' + key)
    require(report['archive'] == fp(path), 'Original report archive identity differs')
    bodies = {}
    with tarfile.open(path, 'r:xz') as archive:
        for member in archive:
            safe_member(member.name)
            require(member.isfile() and member.name not in bodies, 'Unsafe or duplicate capsule member')
            body = archive.extractfile(member).read()
            require(len(body) == member.size, 'Short capsule member')
            bodies[member.name] = body
    require(len(bodies) == 267 and 'CAPSULE_MANIFEST.json' in bodies, 'Wrong capsule member count')
    manifest = json.loads(bodies['CAPSULE_MANIFEST.json'])
    require(manifest['schema'] == 'cell05_rows15_relocatable_supplier_capsule_v1'
            and manifest['accepted_targets_rechecked'] == 15
            and manifest['accepted_steps_rechecked'] == 45
            and manifest['owned_declarations_rechecked'] == 5147
            and manifest['original_receipt_bytes_rewritten'] is False
            and manifest['complete_join_acceptance'] is False, 'Wrong retained supplier capsule scope')
    expected = {row['member']: row for row in manifest['members']}
    require(len(expected) == len(manifest['members']) == 266
            and set(bodies) == set(expected) | {'CAPSULE_MANIFEST.json'}, 'Capsule manifest inventory differs')
    for name, row in expected.items():
        require(pin(bodies[name]) == {key: row[key] for key in ('bytes', 'sha256')}, 'Capsule readback differs')
    require(report['archive'] == fp(path), 'Capsule changed during readback')


def main():
    require(sys.flags.optimize == 0, 'Run without Python optimization')
    roots = (CODE, UPLOAD, CONTROL, OUTPUT.parent, ORIGIN)
    for root in roots:
        canonical(root)
    for i, left in enumerate(roots):
        for right in roots[i + 1:]:
            require(not (left == right or left.is_relative_to(right) or right.is_relative_to(left)),
                    'Code/upload/control/output/original roots overlap')
    for path in (OUTPUT, OUTPUT.with_name(OUTPUT.name + '.partial'), OUTPUT.with_name(OUTPUT.name + '.json'),
                 CONTROL / 'DEPLOY_AND_BUILD_RESULT.json'):
        canonical(path)
        require(not path.exists(), 'Prior output requires read-only recovery; do not resubmit or overwrite: ' + str(path))
    pieces = []
    for row in PARTS:
        body = regular_bytes(UPLOAD / ('part-%03d' % row['index']))
        require(pin(body) == {key: row[key] for key in ('bytes', 'sha256')}, 'Upload part differs')
        pieces.append(body)
    payload = package_payload(b''.join(pieces))
    if CODE.exists():
        require(CODE.is_dir(), 'Code root is not a directory')
        for path in CODE.rglob('*'):
            canonical(path)
            if path.is_file():
                name = path.relative_to(CODE).as_posix()
                require(name in payload and regular_bytes(path) == payload[name], 'Conflicting existing code body')
            else:
                require(path.is_dir(), 'Unexpected special file in code root')
    for name, body in sorted(payload.items()):
        destination = canonical(CODE / name)
        if destination.exists():
            require(regular_bytes(destination) == body, 'Existing source differs before first write')
    for name, body in sorted(payload.items()):
        create_or_same(CODE / name, body)
    before = {name: fp(CODE / name) for name in payload}
    builder = CODE / str(TOOL) / 'build_row_capsule.py'
    print(json.dumps({'phase': 'reviewed_source_deployed', 'source_package': ARCHIVE_PIN,
                      'manifest': MANIFEST_PIN, 'members': 19, 'Lean_commands': 0}), flush=True)
    completed = subprocess.run([sys.executable, '-B', str(builder), '--output', str(OUTPUT)],
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                               env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
    if completed.returncode:
        print(completed.stdout, end='', flush=True)
        raise SystemExit(completed.returncode)
    report_path = OUTPUT.with_name(OUTPUT.name + '.json')
    report_bytes = regular_bytes(report_path)
    require(completed.stdout.encode() == report_bytes, 'Original builder stdout/report bytes differ')
    report = json.loads(report_bytes)
    verify_capsule(OUTPUT, report)
    require({name: fp(CODE / name) for name in payload} == before, 'Deployed reviewed source changed during build')
    result = {'schema': 'cell05_rows15_recovery_deploy_report_v1', 'status': 'PASS_ORIGINAL_ROWS15_CAPSULE_RETAINED_ON_P1',
              'original_report': report, 'original_report_file': fp(report_path),
              'original_report_text': report_bytes.decode(), 'source_package': ARCHIVE_PIN,
              'source_manifest': fp(CODE / str(TOOL) / 'CAPSULE_BUILD_MANIFEST.json'),
              'deployed_source_members': 19, 'capsule_members_rechecked': 267,
              'source_inputs_unchanged': True, 'old_supplier_proof_commands': 0,
              'Lean_commands': 0, 'new_Lean_acceptance': 0,
              'capsule_body_transferred': False, 'P2_deployment_performed': False,
              'Cell01_paths_modified': False,
              'old_Cell01_Row001_archive_or_receipt_group_selected': False}
    create_or_same(CONTROL / 'DEPLOY_AND_BUILD_RESULT.json', (json.dumps(result, indent=2) + '\n').encode())
    print(json.dumps(result, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
