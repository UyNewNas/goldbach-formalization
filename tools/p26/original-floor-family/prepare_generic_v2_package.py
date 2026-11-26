#!/usr/bin/env python3
"""Freeze v2 from the unchanged v1 source-only package; never execute Lean."""
from pathlib import Path
import argparse
import ast
import hashlib
import io
import json
import tarfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
V1_SHA = '923323f30b89fc4cf63833b4cf7fe89747e21ae24501cdc701057d11b0ff6781'
SOURCE_SHA = '9f4b64321975f8eb567484982abc622ee77ac222c90a6d117b2acc7a0f39b574'
AUDIT_SHA = '4fa2d4bc9272505e76c14088e08ff309df9ba21981532016f4ff5ba6b89c7680'


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def fp(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=HERE / 'generic-source-v2')
    args = parser.parse_args()
    output = args.output.absolute()
    tar_path, metadata_path = output.with_suffix('.tar.xz'), output.with_suffix('.metadata.json')
    for path in (output, tar_path, metadata_path):
        need('..' not in path.parts and path.resolve() == path and not path.is_symlink() and
             not path.exists(), f'Refusing existing or noncanonical output: {path}')
    v1_path = HERE / 'generic-source-v1.tar.xz'
    v1_pin = fp(v1_path.read_bytes())
    need(v1_pin == {'bytes': 116504, 'sha256': V1_SHA}, 'Original v1 package changed')
    old_files = {}
    with tarfile.open(v1_path, 'r:xz') as tar:
        for member in tar.getmembers():
            relative = Path(member.name)
            need(member.isfile() and not relative.is_absolute() and '..' not in relative.parts and
                 member.name not in old_files, 'Invalid original package member')
            data = tar.extractfile(member).read()
            need(len(data) == member.size, 'Truncated original package member')
            old_files[member.name] = data
    need(len(old_files) == 9, 'Original package inventory differs')
    old_manifest = json.loads(old_files['PACKAGE_MANIFEST.json'])
    need(len(old_manifest['files']) == 8 and
         {r['member'] for r in old_manifest['files']} | {'PACKAGE_MANIFEST.json'} == set(old_files),
         'Original manifest inventory differs')
    for row in old_manifest['files']:
        need(fp(old_files[row['member']]) == {k: row[k] for k in ('bytes', 'sha256')},
             'Original manifest/member pin differs')
    registry = json.loads(old_files['REGISTRY.json'])
    source_member, audit_member = registry['source_member'], registry['audit_member']
    need(fp(old_files[source_member])['sha256'] == SOURCE_SHA and
         fp(old_files[audit_member])['sha256'] == AUDIT_SHA, 'Original source/audit differs')
    need((REPO / source_member.removeprefix('sources/')).read_bytes() == old_files[source_member] and
         (HERE / 'owned-audit.lean').read_bytes() == old_files[audit_member],
         'Authored mathematical source/audit changed')
    test_result = json.loads((HERE / 'WORKFLOW_TEST_RESULT_v2.json').read_text())
    need(test_result['status'] == 'PASS_SYNTHETIC_WORKFLOW_TESTS' and test_result['exit_code'] == 0,
         'The v2 workflow tests did not pass')
    for pin in test_result['inputs'] + [test_result['log']]:
        need(fp(Path(pin['path']).read_bytes()) == {k: pin[k] for k in ('bytes', 'sha256')},
             'Tested input or authentic test log changed')
    files = {name: data for name, data in old_files.items() if name != 'PACKAGE_MANIFEST.json'}
    files['GenericFloor_verify.py'] = (HERE / 'GenericFloor_verify_v2.py').read_bytes()
    files['README.md'] = (HERE / 'VERIFIER_README_v2.md').read_bytes()
    for name, data in files.items():
        if name.endswith('.py'):
            ast.parse(data.decode())
    changed = [name for name in files if files[name] != old_files[name]]
    need(set(changed) == {'GenericFloor_verify.py', 'README.md'}, 'Unexpected payload modification')
    manifest = {**old_manifest,
        'schema': 'p26_generic_floor_frozen_source_package_v2',
        'revision': 'v2_failed_index_and_export_integrity',
        'supersedes_source_package': {'name': v1_path.name, **v1_pin},
        'files': [{'member': name, **fp(data)} for name, data in sorted(files.items())]}
    files['PACKAGE_MANIFEST.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
    output.mkdir()
    for name, data in sorted(files.items()):
        path = output / name
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('xb') as stream:
            stream.write(data)
    with tar_path.open('xb') as raw, tarfile.open(fileobj=raw, mode='w:xz', format=tarfile.PAX_FORMAT) as tar:
        for name, data in sorted(files.items()):
            info = tarfile.TarInfo(name)
            info.size, info.mode = len(data), 0o644
            tar.addfile(info, io.BytesIO(data))
    seen = set()
    with tarfile.open(tar_path, 'r:xz') as tar:
        for member in tar.getmembers():
            need(member.isfile() and member.name in files and member.name not in seen,
                 'Invalid v2 readback inventory')
            seen.add(member.name)
            need(tar.extractfile(member).read() == files[member.name], 'v2 payload readback differs')
    need(seen == set(files), 'Incomplete v2 readback inventory')
    need(fp(v1_path.read_bytes()) == v1_pin, 'Original v1 archive changed while preparing v2')
    metadata = {'status': 'SOURCE_PACKAGE_ONLY_NOT_EXECUTED', 'package': str(tar_path),
        **fp(tar_path.read_bytes()), 'members': len(files),
        'changed_members_from_v1': sorted(changed + ['PACKAGE_MANIFEST.json']),
        'unchanged_members_from_v1': sorted(set(files) - set(changed) - {'PACKAGE_MANIFEST.json'}),
        'original_v1_package': {'path': str(v1_path), **v1_pin},
        'target_source': fp(files[source_member]), 'target_audit': fp(files[audit_member]),
        'registry': fp(files['REGISTRY.json']), 'supplier_count': len(registry['suppliers']),
        'external_module_count': len(registry['external_modules']),
        'supplier_source_bytes': registry['supplier_source_bytes'],
        'supplier_object_bytes_hardlink_only': registry['supplier_object_bytes'],
        'workflow_tests': {'path': str(HERE / 'WORKFLOW_TEST_RESULT_v2.json'),
                           **fp((HERE / 'WORKFLOW_TEST_RESULT_v2.json').read_bytes())},
        'evidence_boundary': 'Archive contains PROOF_RESULT with EXPORT_PENDING; final PASS RESULT and '
                             'export-2 check remain outside and are bound by the external manifest.',
        'Lean_invoked': False, 'cloud_jobs_submitted': 0, 'old_supplier_proof_commands': 0}
    with metadata_path.open('x') as stream:
        json.dump(metadata, stream, indent=2)
        stream.write('\n')
    print(json.dumps(metadata, indent=2))


if __name__ == '__main__':
    main()
