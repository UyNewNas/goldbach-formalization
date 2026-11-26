#!/usr/bin/env python3
"""Local-only deterministic freeze of the reviewed fourteen-target source package."""
from pathlib import Path
import hashlib
import io
import json
import shutil
import sys
import tarfile

sys.dont_write_bytecode = True
from receipt_checks import TOOL_REL, fp, read, require, same


def encoded(value):
    return (json.dumps(value, indent=2) + '\n').encode()


def pin(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def main():
    here = Path(__file__).absolute().parent
    release = here / 'releases/v1'
    require(not release.exists(), 'Frozen v1 already exists; never overwrite a release')
    targets = read(here / 'CONNECTION_TARGETS.json')['targets']
    require(len(targets) == 14 and len(read(here / 'SUPPLIER_REGISTRY.json')['suppliers']) == 88,
            'Wrong source package scope')
    names = ['verify_connections14.py', 'receipt_checks.py', 'receipt_support.py', 'export_connections14.py',
             'stage_entry.py', 'fields_only_join.py', 'evidence_io.py', 'supplier_capsule.py',
             'portable_receipts.py', 'supplier_join.py', 'runtime_compat.py', 'runtime_probe.py',
             'baseline_checks.py', 'test_connections14.py', 'INPUT_CONTRACT.md',
             'SUPPLIER_PLAN.json', 'SUPPLIER_REGISTRY.json', 'CONNECTION_TARGETS.json',
             'CONNECTIONS_SOURCE_MANIFEST.json', 'READY14_TARGETS.json', 'FIELDS88_SUPPLIERS.json',
             'INPUT_ASSEMBLY.json', 'RUNTIME_COMPATIBILITY_PINS.json']
    for folder in ('accepted-metadata', 'runtime-evidence', 'owned-audits'):
        names += [path.relative_to(here).as_posix() for path in sorted((here / folder).rglob('*')) if path.is_file()]
    require(len(names) == len(set(names)), 'Duplicate workflow file')
    workflow = [{'relative_path': name, **pin((here / name).read_bytes())} for name in sorted(names)]
    verifier = {'schema': 'cell05_connections14_frozen_verifier_v1', 'status': 'SOURCE_ONLY_NOT_RUN',
                'targets': targets, 'target_count': 14, 'expected_steps': 42, 'accepted_steps': 0,
                'old_supplier_count': 88, 'actual_supplier_union': 83, 'old_supplier_proof_commands': 0,
                'source_or_audit_bytes_changed': False, 'whole_geometry_decoded': False,
                'P2_6_complete': False, 'workflow_files': workflow}
    payload = {str(TOOL_REL / row['relative_path']): (here / row['relative_path']).read_bytes() for row in workflow}
    payload[str(TOOL_REL / 'CONNECTIONS14_VERIFIER.json')] = encoded(verifier)
    for row in targets:
        data = (here / row['source_member']).read_bytes()
        require(same(pin(data), row['source']) and
                same(pin((here / row['audit_relative_path']).read_bytes()), row['audit']),
                'Original target source/audit bytes differ')
        payload[row['source_member']] = data
    package = {'schema': 'cell05_connections14_source_package_v1', 'status': 'SOURCE_ONLY_NOT_RUN',
               'target_count': 14, 'planned_new_steps': 42, 'accepted_steps': 0,
               'old_supplier_proof_commands': 0, 'old_supplier_object_bodies': 0,
               'members': [{'member': member, **pin(data)} for member, data in sorted(payload.items())]}
    payload['PACKAGE_CONTENTS.json'] = encoded(package)
    release.mkdir(parents=True, exist_ok=False)
    for member, data in sorted(payload.items()):
        path = release / member
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('xb') as stream:
            stream.write(data)
    archive_path = here / 'cell05-connections14-source-v1.tar.xz'
    with archive_path.open('xb') as stream:
        with tarfile.open(fileobj=stream, mode='w:xz', preset=6) as archive:
            for member, data in sorted(payload.items()):
                info = tarfile.TarInfo(member)
                info.size, info.mode, info.mtime = len(data), 0o644, 0
                archive.addfile(info, io.BytesIO(data))
    seen = set()
    with tarfile.open(archive_path, 'r:xz') as archive:
        for info in archive:
            require(info.isfile() and info.name in payload and info.name not in seen, 'Unexpected archive member')
            require(archive.extractfile(info).read() == payload[info.name], 'Frozen archive readback differs')
            seen.add(info.name)
    require(seen == set(payload), 'Frozen archive is incomplete')
    code_manifest = {'schema': 'cell05_connections14_code_manifest_v1', 'status': 'SOURCE_ONLY_NOT_RUN',
                     'files': [{'relative_path': member, **pin(data)} for member, data in sorted(payload.items())
                               if member.endswith('.py')],
                     'frozen_verifier': pin(payload[str(TOOL_REL / 'CONNECTIONS14_VERIFIER.json')]),
                     'package_manifest': pin(payload['PACKAGE_CONTENTS.json']), 'accepted_new_steps': 0}
    (here / 'CODE_MANIFEST.json').write_bytes(encoded(code_manifest))
    report = {'schema': 'cell05_connections14_source_release_v1', 'status': 'SOURCE_ONLY_NOT_RUN',
              'archive': fp(archive_path), 'archive_members': len(payload),
              'code_manifest': fp(here / 'CODE_MANIFEST.json'), 'release_root': str(release),
              'source_bytes': sum(row['source']['bytes'] for row in targets),
              'audit_bytes': sum(row['audit']['bytes'] for row in targets),
              'archive_regular_member_readback': True, 'new_target_count': 14,
              'planned_new_steps': 42, 'accepted_new_steps': 0, 'Lean_commands_executed_locally': 0}
    (here / 'SOURCE_RELEASE.json').write_bytes(encoded(report))
    print(json.dumps(report, sort_keys=True))


if __name__ == '__main__':
    main()
