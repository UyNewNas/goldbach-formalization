#!/usr/bin/env python3
"""Freeze the reviewed local adapter and exact small inputs; never call a cloud."""
from pathlib import Path, PurePosixPath
import io
import json
import sys
import tarfile

sys.dont_write_bytecode = True
import join_common as C

HERE = Path(__file__).resolve().parent
P26 = HERE.parent
SOURCE_ARCHIVE = {'bytes': 122656, 'sha256': '457b87938ea4f363ab9ef8a6049173c5577f922bd5a133213ccfdd026001dce5'}


def main():
    release = HERE / 'releases/p3-preparation-v2'
    archive_path = HERE / 'cell01-family-p3-preparation-v2.tar.xz'
    C.need(not release.exists() and not archive_path.exists(), 'Existing preparation release must remain unchanged')
    payload = {}
    def add(member, data):
        name = PurePosixPath(member)
        C.need(member and not name.is_absolute() and '..' not in name.parts and str(name) == member
               and member not in payload, 'Unsafe or duplicate preparation member')
        payload[member] = data
    for name in ('prepare_family_p3.py', 'join_common.py', 'external_runtime.py', 'INPUT_CONTRACT.md'):
        add(name, (HERE / name).read_bytes())
    add('INPUT_CONFIG.json', (HERE / 'INPUT_CONFIG_CANDIDATE_v2.json').read_bytes())
    executor = P26 / 'cell01-family-run-20261126/releases/p3-v2'
    executor_data = C.checked_local(executor / 'CODE_MANIFEST.json', C.expected('executor_manifest'))
    add('frozen-executor/CODE_MANIFEST.json', executor_data)
    for row in json.loads(executor_data)['files']:
        add('frozen-executor/' + row['member'], C.checked_local(executor / row['member'], row))
    source_path = P26 / 'original-floor-family/cell01-original-floor-family-v1.tar.xz'
    source_data = C.checked_local(source_path, SOURCE_ARCHIVE)
    add('cell01-original-floor-family-v1.tar.xz', source_data)
    original_members = {}
    with tarfile.open(fileobj=io.BytesIO(source_data), mode='r:xz') as stream:
        for item in stream:
            C.need(item.isfile() and item.name not in original_members, 'Original source archive is not regular and unique')
            data = stream.extractfile(item).read()
            original_members[item.name] = data
            add('source-package/' + item.name, data)
    package = json.loads(original_members['PACKAGE_MANIFEST.json'])
    C.need(set(original_members) == {'PACKAGE_MANIFEST.json'} | {r['member'] for r in package['files']}
           and len(original_members) == 36, 'Original source package member inventory differs')
    for row in package['files']:
        C.need(C.identity_bytes(original_members[row['member']]) == {k: row[k] for k in ('bytes', 'sha256')},
               'Original source archive member pin differs')
    for name, pin_key in [('P3_PRESENT_FINAL.json', 'P3_present'), ('P3_MISSING_FINAL.json', 'P3_missing'),
                          ('P3_INVENTORY_SUMMARY.json', 'P3_inventory')]:
        add('inventories/' + name, C.checked_local(P26 / 'supplier-join-20261126' / name, C.expected(pin_key)))
    canonical_pins = {
        'selected-bodies.tar.xz': {'bytes': 329648, 'sha256': '6ed9837ee38b7c94e6d6ca24e0f4f2e8d82fd7bdb8763531034d4ea6c0c9d97e'},
        'EVIDENCE_MANIFEST.json': {'bytes': 20170, 'sha256': 'da1b149115eef8011190a0cc08d21f80db2b67327ba9115fce8ad437a05caabf'},
    }
    for name, pin in canonical_pins.items():
        add('canonical/' + name, C.checked_local(HERE / 'local-canonical-v1' / name, pin))
    manifest = {'schema': 'p26_family_p3_preparation_package_v1',
                'status': 'FROZEN_INPUT_PREPARATION_ONLY_NOT_RUN_ON_P3',
                'destination': '/workspace/p26-continuation-557a12f3bcd7/cell01-family-p3-preparation-v2',
                'files': [{'member': name, **C.identity_bytes(data)} for name, data in sorted(payload.items())],
                'old_supplier_union': 791, 'new_owner_scope': 11, 'later_proof_steps': 33,
                'row001_historical_bodies_included': False,
                'row001_validator_source_code_included': True,
                'supplier_objects_included': False, 'canonical_original_body_references': 21,
                'external_provider_modules': 515, 'external_objects_included': False,
                'Lean_commands': 0, 'new_proof_credit': 0, 'later_rss_gib': 12}
    C.need(len(payload) == 58, 'Unexpected preparation package file count')
    add('PREPARATION_PACKAGE_MANIFEST.json', (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode())
    release.mkdir(parents=True)
    for member, data in sorted(payload.items()):
        path = release / member
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('xb') as stream:
            stream.write(data)
    with archive_path.open('xb') as raw, tarfile.open(fileobj=raw, mode='w:xz', preset=6) as stream:
        for member, data in sorted(payload.items()):
            item = tarfile.TarInfo(member)
            item.size, item.mode, item.mtime = len(data), 0o444, 0
            stream.addfile(item, io.BytesIO(data))
    seen = set()
    with tarfile.open(archive_path, mode='r:xz') as stream:
        for item in stream:
            C.need(item.isfile() and item.name in payload and item.name not in seen,
                   'Preparation archive member inventory differs')
            data = stream.extractfile(item).read()
            C.need(data == payload[item.name] == (release / item.name).read_bytes(),
                   'Preparation archive readback differs')
            seen.add(item.name)
    C.need(seen == set(payload), 'Preparation archive is incomplete')
    result = {'schema': 'p26_family_p3_preparation_release_v1',
              'status': 'PASS_59_EXACT_PACKAGE_MEMBERS_NOT_DEPLOYED',
              'archive': {'path': str(archive_path), **C.identity_bytes(archive_path.read_bytes())},
              'manifest': {'path': str(release / 'PREPARATION_PACKAGE_MANIFEST.json'),
                           **C.identity_bytes(payload['PREPARATION_PACKAGE_MANIFEST.json'])},
              'archive_members': len(payload), 'all_regular_unique_members_read_back': True,
              'frozen_executor_manifest': C.expected('executor_manifest'),
              'original_11_owner_source_archive': SOURCE_ARCHIVE,
              'new_owners_accepted': 0, 'Lean_commands': 0, 'cloud_adapter_runs': 0}
    with (HERE / 'PREPARATION_RELEASE_v2.json').open('x') as stream:
        json.dump(result, stream, sort_keys=True, indent=2)
        stream.write('\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
