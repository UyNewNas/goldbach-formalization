#!/usr/bin/env python3
"""Install the exact frozen preparation package into a fresh root, then preflight.

This entry point launches only the reviewed Python adapter, never Lean.
Archive transport to P3 is a separate, explicitly recorded operation.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import subprocess
import sys
import tarfile

sys.dont_write_bytecode = True
DESTINATION = Path('/workspace/p26-continuation-557a12f3bcd7/cell01-family-p3-preparation-v3')
ARCHIVE_PIN = (664856, '05db077182e91606f800569f621ec0f13f79e0642500a8f6f930391a522e1bb4')
MANIFEST_PIN = (11935, '2e5595cbea2c0de2df6724535bdb32b3557b46a50de012206669cd9c468c0f95')


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def identity(data):
    return len(data), hashlib.sha256(data).hexdigest()


def canonical(path):
    path = Path(path)
    need(path.is_absolute() and '..' not in path.parts and not path.is_symlink()
         and path.resolve() == path, 'Canonical absolute path required')
    return path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path, required=True)
    args = parser.parse_args()
    archive_path = canonical(args.archive)
    need(archive_path.is_file(), 'Missing exact preparation archive')
    destination = canonical(DESTINATION)
    need(not destination.exists(), 'Existing preparation directory requires inspection; no retry')
    need(not archive_path.is_relative_to(destination), 'Archive must be outside fresh package destination')
    before = archive_path.read_bytes()
    need(identity(before) == ARCHIVE_PIN, 'Preparation archive pin differs')
    payload = {}
    with tarfile.open(archive_path, mode='r:xz') as stream:
        for item in stream:
            relative = PurePosixPath(item.name)
            need(item.isfile() and item.name not in payload and item.name
                 and not relative.is_absolute() and '..' not in relative.parts
                 and str(relative) == item.name, 'Unsafe, duplicate or nonregular preparation member')
            data = stream.extractfile(item).read()
            need(len(data) == item.size, 'Incomplete preparation member')
            payload[item.name] = data
    manifest_data = payload['PREPARATION_PACKAGE_MANIFEST.json']
    need(identity(manifest_data) == MANIFEST_PIN, 'Preparation manifest pin differs')
    manifest = json.loads(manifest_data)
    need(manifest['schema'] == 'p26_family_p3_preparation_package_v1'
         and manifest['destination'] == str(destination)
         and manifest['row001_historical_bodies_included'] is False
         and manifest['supplier_objects_included'] is False
         and manifest['external_objects_included'] is False
         and manifest['external_provider_modules'] == 515
         and manifest['Lean_commands'] == manifest['new_proof_credit'] == 0,
         'Preparation manifest boundary differs')
    expected = {row['member']: row for row in manifest['files']}
    need(len(expected) == len(manifest['files']) == 58 and
         set(payload) == set(expected) | {'PREPARATION_PACKAGE_MANIFEST.json'}
         and len(payload) == 59, 'Preparation archive inventory differs')
    for name, row in expected.items():
        need(identity(payload[name]) == (row['bytes'], row['sha256']), 'Preparation member pin differs')
    need(archive_path.read_bytes() == before, 'Preparation input archive changed during validation')
    # Every package byte has been verified before the first directory write.
    destination.mkdir()
    for name, data in sorted(payload.items()):
        path = destination / name
        path.parent.mkdir(parents=True, exist_ok=True)
        canonical(path)
        with path.open('xb') as stream:
            stream.write(data)
    for name, data in payload.items():
        need(canonical(destination / name).read_bytes() == data, 'Preparation install readback differs')
    need({p.relative_to(destination).as_posix() for p in destination.rglob('*') if p.is_file()} == set(payload),
         'Unexpected installed preparation file')
    print(json.dumps({'phase': 'EXACT_59_FILE_PREPARATION_PACKAGE_INSTALLED',
                      'archive': {'path': str(archive_path), 'bytes': ARCHIVE_PIN[0], 'sha256': ARCHIVE_PIN[1]},
                      'destination': str(destination), 'Lean_commands': 0, 'new_proof_credit': 0}), flush=True)
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    completed = subprocess.run([sys.executable, '-B', str(destination / 'prepare_family_p3.py'),
                                '--config', str(destination / 'INPUT_CONFIG.json')], env=env)
    sys.exit(completed.returncode)


if __name__ == '__main__':
    main()
