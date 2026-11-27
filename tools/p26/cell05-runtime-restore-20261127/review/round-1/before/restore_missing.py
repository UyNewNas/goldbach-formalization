#!/usr/bin/env python3
"""Restore only the pinned missing Mathlib bytes; never certify proof compatibility."""
import argparse
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import stat
import tarfile
import time

STAGE = Path('/workspace/p26-runtime-missing-bytes-20261127-v1')
ROOT = Path('/workspace/compile-deps/mathlib/.lake/build/lib/lean')
CAPSULE = STAGE / 'p1-mathlib-missing-original-bytes.tar.xz'
CAPSULE_PIN = {'bytes': 2962644, 'sha256': '9d4a34bbd76678005e5c0c8368a2d2509e47705ee76dc7c0d3e279ed512329db'}
MANIFEST_PIN = {'bytes': 16929602, 'sha256': '1a2156c601172d688ea4cbb7d99b945ed99004270321695c4ef3fdc0e9d4785a'}
SNAPSHOT = Path('/workspace/p26-continuation-59264dd64286/cell05-runtime-P2-v1.json')
SNAPSHOT_PIN = {'bytes': 12773129, 'sha256': 'fd7749b90ebc482c9450ce6021864370aec0a6459d7c14470b4cf8698434edd7'}
OLD_GUARD = Path('/workspace/p26-cell05-connections14-provider-557a12f3bcd7/evidence/RUNTIME_GUARD.json')
OLD_GUARD_PIN = {'bytes': 16889262, 'sha256': '19d5266e4e36891aa5cf07c0e95dffac30baadae2394b19aaa83dd84ac5d1081'}
EVIDENCE = Path('/workspace/p26-cell05-remaining9-stage-v2-557a12f3bcd7/tools/p26/cell05-remaining9-run-20261126/original103/runtime-evidence')
DIGEST = 'f2e4b7beced12241c314edc5716836ab83656b5465c97719523cdf7a175e1362'
HASH_SUFFIXES = ('.olean.hash', '.olean.private.hash', '.olean.server.hash')
CACHE = {'Cache/' + n + '.olean' for n in ('Cli', 'Hashing', 'IO', 'Infra', 'Lean', 'Main', 'Marker', 'Query', 'Requests', 'Warning')}
EVIDENCE_NAMES = {'runtime-P1-SUMMARY.json', 'runtime-P2-SUMMARY.json', 'RUNTIME_COMPARISON.json', 'runtime-P1-MCP_TASK.json', 'runtime-P2-MCP_TASK.json'}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def pin(body):
    return {'bytes': len(body), 'sha256': hashlib.sha256(body).hexdigest()}


def canonical(path, exists=True):
    path = Path(path)
    require(path.is_absolute() and '..' not in path.parts and path.resolve(strict=exists) == path,
            'Noncanonical path: ' + str(path))
    # resolve() does not expose a dangling final symlink.
    require(not path.is_symlink(), 'Symlink: ' + str(path))
    return path


def checked(path, expected):
    path = canonical(path)
    require(stat.S_ISREG(path.lstat().st_mode), 'Nonregular file: ' + str(path))
    before = path.stat()
    body = path.read_bytes()
    after = path.stat()
    require((before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns) ==
            (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns),
            'File changed while reading: ' + str(path))
    require(pin(body) == {k: expected[k] for k in ('bytes', 'sha256')}, 'Changed bytes: ' + str(path))
    return body


def safe_relative(name):
    path = PurePosixPath(name)
    require(isinstance(name, str) and name and not path.is_absolute() and path.as_posix() == name and
            '..' not in path.parts and '\\' not in name and '\x00' not in name,
            'Unsafe archive path: ' + repr(name))
    return path


def unpack(capsule_bytes):
    """Validate the entire authenticated archive before any destination is written."""
    require(pin(capsule_bytes) == CAPSULE_PIN, 'Capsule pin mismatch')
    result = {}
    expanded = 0
    with tarfile.open(fileobj=io.BytesIO(capsule_bytes), mode='r:xz') as archive:
        for member in archive:
            safe_relative(member.name)
            require(member.isfile() and not member.issym() and not member.islnk(), 'Nonregular archive member')
            require(member.name not in result, 'Duplicate archive member')
            expanded += member.size
            require(member.size >= 0 and expanded <= 25 * 1024**2 and len(result) < 24929, 'Archive exceeds fixed scope')
            result[member.name] = archive.extractfile(member).read()
            require(len(result[member.name]) == member.size, 'Truncated archive member')
    require(len(result) == 24929 and pin(result['RESTORE_MANIFEST.json']) == MANIFEST_PIN, 'Wrong archive inventory/manifest')
    return result


def validate_payload(files, snapshot):
    manifest = json.loads(files['RESTORE_MANIFEST.json'])
    require(manifest['schema'] == 'p26_original_mathlib_missing_bytes_recovery_v1', 'Wrong manifest schema')
    require(manifest['original_P2_snapshot'] == {'path': str(SNAPSHOT), **SNAPSHOT_PIN}, 'Wrong P2 snapshot')
    roots = [r for r in snapshot['roots'] if r['logical_root'] == 'mathlib-objects']
    require(len(roots) == 1 and roots[0]['physical_root'] == str(ROOT), 'Wrong snapshot root')
    root = roots[0]
    rows = root['files']
    require(len(rows) == root['file_count'] == 49826 and sum(r['bytes'] for r in rows) == root['total_bytes'] == 5490108736,
            'Wrong original Mathlib inventory')
    require(hashlib.sha256(json.dumps(rows, sort_keys=True, separators=(',', ':')).encode()).hexdigest() ==
            root['logical_inventory_sha256'] == DIGEST, 'Wrong original logical digest')
    require(len({r['relative_path'] for r in rows}) == len(rows), 'Duplicate original path')
    selected = {r['relative_path']: r for r in rows if r['relative_path'].endswith(HASH_SUFFIXES) or r['relative_path'] in CACHE}
    require(len(selected) == 24923 and sum(r['bytes'] for r in selected.values()) == 7156488, 'Wrong recovery set')
    records = manifest['selected_records']
    require(manifest['file_count'] == len(records) == len(selected) and manifest['total_bytes'] == 7156488, 'Wrong manifest count')
    require([r['relative_path'] for r in records] == sorted(selected), 'Recovery set is incomplete or unordered')
    for row in records:
        rel = row['relative_path']
        safe_relative(rel)
        require(row['archive_path'] == 'files/' + rel and row['snapshot_record'] == selected[rel], 'Wrong original file binding')
        require('link_target' not in selected[rel], 'Unexpected original symlink')
        require(pin(files[row['archive_path']]) == {k: selected[rel][k] for k in ('bytes', 'sha256')} ==
                {k: row[k] for k in ('bytes', 'sha256')}, 'Recovery file content differs from original P2 snapshot')
    require(set(manifest['original_evidence_files']) == EVIDENCE_NAMES, 'Wrong original evidence set')
    for name in EVIDENCE_NAMES:
        require(files['evidence/' + name] == checked(EVIDENCE / name, manifest['original_evidence_files'][name]),
                'P1 transfer evidence differs from immutable original P2 metadata')
    expected = {'RESTORE_MANIFEST.json'} | {'files/' + p for p in selected} | {'evidence/' + n for n in EVIDENCE_NAMES}
    require(set(files) == expected, 'Missing or extra archive member')
    return selected


def destination_inventory():
    canonical(ROOT)
    result = set()
    for directory, dirs, names in os.walk(ROOT, followlinks=False):
        parent = canonical(directory)
        for name in dirs:
            canonical(parent / name)
        for name in names:
            if name.endswith('.olean') or '.olean.' in name:
                path = canonical(parent / name)
                require(path.is_file(), 'Unexpected runtime inode')
                result.add(path.relative_to(ROOT).as_posix())
    return result


def write_new(path, body):
    path = canonical(path, exists=False)
    with path.open('xb') as stream:
        stream.write(body)
        stream.flush()
        os.fsync(stream.fileno())


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('restore', 'verify'))
    action = parser.parse_args().action
    canonical(STAGE)
    files = unpack(checked(CAPSULE, CAPSULE_PIN))
    snapshot = json.loads(checked(SNAPSHOT, SNAPSHOT_PIN))
    guard = checked(OLD_GUARD, OLD_GUARD_PIN)
    selected = validate_payload(files, snapshot)
    original = {r['relative_path'] for root in snapshot['roots'] if root['logical_root'] == 'mathlib-objects' for r in root['files']}
    before = destination_inventory()
    launch_path, result_path = STAGE / 'RESTORE_LAUNCH.json', STAGE / 'RESTORED.json'
    binding = {'schema': 'p26_missing_original_runtime_bytes_restore_v1', 'capsule': {'path': str(CAPSULE), **CAPSULE_PIN},
               'snapshot': {'path': str(SNAPSHOT), **SNAPSHOT_PIN}, 'old_guard': {'path': str(OLD_GUARD), **OLD_GUARD_PIN},
               'manifest': MANIFEST_PIN, 'destination_root': str(ROOT), 'restored_files': 24923, 'restored_bytes': 7156488,
               'script': {'path': str(Path(__file__).resolve()), **pin(Path(__file__).read_bytes())},
               'Lean_commands': 0, 'kernel_commands': 0, 'old_guard_modified': False, 'old_receipts_modified': False,
               'runtime_compatibility_accepted': False, 'formal_acceptance': False}
    if action == 'restore':
        require(not launch_path.exists() and not result_path.exists(), 'Existing restore attempt retained; do not replay')
        require(original - before == set(selected) and not before - original, 'Current missing set differs; do not overwrite or widen recovery')
        launch = dict(binding, started_unix=time.time(), originally_missing=sorted(selected))
        write_new(launch_path, encoded(launch))
        for rel in sorted(selected):
            destination = ROOT / rel
            canonical(destination.parent, exists=False)
            destination.parent.mkdir(parents=True, exist_ok=True)
            canonical(destination.parent)
            write_new(destination, files['files/' + rel])
        require(destination_inventory() == original, 'Restored file inventory differs')
    else:
        require(before == original, 'Current runtime inventory differs')
        launch = json.loads(canonical(launch_path).read_bytes())
        require({k: launch[k] for k in binding} == binding and launch['originally_missing'] == sorted(selected), 'Restore launch binding changed')
    for rel, row in selected.items():
        checked(ROOT / rel, row)
    require(checked(OLD_GUARD, OLD_GUARD_PIN) == guard, 'Original guard document changed')
    checked(SNAPSHOT, SNAPSHOT_PIN)
    expected = dict(binding, status='ORIGINAL_MISSING_BYTES_RESTORED_ONLY', launch={'path': str(launch_path), **pin(launch_path.read_bytes())})
    if action == 'restore':
        write_new(result_path, encoded(expected))
    else:
        require(json.loads(canonical(result_path).read_bytes()) == expected, 'Restore result binding changed')
    print(json.dumps({'status': 'RESTORED' if action == 'restore' else 'RESTORE_REVERIFIED',
                      'receipt': {'path': str(result_path), **pin(result_path.read_bytes())}, **binding}, sort_keys=True))


if __name__ == '__main__':
    main()
