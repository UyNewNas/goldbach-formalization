#!/usr/bin/env python3
"""Read-only runtime inventory; no Lean, Git, extraction or proof command.

The output is a current snapshot, not a retroactive record of historical loads.
Logical root names deliberately exclude host directory names. Differences are
reported for investigation; this probe never schedules kernel compatibility.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import stat
import sys

sys.dont_write_bytecode = True


def require(value, message):
    if not value:
        raise RuntimeError(message)


def pin_bytes(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def canonical(path):
    path = Path(path)
    require(path.is_absolute() and '..' not in path.parts, f'Noncanonical path: {path}')
    for parent in [*reversed(path.parents), path]:
        require(not parent.is_symlink(), f'Symlink in root/output path: {parent}')
    return path


def fingerprint(path):
    path = canonical(path)
    require(path.is_file(), f'Missing regular file: {path}')
    before = path.stat()
    digest = hashlib.sha256()
    with path.open('rb') as incoming:
        for chunk in iter(lambda: incoming.read(1024 * 1024), b''):
            digest.update(chunk)
    after = path.stat()
    require((before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns)
            == (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns),
            f'File changed while hashing: {path}')
    return {'bytes': after.st_size, 'sha256': digest.hexdigest()}


def selected(name, kind):
    if kind == 'objects':
        return name.endswith('.olean') or '.olean.' in name
    return name.endswith('.so') or '.so.' in name


def inventory(root, kind):
    root = canonical(root)
    require(root.is_dir(), f'Missing runtime root: {root}')
    rows, links, stats = [], [], {}
    for folder, directories, files in os.walk(root, followlinks=False):
        folder = Path(folder)
        for name in directories:
            child = folder / name
            require(not child.is_symlink(), f'Symlink directory in runtime inventory: {child}')
        for name in sorted(files):
            if not selected(name, kind):
                continue
            path = folder / name
            logical = path.relative_to(root).as_posix()
            if path.is_symlink():
                target = path.resolve(strict=True)
                require(target.is_relative_to(root), f'Runtime file link escapes root: {path}')
                row = {'relative_path': logical, 'link_target': target.relative_to(root).as_posix(),
                       **fingerprint(target)}
                links.append(row)
                stats[str(path)] = ('link', os.readlink(path))
            else:
                require(stat.S_ISREG(path.lstat().st_mode), f'Nonregular runtime file: {path}')
                row = {'relative_path': logical, **fingerprint(path)}
                s = path.stat()
                stats[str(path)] = ('file', s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
            rows.append(row)
    rows.sort(key=lambda row: row['relative_path'])
    require(rows or kind == 'libraries', f'Empty object root: {root}')
    return rows, stats


def check_stats(stats):
    for name, expected in stats.items():
        path = Path(name)
        if expected[0] == 'link':
            actual = ('link', os.readlink(path))
        else:
            s = path.stat()
            actual = ('file', s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
        require(actual == expected, f'Runtime input changed during probe: {name}')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--run', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    run_path, output = canonical(args.run), canonical(args.output)
    require(not output.exists(), f'Refusing output overwrite: {output}')
    require(output.parent.is_dir(), 'Output parent must already exist')
    run_pin = fingerprint(run_path)
    run = json.loads(run_path.read_text())
    context = run['context']
    require(context['schema'] == 'cell05_complete_context_v2', 'Unexpected original context schema')
    runtime = context['runtime']
    for key in ('lean_binary', 'leanchecker_binary'):
        require(fingerprint(runtime[key]['path']) == {k: runtime[key][k] for k in ('bytes', 'sha256')},
                f'Current binary differs from original RUN: {key}')
    sysroot = Path(context['environment']['LEAN_SYSROOT'])
    roots = [('toolchain-objects', sysroot / 'lib/lean', 'objects')]
    for raw in context['mathlib_package_object_roots']:
        root = Path(raw)
        suffix = Path('.lake/build/lib/lean')
        require(root.parts[-4:] == suffix.parts, f'Unexpected package root: {root}')
        roots.append(('package-' + root.parents[3].name, root, 'objects'))
    roots.extend([('mathlib-objects', Path(context['mathlib_objects']), 'objects'),
                  ('toolchain-libraries', sysroot / 'lib', 'libraries')])
    require(len({name for name, _, _ in roots}) == len(roots), 'Duplicate logical runtime root')
    result_roots, all_stats = [], {}
    for name, root, kind in roots:
        rows, stats = inventory(root, kind)
        all_stats.update(stats)
        encoded = json.dumps(rows, sort_keys=True, separators=(',', ':')).encode()
        result_roots.append({'logical_root': name, 'physical_root': str(root), 'kind': kind,
                             'file_count': len(rows), 'total_bytes': sum(row['bytes'] for row in rows),
                             'logical_inventory_sha256': hashlib.sha256(encoded).hexdigest(), 'files': rows})
    check_stats(all_stats)
    require(fingerprint(run_path) == run_pin, 'RUN changed during probe')
    result = {'schema': 'cell05_current_runtime_inventory_v1', 'original_run': {'path': str(run_path), **run_pin},
              'runtime': runtime, 'roots': result_roots,
              'snapshot_kind': 'current_full_stock_olean_sidecar_and_toolchain_shared_library_inventory',
              'historical_loaded_objects_recorded': False, 'Lean_commands': 0, 'Git_commands': 0,
              'kernel_replay_decision': 'none; compare logical identities, then investigate any actual differences'}
    data = (json.dumps(result, indent=2) + '\n').encode()
    with output.open('xb') as out:
        out.write(data)
    require(fingerprint(output) == pin_bytes(data), 'Probe output readback mismatch')
    print(json.dumps({'output': {'path': str(output), **pin_bytes(data)}, 'Lean_commands': 0,
                      'roots': [{k: v for k, v in row.items() if k != 'files'} for row in result_roots]}, indent=2))


if __name__ == '__main__':
    main()
