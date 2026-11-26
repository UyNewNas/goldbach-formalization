#!/usr/bin/env python3
"""Exact current runtime comparison and a cheap, fail-closed post-hash guard."""
from pathlib import Path
import hashlib
import json
import os
import re
import stat

from evidence_io import canonical, fp, member_name, pin, read, require, same
from runtime_probe import fingerprint, selected
from supplier_capsule import metadata


def stat_identity(path):
    path = Path(path)
    value = path.lstat()
    return [value.st_dev, value.st_ino, value.st_mode, value.st_size, value.st_mtime_ns, value.st_ctime_ns]


def logical_roots(summary):
    return [{key: value for key, value in row.items() if key != 'physical_root'} for row in summary['roots']]


def runtime_evidence(here, plan):
    pins = read(here / 'RUNTIME_COMPATIBILITY_PINS.json')
    require(pins['schema'] == 'cell05_connections_runtime_compatibility_pins_v1', 'Unknown runtime evidence schema')
    for row in pins['files']:
        member_name(row['relative_path'])
        require(same(fp(here / row['relative_path']), row), 'Pinned runtime summary/MCP bytes changed')
    summaries = {host: read(here / f'runtime-evidence/runtime-{host}-SUMMARY.json') for host in ('P1', 'P2')}
    for host in ('P1', 'P2'):
        task = read(here / f'runtime-evidence/runtime-{host}-MCP_TASK.json')
        require(task['status'] == 'succeeded' and task['exit_code'] == 0, 'Runtime probe did not actually succeed')
        require(summaries[host]['Lean_commands'] == 0, 'Runtime probe scope differs')
    require(len(summaries['P1']['roots']) == len(summaries['P2']['roots']) == 10, 'Incomplete runtime root comparison')
    require(logical_roots(summaries['P1']) == logical_roots(summaries['P2']),
            'Actual current stock-runtime content differs; investigate before any compatibility check, never replay normal')
    rows_context = metadata(here, plan, 'rows15')[1]['context']
    fields_context = metadata(here, plan, 'fields73')[1]['context']
    require(rows_context['runtime'] == fields_context['runtime'] and rows_context['suppliers'] == fields_context['suppliers'],
            'Original binary/version/commit or common supplier bytes differ')
    for key in rows_context['environment']:
        if key == 'LEAN_PATH':
            continue
        require(rows_context['environment'][key] == fields_context['environment'][key],
                f'Original nonrelocated environment field differs: {key}')
    snapshot_identity = summaries['P2']['output']
    require(fp(snapshot_identity['path']) == snapshot_identity, 'P2 full runtime snapshot changed')
    snapshot = read(snapshot_identity['path'])
    require(snapshot['schema'] == 'cell05_current_runtime_inventory_v1'
            and snapshot['original_run'] == plan['batches']['fields73']['run']
            and snapshot['runtime'] == fields_context['runtime'], 'P2 runtime snapshot/accepted RUN binding differs')
    summary_rows = [{k: v for k, v in row.items() if k != 'files'} for row in snapshot['roots']]
    require(summary_rows == summaries['P2']['roots'], 'Full inventory and reported runtime summary differ')
    require(snapshot['historical_loaded_objects_recorded'] is False, 'Current snapshot incorrectly claims historical loads')
    for root in snapshot['roots']:
        files = root['files']
        require(files == sorted(files, key=lambda row: row['relative_path']), 'Unsorted runtime inventory')
        require(len({row['relative_path'] for row in files}) == len(files) == root['file_count'], 'Runtime file coverage differs')
        require(sum(row['bytes'] for row in files) == root['total_bytes'], 'Runtime inventory byte total differs')
        encoded = json.dumps(files, sort_keys=True, separators=(',', ':')).encode()
        require(hashlib.sha256(encoded).hexdigest() == root['logical_inventory_sha256'], 'Runtime inventory digest differs')
        for row in files:
            member_name(row['relative_path'])
    return summaries, snapshot


def capture_runtime_guard(here, plan):
    """Recheck P2 bytes once; later steps check inode/size/mtime/ctime unchanged."""
    summaries, snapshot = runtime_evidence(here, plan)
    entries = {}
    for root in snapshot['roots']:
        physical = canonical(root['physical_root'], True)
        selected_names = set()
        for folder, directories, files in os.walk(physical, followlinks=False):
            folder = canonical(folder, True)
            entries[str(folder)] = stat_identity(folder)
            for name in directories:
                canonical(folder / name, True)
            for name in files:
                if selected(name, root['kind']):
                    selected_names.add((folder / name).relative_to(physical).as_posix())
        require(selected_names == {row['relative_path'] for row in root['files']}, 'Current runtime file inventory changed')
        for row in root['files']:
            path = physical / row['relative_path']
            before = stat_identity(path)
            if 'link_target' in row:
                require(path.is_symlink(), 'Runtime link became a regular file')
                target = path.resolve(strict=True)
                require(target.is_relative_to(physical) and target.relative_to(physical).as_posix() == row['link_target'],
                        'Runtime link target changed')
                real = canonical(target, True)
            else:
                real = canonical(path, True)
            real_before = stat_identity(real)
            require(same(fingerprint(real), row), f'Current runtime file changed since the matching probes: {path}')
            require(stat_identity(path) == before and stat_identity(real) == real_before, 'Runtime changed while constructing guard')
            entries[str(path)], entries[str(real)] = before, real_before
    guard = {'schema': 'cell05_connections_runtime_guard_v1', 'snapshot': summaries['P2']['output'],
             'logical_roots': logical_roots(summaries['P2']),
             'entries': [{'path': path, 'lstat': entries[path]} for path in sorted(entries)],
             'all_selected_bytes_rehashed_before_guard': True,
             'historical_loaded_inventory_retroactively_claimed': False,
             'kernel_compatibility_replays_required': 0, 'normal_replays_permitted': False}
    check_runtime_guard_value(guard)
    return guard


def check_runtime_guard_value(guard):
    require(guard['schema'] == 'cell05_connections_runtime_guard_v1' and guard['all_selected_bytes_rehashed_before_guard'] is True,
            'Invalid runtime guard')
    require(len({row['path'] for row in guard['entries']}) == len(guard['entries']), 'Duplicate runtime guard path')
    for row in guard['entries']:
        require(stat_identity(row['path']) == row['lstat'], f'Current runtime file/directory changed: {row["path"]}')


def check_runtime_guard(identity):
    require(fp(identity['path']) == identity, 'Runtime guard document changed')
    check_runtime_guard_value(read(identity['path']))


def git_commit_readonly(root):
    """Read a checkout's HEAD without invoking Git or changing its index."""
    root = canonical(root, True)
    git = root / '.git'
    if git.is_file():
        value = git.read_text().strip()
        require(value.startswith('gitdir: '), 'Unknown checkout metadata format')
        git = (root / value[len('gitdir: '):]).resolve()
    git = canonical(git, True)
    value = (git / 'HEAD').read_text().strip()
    if not value.startswith('ref: '):
        require(re.fullmatch('[0-9a-f]{40}', value), 'Malformed detached checkout HEAD')
        return value
    ref = value[len('ref: '):]
    member_name(ref)
    require(ref.startswith('refs/'), 'Malformed symbolic checkout HEAD')
    common = git
    if (git / 'commondir').is_file():
        common = canonical((git / (git / 'commondir').read_text().strip()).resolve(), True)
    for folder in (git, common):
        if (folder / ref).is_file():
            result = (folder / ref).read_text().strip()
            require(re.fullmatch('[0-9a-f]{40}', result), 'Malformed loose commit reference')
            return result
    for folder in (git, common):
        packed = folder / 'packed-refs'
        if packed.is_file():
            for line in packed.read_text().splitlines():
                parts = line.split()
                if len(parts) == 2 and parts[1] == ref:
                    require(re.fullmatch('[0-9a-f]{40}', parts[0]), 'Malformed packed commit reference')
                    return parts[0]
    raise RuntimeError('Mathlib commit reference is missing')
