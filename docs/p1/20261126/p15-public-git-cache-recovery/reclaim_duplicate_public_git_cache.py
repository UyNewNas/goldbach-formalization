#!/usr/bin/env python3
"""Reclaim only P1 public Git packs proved redundant by the frozen read-only plan."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

REPO = Path('/workspace/goldbach-formalization')
PACK = REPO / '.git/objects/pack'
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-public-git-cache-maintenance-v1')
PLAN = ROOT / 'VERIFIED_PLAN.json'
UNION_SHA = '79ca3ec76032ad4583b4e49c464094b10b25c394ab787f539af075b682f9b5d8'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def stat(path):
    s = path.lstat()
    assert path.is_file() and not path.is_symlink(), str(path)
    return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns]


def fingerprint(path):
    before = stat(path)
    h = hashlib.sha256()
    with path.open('rb') as f:
        for part in iter(lambda: f.read(4 * 1024 * 1024), b''):
            h.update(part)
    assert stat(path) == before
    return {'stat': before, 'sha256': h.hexdigest()}


def git(args, input=None):
    r = subprocess.run(['git'] + args, cwd=REPO, input=input,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
    assert r.returncode == 0, (args, r.returncode, r.stderr[:1000])
    return r.stdout


def git_state():
    # Opaque fingerprints: do not print the pre-existing dirty paths or ref contents.
    return {key: sha(git(args)) for key, args in {
        'HEAD': ['rev-parse', 'HEAD'],
        'refs': ['show-ref', '--head', '--dereference'],
        'status': ['status', '--porcelain=v1', '-z', '--untracked-files=all'],
    }.items()}


def durable_json(path, value):
    raw = (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()
    with path.open('xb') as f:
        f.write(raw)
        f.flush()
        os.fsync(f.fileno())
    return {'path': str(path), 'bytes': len(raw), 'sha256': sha(raw)}


def main():
    if not __debug__:
        raise RuntimeError('Optimized Python disables this cache repair gate; refusing all changes')
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--verified-plan-sha256', required=True)
    args = p.parse_args()
    raw = PLAN.read_bytes()
    assert sha(raw) == args.verified_plan_sha256
    plan = json.loads(raw)
    assert plan['schema'] == 'p15_public_git_duplicate_cache_verified_v1'
    assert plan['retained_git_verify_pack_exit'] == 0
    old = plan['original_plan']
    assert old['object_union_sha256'] == UNION_SHA and old['object_union_count'] == 63190
    assert old['total_packs'] == 65 and len(old['kept']) == 9 and len(old['redundant']) == 56
    assert old['redundant_pack_bytes'] == 1927063141
    keep = {r['stem'] for r in old['kept']}
    drop = {r['stem'] for r in old['redundant']}
    assert not keep & drop and keep | drop == set(plan['pack_files'])
    assert {f.stem for f in PACK.glob('pack-*.idx')} == keep | drop
    for lock in [REPO / '.git/index.lock', REPO / '.git/shallow.lock',
                 REPO / '.git/packed-refs.lock', PACK / 'multi-pack-index.lock']:
        assert not lock.exists(), str(lock)
    assert not (ROOT / 'CACHE_RECLAIM_RESULT.json').exists()
    assert not (ROOT / 'holding-duplicates').exists()
    before = git_state()
    original_ids = set()
    retained_ids = set()
    for stem, files in plan['pack_files'].items():
        assert set(files) <= {'.pack', '.idx', '.rev', '.keep'}
        assert {'.pack', '.idx'} <= set(files)
        assert stem in keep or '.keep' not in files
        for ext, row in files.items():
            assert fingerprint(PACK / (stem + ext)) == row
        index = (PACK / (stem + '.idx')).read_bytes()
        assert index[:8] == b'\xfftOc\x00\x00\x00\x02'
        assert hashlib.sha1(index[:-20]).digest() == index[-20:]
        n = int.from_bytes(index[1028:1032], 'big')
        ids = {index[1032 + 20*i:1052 + 20*i] for i in range(n)}
        original_ids.update(ids)
        if stem in keep:
            retained_ids.update(ids)
    assert original_ids == retained_ids and len(retained_ids) == 63190
    assert sha(b''.join(sorted(retained_ids))) == UNION_SHA
    assert git_state() == before
    disk_before = shutil.disk_usage('/workspace').free
    original_index = PACK / 'multi-pack-index'
    original_index_pin = fingerprint(original_index)
    saved_index = ROOT / 'original-multi-pack-index'
    assert not saved_index.exists()
    holding = ROOT / 'holding-duplicates'
    holding.mkdir(mode=0o700)
    moved = []
    deleted_bytes = 0
    deleted_files = 0
    try:
        # Both the old index and every redundant pack remain recoverable until
        # the real Git reader and the replacement index have passed below.
        assert fingerprint(original_index) == original_index_pin
        original_index.rename(saved_index)
        for stem in sorted(drop):
            if os.path.lexists(PACK / (stem + '.keep')):
                raise RuntimeError('A redundant pack now has a keep marker: ' + stem)
            for ext, row in plan['pack_files'][stem].items():
                source = PACK / (stem + ext)
                assert stat(source) == row['stat']
                target = holding / source.name
                assert not target.exists()
                source.rename(target)
                moved.append((source, target))
        assert {f.stem for f in PACK.glob('pack-*.idx')} == keep
        ordered = sorted(retained_ids)
        request = b''.join(k.hex().encode() + b'\n' for k in ordered)
        observed = git(['cat-file', '--batch-check=%(objectname) %(objecttype) %(objectsize)'], request)
        lines = observed.splitlines()
        assert len(lines) == len(ordered)
        for expected, line in zip(ordered, lines):
            parts = line.split()
            assert len(parts) == 3 and parts[0] == expected.hex().encode()
            assert parts[1] in (b'blob', b'tree', b'commit', b'tag') and parts[2].isdigit()
        git(['multi-pack-index', 'write'])
        git(['multi-pack-index', 'verify'])
        for stem in keep:
            for ext, row in plan['pack_files'][stem].items():
                assert stat(PACK / (stem + ext)) == row['stat']
        assert git_state() == before
        durable_json(ROOT / 'PRE_DELETE_VALIDATION.json', {
            'verified_plan_sha256': args.verified_plan_sha256,
            'original_object_count': len(original_ids), 'all_original_objects_readable': True,
            'object_union_sha256': UNION_SHA, 'retained_git_verify_pack_exit': 0,
            'replacement_multi_pack_index_verify_exit': 0, 'git_state_before_and_after': before,
            'original_multi_pack_index': original_index_pin,
            'moved_duplicate_files': len(moved), 'only_duplicate_objects': True,
        })
        # Finish every deletion prerequisite while all files are still recoverable.
        for stem in drop:
            if os.path.lexists(PACK / (stem + '.keep')):
                raise RuntimeError('A moved duplicate now has a keep marker: ' + stem)
        for source, target in moved:
            row = plan['pack_files'][source.stem][source.suffix]
            assert stat(target) == row['stat']
        for source, target in moved:
            if os.path.lexists(PACK / (source.stem + '.keep')):
                raise RuntimeError('Keep marker appeared before deletion: ' + source.stem)
            row = plan['pack_files'][source.stem][source.suffix]
            assert stat(target) == row['stat']
            target.unlink()
            deleted_files += 1
            deleted_bytes += row['stat'][2]
    finally:
        if deleted_files == 0:
            # No duplicate bytes have been deleted on this path.
            for source, target in reversed(moved):
                if target.exists():
                    assert not source.exists()
                    target.rename(source)
            if saved_index.exists():
                if original_index.exists():
                    original_index.rename(ROOT / 'failed-replacement-multi-pack-index')
                saved_index.rename(original_index)
    holding.rmdir()
    result = {
        'schema': 'p15_redundant_public_git_cache_reclaimed_v1',
        'status': 'VERIFIED_DUPLICATE_PUBLIC_GIT_PACKS_RECLAIMED',
        'verified_plan_sha256': args.verified_plan_sha256,
        'original_packs': 65, 'retained_packs': 9, 'removed_duplicate_packs': 56,
        'original_object_count': 63190, 'retained_object_count': 63190,
        'object_union_sha256': UNION_SHA, 'all_original_objects_readable': True,
        'deleted_duplicate_files': deleted_files, 'deleted_duplicate_file_bytes': deleted_bytes,
        'workspace_free_before': disk_before, 'workspace_free_after': shutil.disk_usage('/workspace').free,
        'git_state_before': before, 'git_state_after': git_state(),
        'old_multi_pack_index_preserved': str(saved_index),
        'source_runtime_receipt_or_Lean_artifact_paths_modified': [],
        'Lean_commands': 0,
    }
    assert result['git_state_after'] == before
    binding = durable_json(ROOT / 'CACHE_RECLAIM_RESULT.json', result)
    print(json.dumps({'result': result, 'result_binding': binding}, sort_keys=True), flush=True)


if __name__ == '__main__':
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    os.environ['GIT_NO_LAZY_FETCH'] = '1'
    main()
