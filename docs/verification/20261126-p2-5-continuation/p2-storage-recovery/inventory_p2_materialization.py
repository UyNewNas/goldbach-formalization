#!/usr/bin/env python3
"""Read-only materialization inventory for the exact P2 continuation worktree."""
from collections import defaultdict
from pathlib import Path
import hashlib
import json
import os
import shutil
import stat
import subprocess

ROOT = Path('/workspace/p2-saving16-20261125')
PUBLICATION = '6a4bfce285e1512b3ba31fb408812040b8aee368'
ENV = dict(os.environ, GIT_OPTIONAL_LOCKS='0')
GIT = ['git', '-c', 'gc.auto=0', '-c', 'maintenance.auto=false', '-c', 'core.fsmonitor=false']


def git(*args, cwd=ROOT, allowed=(0,)):
    result = subprocess.run(GIT + list(args), cwd=cwd, env=ENV, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, timeout=60)
    assert result.returncode in allowed, result.stderr.decode(errors='replace')
    return result.stdout


def bucket(rows, path, size, allocated, materialized=True):
    parts = Path(path).parts[:-1]
    keys = {'/'.join(parts[:depth]) for depth in range(1, min(3, len(parts)) + 1)} or {'(root files)'}
    for key in keys:
        row = rows[key]
        row['files'] += 1
        row['logical_bytes'] += size
        row['conservative_allocated_bytes'] += allocated
        row['materialized'] += int(materialized)


def main():
    assert ROOT.resolve() == ROOT
    head = git('rev-parse', 'HEAD').decode().strip()
    assert head == PUBLICATION, head
    tracked_status = git('status', '--porcelain', '--untracked-files=no').decode()
    assert not tracked_status, tracked_status
    groups = defaultdict(lambda: dict(files=0, logical_bytes=0, conservative_allocated_bytes=0, materialized=0))
    tracked = []
    symlinks = []
    total = dict(files=0, logical_bytes=0, conservative_allocated_bytes=0, materialized=0)
    for item in git('ls-files', '--stage', '-z').split(b'\0'):
        if not item:
            continue
        metadata, name = item.split(b'\t', 1)
        mode, oid, stage = metadata.decode().split()
        assert stage == '0'
        relative = os.fsdecode(name)
        path = ROOT / relative
        materialized = os.path.lexists(path)
        size = allocated = 0
        if materialized:
            info = path.lstat()
            assert stat.S_ISREG(info.st_mode) or stat.S_ISLNK(info.st_mode)
            size = info.st_size
            allocated = info.st_blocks * 512 if info.st_nlink == 1 else 0
            if stat.S_ISLNK(info.st_mode):
                symlinks.append(dict(path=relative, target=os.readlink(path), resolved=str(path.resolve())))
        row = dict(path=relative, mode=mode, object=oid, logical_bytes=size,
                   conservative_allocated_bytes=allocated, materialized=materialized)
        tracked.append(row)
        bucket(groups, relative, size, allocated, materialized)
        total['files'] += 1
        total['logical_bytes'] += size
        total['conservative_allocated_bytes'] += allocated
        total['materialized'] += int(materialized)
    untracked_groups = defaultdict(lambda: dict(files=0, logical_bytes=0, conservative_allocated_bytes=0, materialized=0))
    untracked_source_only = []
    for name in git('ls-files', '--others', '-z').split(b'\0'):
        if not name:
            continue
        relative = os.fsdecode(name)
        path = ROOT / relative
        info = path.lstat()
        bucket(untracked_groups, relative, info.st_size, info.st_blocks * 512 if info.st_nlink == 1 else 0)
        if relative.startswith('docs/source-only/'):
            untracked_source_only.append(relative)
    common = Path(git('rev-parse', '--path-format=absolute', '--git-common-dir').decode().strip())
    worktree_config_enabled = git('config', '--bool', '--get', 'extensions.worktreeConfig', allowed=(0, 1)).decode().strip() or None
    worktrees = []
    for item in git('worktree', 'list', '--porcelain', '-z').split(b'\0'):
        if item.startswith(b'worktree '):
            path = Path(os.fsdecode(item)[9:])
            gd = Path(git('rev-parse', '--absolute-git-dir', cwd=path).decode().strip())
            config = gd / 'config.worktree'
            raw = config.read_bytes() if config.is_file() else b''
            # No config values or remotes are emitted.
            keys = git('config', '--file', str(config), '--name-only', '--list', cwd=path).decode().splitlines() if raw else []
            worktrees.append(dict(path=str(path), gitdir=str(gd), head=git('rev-parse', 'HEAD', cwd=path).decode().strip(),
                                  private_config_present=config.exists(), private_config_bytes=len(raw),
                                  private_config_sha256=hashlib.sha256(raw).hexdigest() if raw else None,
                                  private_config_keys=keys))
    disk = shutil.disk_usage(ROOT)
    print('P25_P2_MATERIALIZATION_INVENTORY ' + json.dumps(dict(
        schema='p25-p2-readonly-materialization-inventory-v1', root=str(ROOT), head=head,
        tree=git('rev-parse', 'HEAD^{tree}').decode().strip(), git_version=git('--version').decode().strip(),
        common_gitdir=str(common), extensions_worktree_config=worktree_config_enabled,
        disk=dict(total=disk.total, used=disk.used, free=disk.free), tracked_total=total,
        tracked_groups=dict(sorted(groups.items())),
        largest_tracked_files=sorted(tracked, key=lambda r:r['conservative_allocated_bytes'], reverse=True)[:40],
        all_tracked_symlinks=symlinks, untracked_groups=dict(sorted(untracked_groups.items())),
        untracked_source_only_paths=untracked_source_only, worktrees=worktrees,
        read_only=True, mutation_performed=False), separators=(',', ':')), flush=True)


if __name__ == '__main__':
    main()
