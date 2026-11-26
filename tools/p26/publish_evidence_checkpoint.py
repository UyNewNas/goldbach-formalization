#!/usr/bin/env python3
"""Publish exactly pinned verification artifacts from an isolated bare repo.

This does not author Lean, compile anything, or change an existing worktree.
Only the configured evidence paths are added, followed by a non-force push.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import uuid


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--config', type=Path, required=True)
    args = ap.parse_args()
    cfg = json.loads(args.config.read_text())
    repo = Path(cfg['repository']).resolve()
    stage = Path(cfg['stage']).resolve()
    assert repo.is_dir() and stage.is_dir()
    git = ['git', '--git-dir=' + str(repo)]
    branch, parent = cfg['branch'], cfg['expected_parent']
    assert branch == 'work/p2-6-source-closure-20261125'
    assert len(parent) == 40 and all(c in '0123456789abcdef' for c in parent)
    subprocess.run(git + ['fetch', '--filter=blob:none', '--depth=1', 'origin', branch], check=True)
    remote = subprocess.check_output(git + ['ls-remote', 'origin', 'refs/heads/' + branch]).decode().split()[0]
    assert remote == parent, ('remote branch advanced', remote, parent)
    env = os.environ.copy()
    env['GIT_INDEX_FILE'] = str(stage / ('evidence-index-' + uuid.uuid4().hex))
    env['GIT_AUTHOR_NAME'] = env['GIT_COMMITTER_NAME'] = 'P2.6 verification'
    env['GIT_AUTHOR_EMAIL'] = env['GIT_COMMITTER_EMAIL'] = 'p26-verification@users.noreply.github.com'
    subprocess.run(git + ['read-tree', parent], env=env, check=True)
    files = []
    for item in cfg['files']:
        source = Path(item['source']).resolve()
        dest = Path(item['repository_path'])
        assert source.is_relative_to(stage) and source.is_file()
        assert not dest.is_absolute() and '..' not in dest.parts
        assert str(dest).startswith('docs/verification/20261126-p26/')
        data = source.read_bytes()
        assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256']
        blob = subprocess.check_output(git + ['hash-object', '-w', str(source)]).decode().strip()
        subprocess.run(git + ['update-index', '--add', '--cacheinfo', '100644,' + blob + ',' + str(dest)], env=env, check=True)
        files.append({**item, 'git_blob': blob})
    tree = subprocess.check_output(git + ['write-tree'], env=env).decode().strip()
    commit = subprocess.check_output(git + ['commit-tree', tree, '-p', parent],
        input=(cfg['message'].rstrip() + '\n').encode(), env=env).decode().strip()
    subprocess.run(git + ['push', 'origin', commit + ':refs/heads/' + branch], check=True)
    observed = subprocess.check_output(git + ['ls-remote', 'origin', 'refs/heads/' + branch]).decode().split()[0]
    assert observed == commit
    print(json.dumps({'published_commit': commit, 'parent': parent, 'tree': tree,
        'branch': branch, 'files': files, 'Lean_invoked': False}), flush=True)


if __name__ == '__main__':
    main()
