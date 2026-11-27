#!/usr/bin/env python3
"""Stage exact published Geometry entrypoints; never install or compile Lean.

FINAL_ENTRYPOINTS is deliberately unbound until the actual successful probe is
bound into run_geometry.py and both final entrypoint fingerprints are known.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
sys.dont_write_bytecode = True

REPO = Path('/workspace/goldbach-formalization')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
INSTALL_ROOT = Path('/workspace/p1-complete-proof/20261127-p15-geometry-source-install-v1')
PACKAGE = 'docs/p1/20261127/p15-remaining-typei-geometry/'
SCRIPT = PACKAGE + 'stage_geometry_formal.py'
AM = '45e8de70fb3045b04f3ef3ad2ff364c7ee2f390c'
FINAL_ENTRYPOINTS = {
    'run_geometry.py': {'bytes': 43509, 'sha256': 'e52e170a0d06b40b3d52020a2f2627df48dbd621c53099c696a8a0caac5703ff'},
    'install_geometry_source.py': {'bytes': 8894, 'sha256': '51a56303977a040e4ffcbd020f2068e4bad08427ba0a0e5af264bada9f9a3c3b'},
}


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def git(*arguments):
    return subprocess.check_output(['git', *arguments], cwd=REPO)


def gitstate():
    return {name: fp(git(*arguments)) for name, arguments in {
        'head': ['rev-parse', 'HEAD'],
        'status': ['status', '--porcelain=v1', '--untracked-files=all'],
        'worktree_diff': ['diff', '--binary'],
        'index_diff': ['diff', '--cached', '--binary']}.items()}


def put(path, payload):
    path.parent.mkdir(parents=True, exist_ok=True)
    require(path.parent.resolve() == path.parent and path.resolve() == path,
            'published entrypoint path traverses a symlink')
    if os.path.lexists(path):
        require(path.is_file() and not path.is_symlink() and path.read_bytes() == payload,
                'existing published entrypoint differs; replacement is forbidden')
        return
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o644)
    with os.fdopen(descriptor, 'wb') as stream:
        stream.write(payload); stream.flush(); os.fsync(stream.fileno())
    directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--publication', required=True)
    args = parser.parse_args()
    require(__debug__ and isinstance(FINAL_ENTRYPOINTS, dict) and
            set(FINAL_ENTRYPOINTS) == {'run_geometry.py', 'install_geometry_source.py'} and
            all(isinstance(row, dict) and type(row.get('bytes')) is int and row['bytes'] > 0 and
                isinstance(row.get('sha256'), str) and re.fullmatch('[0-9a-f]{64}', row['sha256'])
                for row in FINAL_ENTRYPOINTS.values()), 'final Geometry entrypoint fingerprints are unbound')
    publication = args.publication
    require(re.fullmatch('[0-9a-f]{40}', publication), 'exact publication commit required')
    own_path = Path(__file__)
    require(own_path.is_file() and not own_path.is_symlink(), 'stager must be a regular file')
    before = gitstate()
    subprocess.run(['git', '-c', 'maintenance.auto=false', 'fetch', '--no-tags',
                    '--no-write-fetch-head', 'origin', publication], cwd=REPO, check=True)
    require(subprocess.run(['git', 'merge-base', '--is-ancestor', AM, publication],
                           cwd=REPO).returncode == 0, 'formal publication must descend from AM')
    require(own_path.read_bytes() == git('show', publication + ':' + SCRIPT),
            'executed final stager differs from its exact publication')
    files = []
    for name, root in [('run_geometry.py', ROOT), ('install_geometry_source.py', INSTALL_ROOT)]:
        source = PACKAGE + name
        payload = git('show', publication + ':' + source)
        require(fp(payload) == FINAL_ENTRYPOINTS[name], 'published entrypoint fingerprint differs: ' + name)
        path = root / publication / 'published-entrypoints' / name
        put(path, payload)
        files.append({'source': source, 'path': str(path), **fp(payload)})
    after = gitstate()
    require(before == after, 'original Git head/status/worktree/index state changed during staging')
    receipt = {'schema': 'p15_geometry_formal_entrypoints_staging_v1',
        'status': 'EXACT_GEOMETRY_FORMAL_ENTRYPOINTS_STAGED', 'commit': publication,
        'files': files, 'original_git_state_unchanged': True, 'git_state': after,
        'canonical_source_installed': False, 'normal_or_kernel_commands_executed': 0,
        'new_owner_accepted': False, 'whole_P1_5_complete': False}
    path = ROOT / publication / 'published-entrypoints/GEOMETRY_STAGING_RECEIPT.json'
    put(path, (json.dumps(receipt, sort_keys=True, indent=2) + '\n').encode())
    print(json.dumps({'receipt_path': str(path), **receipt}, sort_keys=True), flush=True)
    return 0


if __name__ == '__main__':
    os.environ.update({'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'})
    try:
        raise SystemExit(main())
    except Exception as error:
        print(json.dumps({'status': 'GEOMETRY_FORMAL_STAGING_HOLD', 'error_type': type(error).__name__,
            'error': str(error), 'canonical_source_installed': False,
            'new_owner_accepted': False, 'whole_P1_5_complete': False}), flush=True)
        raise SystemExit(3)
