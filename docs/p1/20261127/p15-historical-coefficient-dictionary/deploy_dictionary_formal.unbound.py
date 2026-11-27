#!/usr/bin/env python3
"""Bootstrap the exact final stager. INPUTS=None prohibits fetch, write or run."""
from pathlib import Path
import argparse
import ast
import hashlib
import json
import os
import re
import subprocess
import sys
sys.dont_write_bytecode = True

REPO = Path('/workspace/goldbach-formalization')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
AO = '74926278c913d45401225c1b7e08185c9eec57e9'
AN = '938a761761f0e8a96404f843488f0a733818b156'
STAGER = 'docs/p1/20261127/p15-historical-coefficient-dictionary/stage_dictionary_formal.py'
INPUTS = None


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def require_bound_inputs():
    require(__debug__ and isinstance(INPUTS, dict) and INPUTS.get('probe_publication') == AO and
            isinstance(INPUTS.get('stager'), dict) and set(INPUTS['stager']) == {'bytes', 'sha256'} and
            type(INPUTS['stager']['bytes']) is int and INPUTS['stager']['bytes'] > 0 and
            isinstance(INPUTS['stager']['sha256'], str) and re.fullmatch('[0-9a-f]{64}', INPUTS['stager']['sha256']),
            'final dictionary bootstrap INPUTS are unbound')


def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def git(*args):
    return subprocess.check_output(['git', *args], cwd=REPO)


def gitstate():
    return {name: fp(git(*args)) for name, args in {
        'head': ['rev-parse', 'HEAD'], 'status': ['status', '--porcelain=v1', '--untracked-files=all'],
        'worktree_diff': ['diff', '--binary'], 'index_diff': ['diff', '--cached', '--binary']}.items()}


def put(path, raw):
    require(path.parent.resolve() == path.parent and path.resolve() == path,
            'bootstrap path traverses a symlink')
    path.parent.mkdir(parents=True, exist_ok=True)
    require(path.parent.resolve() == path.parent, 'bootstrap parent changed')
    if os.path.lexists(path):
        require(path.is_file() and not path.is_symlink() and path.read_bytes() == raw,
                'different existing stager cannot be overwritten')
        return
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o644)
    with os.fdopen(descriptor, 'wb') as stream:
        stream.write(raw); stream.flush(); os.fsync(stream.fileno())
    directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def deploy(publication):
    require_bound_inputs()
    require(isinstance(publication, str) and re.fullmatch('[0-9a-f]{40}', publication) and
            publication not in (AO, AN), 'bootstrap needs a unique new formal publication after AO')
    before = gitstate()
    subprocess.run(['git', '-c', 'maintenance.auto=false', 'fetch', '--no-tags', '--no-write-fetch-head',
                    'origin', publication], cwd=REPO, check=True)
    require(subprocess.run(['git', 'merge-base', '--is-ancestor', AO, publication], cwd=REPO).returncode == 0,
            'formal publication does not descend from AO')
    raw = git('show', publication + ':' + STAGER)
    require(fp(raw) == INPUTS['stager'], 'published final stager fingerprint differs')
    assignments = [node for node in ast.parse(raw.decode('utf-8')).body if isinstance(node, ast.Assign) and
        any(isinstance(target, ast.Name) and target.id == 'INPUTS' for target in node.targets)]
    require(len(assignments) == 1 and isinstance(ast.literal_eval(assignments[0].value), dict),
            'pinned formal stager is still unbound')
    path = ROOT / publication / 'published-entrypoints/stage_dictionary_formal.py'
    put(path, raw)
    require(gitstate() == before, 'Git state changed before final staging')
    subprocess.run([sys.executable, '-B', str(path), '--publication', publication], cwd=REPO, check=True)
    after = gitstate()
    require(after == before, 'Git state changed during final staging')
    result = {'schema': 'p15_dictionary_formal_bootstrap_v1', 'publication': publication,
        'stager': {'source': STAGER, 'path': str(path), **fp(raw)}, 'original_git_state_unchanged': True,
        'git_state': after, 'canonical_source_installed': False, 'normal_or_kernel_commands_executed': 0,
        'new_owner_accepted': False, 'whole_P1_5_complete': False}
    receipt = path.parent / 'DICTIONARY_BOOTSTRAP_RECEIPT.json'
    put(receipt, (json.dumps(result, indent=2, sort_keys=True) + '\n').encode())
    print(json.dumps({'receipt_path': str(receipt), **result}, sort_keys=True), flush=True)
    return 0


def main():
    require_bound_inputs()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--publication', required=True)
    return deploy(parser.parse_args().publication)


if __name__ == '__main__':
    try:
        require_bound_inputs()
        os.environ.update({'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                           'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'})
        raise SystemExit(main())
    except Exception as error:
        print(json.dumps({'status': 'DICTIONARY_FORMAL_BOOTSTRAP_HOLD', 'error_type': type(error).__name__,
            'error': str(error), 'canonical_source_installed': False, 'new_owner_accepted': False,
            'whole_P1_5_complete': False}), flush=True)
        raise SystemExit(3)
