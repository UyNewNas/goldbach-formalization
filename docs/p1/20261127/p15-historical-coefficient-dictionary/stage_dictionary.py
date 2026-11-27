#!/usr/bin/env python3
"""Stage only the exact published dictionary probe; do not install Lean sources."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys

REPO = Path('/workspace/goldbach-formalization')
AK = 'd4f88a20262af7d54ed0e6e58dfc533496c595e3'
AM = '45e8de70fb3045b04f3ef3ad2ff364c7ee2f390c'
SCRIPT = 'docs/p1/20261127/p15-historical-coefficient-dictionary/probe_dictionary.py'
SCRIPT_FP = {'bytes': 29728, 'sha256': '4ff5139a3c9eacd16f29e11a99da8cee7c20541a284ad9538458b3caaf4ea8c4'}
ORIGINAL_ORIGIN = 'docs/source-only/20261127/p1-historical-coefficient-dictionary/P1OriginalHistoricalCoefficientDictionary.lean'
ORIGIN = 'docs/source-only/20261127/p1-historical-coefficient-dictionary-if-neg-repair/P1OriginalHistoricalCoefficientDictionary.lean'
ORIGINAL_SOURCE_FP = {'bytes': 9079, 'sha256': 'b90556b05b152cea39fd72eb55428986105ad86a4926e2badf50175927c47409'}
SOURCE_FP = {'bytes': 9107, 'sha256': 'eb78b1ba6ced1f441b8b923210ef1fc32c107b307be69c0c3f6d2b8fd91d97ff'}
PROBE_ROOT = Path('/workspace/p1-complete-proof/20261127-p15-historical-coefficient-dictionary-probe-v1')


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def require_corrected_source(original, source):
    old = b'    simp [roughMaskDelta, attachedMobius, hnew, hold, signAttachedCoefficient]\n'
    new = b'    simp [roughMaskDelta, attachedMobius, hnew, hold, signAttachedCoefficient] <;>\n      split_ifs <;> rfl\n'
    require(fp(original) == ORIGINAL_SOURCE_FP and original.count(old) == 1 and
            fp(source) == SOURCE_FP and source == original.replace(old, new),
            'dictionary is not the exact proof-only if-neg repair')


def git(*argv):
    return subprocess.check_output(['git', *argv], cwd=REPO)


def gitstate():
    return {key: fp(git(*args)) for key, args in {
        'head': ['rev-parse', 'HEAD'],
        'status': ['status', '--porcelain=v1', '--untracked-files=all'],
        'worktree_diff': ['diff', '--binary'],
        'index_diff': ['diff', '--cached', '--binary']}.items()}


def put(path, raw):
    require(path.parent.resolve() == path.parent, 'staging parent traverses a symlink')
    path.parent.mkdir(parents=True, exist_ok=True)
    require(path.parent.resolve() == path.parent, 'staging parent changed')
    if os.path.lexists(path):
        require(not path.is_symlink() and path.is_file() and path.read_bytes() == raw,
                'nonregular or different existing staging file')
        return
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o644)
    with os.fdopen(descriptor, 'wb') as stream:
        stream.write(raw)
        stream.flush()
        os.fsync(stream.fileno())
    descriptor = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def stage(publication):
    require(__debug__ and re.fullmatch('[0-9a-f]{40}', publication), 'exact publication commit required')
    before = gitstate()
    subprocess.run(['git', '-c', 'maintenance.auto=false', 'fetch', '--no-tags',
                    '--no-write-fetch-head', 'origin', publication], cwd=REPO, check=True)
    require(subprocess.run(['git', 'merge-base', '--is-ancestor', AM, publication], cwd=REPO).returncode == 0,
            'publication does not descend from original failed AM')
    raw = git('show', publication + ':' + SCRIPT)
    source = git('show', publication + ':' + ORIGIN)
    require(fp(raw) == SCRIPT_FP, 'published probe bytes differ')
    original = git('show', AK + ':' + ORIGINAL_ORIGIN)
    require(git('show', publication + ':' + ORIGINAL_ORIGIN) == original,
            'original AK dictionary source changed')
    require_corrected_source(original, source)
    root = PROBE_ROOT / publication / 'published-entrypoints'
    path = root / 'probe_dictionary.py'
    put(path, raw)
    after = gitstate()
    require(before == after, 'original Git worktree or index changed')
    receipt = {'status': 'EXACT_DICTIONARY_PROBE_PUBLICATION_STAGED', 'commit': publication,
               'files': [{'source': SCRIPT, 'path': str(path), **fp(raw)}],
               'frozen_Lean_origin': {'commit': publication, 'path': ORIGIN, **SOURCE_FP},
               'original_Lean_origin': {'commit': AK, 'path': ORIGINAL_ORIGIN, **ORIGINAL_SOURCE_FP},
               'original_git_state_unchanged': True, 'git_state': after,
               'new_lean_acceptance': False, 'canonical_source_installed': False}
    put(root / 'STAGING_RECEIPT.json', (json.dumps(receipt, indent=2, sort_keys=True) + '\n').encode())
    print(json.dumps(receipt, sort_keys=True), flush=True)


if __name__ == '__main__':
    os.environ.update({'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'})
    require(len(sys.argv) == 2, 'usage: stage_dictionary.py FULL_PUBLICATION_COMMIT')
    stage(sys.argv[1])
