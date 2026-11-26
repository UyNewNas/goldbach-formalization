python3 -B - --commit bb5081e19ace341ef1afa1bb8d4656161546b2da <<'PY_P26_P3_PREPARATION_V2_RECEIVE'
#!/usr/bin/env python3
"""Fetch one fixed preparation archive from a reviewed immutable source commit.

Only a fresh Git receiver and one fresh archive file are written. No checkout,
extraction, existing provider mutation, adapter launch or proof is performed.
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
URL = 'https://github.com/UyNewNas/goldbach-formalization.git'
RECEIVER = Path('/workspace/p26-cell01-preparation-v2-fetch-557a12f3bcd7')
ARCHIVE = Path('/workspace/p26-continuation-557a12f3bcd7/cell01-family-p3-preparation-v2.tar.xz')
MEMBER = 'tools/p26/cell01-family-p3-join-20261126/cell01-family-p3-preparation-v2.tar.xz'
PIN = (664292, '3f2112c82a71ee05b816b9a9b13d33991957b94896ef3fbcf433a3ec1a65c61b')


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def canonical(path):
    need(path.is_absolute() and '..' not in path.parts and path.resolve() == path
         and not path.is_symlink(), 'NONCANONICAL_RECEIVER_PATH')
    return path


def git(repo, arguments):
    env = os.environ.copy()
    for key in list(env):
        if key.startswith('GIT_TRACE') or key in {
            'GIT_DIR', 'GIT_COMMON_DIR', 'GIT_WORK_TREE', 'GIT_INDEX_FILE',
            'GIT_OBJECT_DIRECTORY', 'GIT_ALTERNATE_OBJECT_DIRECTORIES', 'GIT_NAMESPACE',
        }:
            env.pop(key)
    env['GIT_TERMINAL_PROMPT'] = '0'
    result = subprocess.run(['git', '--git-dir=' + str(repo), *arguments], env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=480)
    # Remote diagnostics can contain credentials from configured URL rewrites;
    # no raw command diagnostics enter stdout or receipt metadata.
    need(result.returncode == 0, 'SOURCE_FETCH_GIT_EXIT_' + str(result.returncode))
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--commit', required=True)
    args = parser.parse_args()
    commit = args.commit
    need(re.fullmatch('[0-9a-f]{40}', commit) is not None, 'EXACT_SOURCE_COMMIT_REQUIRED')
    receiver, archive = canonical(RECEIVER), canonical(ARCHIVE)
    need(not receiver.exists() and not archive.exists(), 'EXISTING_RECEIVER_REQUIRES_INSPECTION_NO_RETRY')
    need(archive.parent.is_dir() and not archive.is_relative_to(receiver)
         and not receiver.is_relative_to(archive), 'RECEIVER_OUTPUT_ROOTS_DIFFER')
    receiver.mkdir()
    repo = receiver / 'repository.git'
    git(repo, ['init', '--bare', str(repo)])
    git(repo, ['remote', 'add', 'origin', URL])
    git(repo, ['config', 'remote.origin.promisor', 'true'])
    git(repo, ['config', 'remote.origin.partialCloneFilter', 'blob:none'])
    git(repo, ['fetch', '--filter=blob:none', '--depth=1', '--no-tags', '--no-recurse-submodules',
               'origin', commit])
    need(git(repo, ['rev-parse', 'FETCH_HEAD']).decode().strip() == commit,
         'FETCHED_SOURCE_COMMIT_DIFFERS')
    entries = git(repo, ['ls-tree', '-z', '--full-tree', commit, '--', MEMBER]).rstrip(b'\0').split(b'\0')
    need(len(entries) == 1 and entries[0], 'FIXED_PACKAGE_TREE_MEMBER_MISSING')
    header, name = entries[0].decode().split('\t', 1)
    mode, kind, oid = header.split()
    need(mode == '100644' and kind == 'blob' and name == MEMBER
         and re.fullmatch('[0-9a-f]{40}', oid) is not None, 'FIXED_PACKAGE_TREE_MEMBER_DIFFERS')
    need(int(git(repo, ['cat-file', '-s', oid]).decode()) == PIN[0], 'SOURCE_PACKAGE_BLOB_SIZE_DIFFERS')
    data = git(repo, ['cat-file', 'blob', oid])
    need((len(data), hashlib.sha256(data).hexdigest()) == PIN, 'SOURCE_PACKAGE_BLOB_PIN_DIFFERS')
    with archive.open('xb') as stream:
        stream.write(data)
    need(archive.read_bytes() == data, 'SOURCE_PACKAGE_FILE_READBACK_DIFFERS')
    receipt = {'schema': 'p26_cell01_preparation_single_blob_receipt_v1',
               'status': 'PASS_EXACT_SOURCE_COMMIT_PREPARATION_BLOB',
               'repository': 'UyNewNas/goldbach-formalization', 'source_commit': commit,
               'member': MEMBER, 'git_blob': oid,
               'archive': {'path': str(archive), 'bytes': PIN[0], 'sha256': PIN[1]},
               'archive_extracted': False, 'adapter_executed': False,
               'existing_provider_written': False, 'Lean_commands': 0, 'new_proof_credit': 0}
    with (receiver / 'RECEIVED.json').open('x') as stream:
        json.dump(receipt, stream, sort_keys=True, indent=2)
        stream.write('\n')
    print(json.dumps(receipt, sort_keys=True), flush=True)


if __name__ == '__main__':
    try:
        main()
    except RuntimeError as error:
        print(json.dumps({'status': 'STOPPED_INSPECT_BEFORE_RECOVERY', 'reason': str(error)}), flush=True)
        sys.exit(1)
    except Exception as error:
        print(json.dumps({'status': 'STOPPED_INSPECT_BEFORE_RECOVERY',
                          'reason': type(error).__name__}), flush=True)
        sys.exit(1)
PY_P26_P3_PREPARATION_V2_RECEIVE
