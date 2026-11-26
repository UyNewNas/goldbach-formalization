#!/usr/bin/env python3
"""Exact three-file Cell01 transport. Execute only after route review.

No Lean, provider installation, archive extraction, checkout, force push, or
existing branch update is available through this entry point.
"""
from pathlib import Path
from urllib.parse import urlsplit
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

sys.dont_write_bytecode = True
REPOSITORY = 'UyNewNas/goldbach-formalization'
BRANCH = 'work/p2-6-cell01-supplier-transport-20261126-557a12f3bcd7'
REF = 'refs/heads/' + BRANCH
PUBLICATION = Path('/workspace/p26-continuation-59264dd64286/publication.git')
CAPSULE = Path('/workspace/p26-continuation-557a12f3bcd7/supplier-capsule/missing189-objects-and14sources-v2')
P3_INCOMING = Path('/workspace/p26-cell01-supplier-transport-557a12f3bcd7')
URL = 'https://github.com/' + REPOSITORY + '.git'
PINS = {
    'MANIFEST.json': (409031, '8d001ee3a7bfbe4c2d6f7708c86b59977d3212053ba54bbe697143ed0a2064df'),
    'TRANSPORT.json': (2118, '07aee0214bc3e209c0a97eed04f6db88122d38155e751abdbd0a17ffa5d587eb'),
    'objects-and-missing-sources.tar.xz': (39794840, 'a16d07fe3489855e1c69a5c2658824b8b7fce7fc44ab527d3a88eb5e8451899b'),
}


def need(condition, code):
    if not condition:
        raise RuntimeError(code)


def canonical(path):
    path = Path(path).absolute()
    need('..' not in path.parts and not path.is_symlink() and path.resolve() == path,
         'NONCANONICAL_PATH')
    return path


def fingerprint(path):
    path = canonical(path)
    need(path.is_file(), 'MISSING_REGULAR_INPUT')
    before = path.stat()
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    after = path.stat()
    need((before.st_size, before.st_mtime_ns) == (after.st_size, after.st_mtime_ns),
         'INPUT_CHANGED_WHILE_HASHING')
    return {'bytes': after.st_size, 'sha256': h.hexdigest()}


def pinned(path, name):
    actual = fingerprint(path)
    need((actual['bytes'], actual['sha256']) == PINS[name], 'EXACT_TRANSPORT_PIN_MISMATCH')
    return actual


def write_new(path, value):
    path = canonical(path)
    with path.open('x') as stream:
        json.dump(value, stream, sort_keys=True, indent=2)
        stream.write('\n')


def git_environment():
    env = os.environ.copy()
    for key in list(env):
        if key.startswith('GIT_TRACE') or key in {
            'GIT_DIR', 'GIT_COMMON_DIR', 'GIT_WORK_TREE', 'GIT_INDEX_FILE',
            'GIT_OBJECT_DIRECTORY', 'GIT_ALTERNATE_OBJECT_DIRECTORIES', 'GIT_NAMESPACE',
        }:
            env.pop(key)
    env['GIT_TERMINAL_PROMPT'] = '0'
    env['GIT_AUTHOR_NAME'] = env['GIT_COMMITTER_NAME'] = 'P2.6 evidence transport'
    env['GIT_AUTHOR_EMAIL'] = env['GIT_COMMITTER_EMAIL'] = 'p26-evidence-transport@users.noreply.github.com'
    return env


def git(repo, arguments, *, data=None, allowed=(0,), timeout=180):
    # stdout/stderr remain private unless an explicitly safe parsed field is
    # returned by a caller. In particular remote URLs and Git diagnostics never
    # enter task output or saved reports.
    command = ['git', '--git-dir=' + str(repo), '-c', 'remote.origin.mirror=false',
               '-c', 'push.followTags=false', '-c', 'push.recurseSubmodules=no', *arguments]
    completed = subprocess.run(command, input=data, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, env=git_environment(), timeout=timeout)
    if completed.returncode not in allowed:
        diagnostic = completed.stderr.lower()
        category = next((code for token, code in (
            (b'authentication', 'AUTHENTICATION'), (b'permission denied', 'PERMISSION'),
            (b'repository not found', 'REPOSITORY_UNAVAILABLE'),
            (b'non-fast-forward', 'NON_FAST_FORWARD'), (b'rejected', 'REJECTED'),
            (b'could not read username', 'CREDENTIALS_UNAVAILABLE'),
        ) if token in diagnostic), 'COMMAND_FAILED')
        raise RuntimeError('GIT_' + category + '_EXIT_' + str(completed.returncode))
    return completed.returncode, completed.stdout


def text_git(repo, arguments, **kwargs):
    _, output = git(repo, arguments, **kwargs)
    return output.decode('utf-8').strip()


def authorized_url(raw):
    # Never include raw, parsed.username or parsed.password in an exception.
    if raw.startswith('git@github.com:'):
        path = raw[len('git@github.com:'):]
    else:
        parsed = urlsplit(raw)
        need(parsed.scheme in {'https', 'ssh'} and parsed.hostname == 'github.com'
             and parsed.port is None and not parsed.query and not parsed.fragment,
             'ORIGIN_NOT_AUTHORIZED_REPOSITORY')
        path = parsed.path.lstrip('/')
    if path.endswith('.git'):
        path = path[:-4]
    need(path.lower() == REPOSITORY.lower(), 'ORIGIN_NOT_AUTHORIZED_REPOSITORY')


def verify_origin(repo):
    for arguments in (['remote', 'get-url', '--all', 'origin'],
                      ['remote', 'get-url', '--push', '--all', 'origin']):
        urls = text_git(repo, arguments).splitlines()
        need(len(urls) == 1, 'ORIGIN_URL_COUNT_CHANGED')
        authorized_url(urls[0])


def require_absent_branch(repo):
    code, output = git(repo, ['ls-remote', '--exit-code', '--heads', 'origin', REF],
                       allowed=(0, 2))
    need(code == 2 and output == b'', 'TRANSPORT_BRANCH_ALREADY_EXISTS')


def require_remote_commit(repo, remote, commit):
    observed = text_git(repo, ['ls-remote', '--heads', remote, REF]).split()
    need(observed == [commit, REF], 'REMOTE_TRANSPORT_COMMIT_DIFFERS')


def tree_inventory(repo, commit):
    need(re.fullmatch('[0-9a-f]{40}', commit) is not None, 'INVALID_COMMIT')
    header = text_git(repo, ['cat-file', '-p', commit]).split('\n\n', 1)[0]
    need(not any(line.startswith('parent ') for line in header.splitlines()), 'TRANSPORT_COMMIT_HAS_PARENT')
    _, raw = git(repo, ['ls-tree', '-z', '--full-tree', commit])
    rows = {}
    for entry in raw.rstrip(b'\0').split(b'\0'):
        left, name = entry.decode().split('\t', 1)
        mode, kind, oid = left.split()
        need(mode == '100644' and kind == 'blob' and re.fullmatch('[0-9a-f]{40}', oid)
             and name in PINS and name not in rows, 'TREE_WHITELIST_REJECTED')
        need(int(text_git(repo, ['cat-file', '-s', oid])) == PINS[name][0], 'TREE_BLOB_SIZE_DIFFERS')
        rows[name] = oid
    need(set(rows) == set(PINS), 'TREE_WHITELIST_REJECTED')
    return rows


def verify_manifest(path):
    manifest = json.loads(Path(path).read_text())
    need(manifest['schema'] == 'p26_minimal_p3_missing189_object_capsule_v2'
         and manifest['object_count'] == 189 and manifest['source_body_count'] == 14
         and manifest['sidecar_count'] == 0 and manifest['payload_file_count'] == 203
         and manifest['compiler_or_proof_commands_executed'] is False
         and manifest['row001_files_accessed'] is False
         and manifest['receipt_or_log_bodies_included'] is False, 'MANIFEST_BOUNDARY_DIFFERS')
    modules = manifest['modules']
    need(len(modules) == len({row['module'] for row in modules}) == 189
         and all('row001' not in row['module'].lower() for row in modules),
         'MANIFEST_MODULE_SCOPE_DIFFERS')
    members = manifest['members']
    need(len(members) == len({row['member'] for row in members}) == 203
         and sum(row['kind'] == 'object' for row in members) == 189
         and sum(row['kind'] == 'source' for row in members) == 14,
         'MANIFEST_MEMBER_SCOPE_DIFFERS')


def publish_p1(here):
    repo, capsule = canonical(PUBLICATION), canonical(CAPSULE)
    need(repo.is_dir() and capsule.is_dir(), 'ORIGINAL_P1_DIRECTORIES_MISSING')
    need(text_git(repo, ['rev-parse', '--is-bare-repository']) == 'true', 'PUBLICATION_NOT_BARE')
    need(text_git(repo, ['rev-parse', '--show-object-format']) == 'sha1', 'UNEXPECTED_GIT_OBJECT_FORMAT')
    verify_origin(repo)
    require_absent_branch(repo)
    for name in ('PREPARED_COMMIT.json', 'PUBLISHED.json'):
        need(not (here / name).exists(), 'RECOVERY_REQUIRED_DO_NOT_RESUBMIT')
    paths = {name: here / name if name == 'TRANSPORT.json' else capsule / name for name in PINS}
    before = {name: pinned(path, name) for name, path in paths.items()}
    verify_manifest(paths['MANIFEST.json'])
    head_before = (repo / 'HEAD').read_bytes()
    head_ref_before = git(repo, ['rev-parse', '--verify', 'HEAD'], allowed=(0, 128))
    blobs = {name: text_git(repo, ['hash-object', '-w', '--no-filters', '--', str(path)])
             for name, path in paths.items()}
    need(all(re.fullmatch('[0-9a-f]{40}', oid) for oid in blobs.values()), 'INVALID_BLOB_ID')
    tree_input = ''.join('100644 blob ' + blobs[name] + '\t' + name + '\n' for name in sorted(blobs))
    tree = text_git(repo, ['mktree'], data=tree_input.encode())
    message = b'Transport exact Cell01 supplier bytes; zero new proof credit\n'
    commit = text_git(repo, ['commit-tree', tree], data=message)
    need(tree_inventory(repo, commit) == blobs, 'PREPARED_TREE_DIFFERS')
    need({name: pinned(path, name) for name, path in paths.items()} == before, 'INPUT_CHANGED_BEFORE_PUSH')
    prepared = {'schema': 'p26_cell01_git_transport_prepared_v1', 'repository': REPOSITORY,
                'branch': BRANCH, 'commit': commit, 'tree': tree, 'parent_count': 0,
                'files': {name: {**before[name], 'git_blob': blobs[name]} for name in sorted(blobs)},
                'new_proof_credit': 0, 'Lean_commands': 0, 'force_push': False}
    write_new(here / 'PREPARED_COMMIT.json', prepared)
    print(json.dumps({'phase': 'prepared_isolated_root_commit', 'commit': commit, 'tree': tree,
                      'files': sorted(blobs), 'new_proof_credit': 0}), flush=True)
    require_absent_branch(repo)
    git(repo, ['push', '--porcelain', '--no-follow-tags', '--recurse-submodules=no',
               'origin', commit + ':' + REF], timeout=480)
    require_remote_commit(repo, 'origin', commit)
    need((repo / 'HEAD').read_bytes() == head_before
         and git(repo, ['rev-parse', '--verify', 'HEAD'], allowed=(0, 128)) == head_ref_before,
         'EXISTING_PUBLICATION_HEAD_CHANGED')
    need({name: pinned(path, name) for name, path in paths.items()} == before, 'INPUT_CHANGED_AFTER_PUSH')
    result = {**prepared, 'status': 'PUBLISHED_EXACT_THREE_FILE_TRANSPORT',
              'remote_ref_readback_matches': True, 'existing_publication_HEAD_unchanged': True,
              'row001_files_transferred': False, 'old_receipt_or_log_bodies_transferred': False}
    write_new(here / 'PUBLISHED.json', result)
    print(json.dumps(result, sort_keys=True), flush=True)


def fetch_p3(here, commit):
    need(re.fullmatch('[0-9a-f]{40}', commit) is not None, 'INVALID_COMMIT')
    incoming = canonical(P3_INCOMING)
    need(not incoming.exists(), 'P3_TRANSPORT_DESTINATION_EXISTS_RECOVERY_REQUIRED')
    # Source package and existing provider trees are not extraction targets.
    need(not here.is_relative_to(incoming) and not incoming.is_relative_to(here), 'P3_CONTROL_OUTPUT_OVERLAP')
    incoming.mkdir()
    repo = incoming / 'repository.git'
    git(repo, ['init', '--bare', str(repo)])
    require_remote_commit(repo, URL, commit)
    git(repo, ['fetch', '--no-tags', '--depth=1', '--no-recurse-submodules', URL, commit], timeout=480)
    need(text_git(repo, ['rev-parse', 'FETCH_HEAD']) == commit, 'FETCHED_COMMIT_DIFFERS')
    blobs = tree_inventory(repo, commit)
    payload = incoming / 'payload'
    payload.mkdir()
    for name, oid in sorted(blobs.items()):
        _, data = git(repo, ['cat-file', 'blob', oid])
        need((len(data), hashlib.sha256(data).hexdigest()) == PINS[name], 'FETCHED_BLOB_PIN_MISMATCH')
        with (payload / name).open('xb') as stream:
            stream.write(data)
        pinned(payload / name, name)
    verify_manifest(payload / 'MANIFEST.json')
    need((payload / 'TRANSPORT.json').read_bytes() == (here / 'TRANSPORT.json').read_bytes(), 'TRANSPORT_METADATA_DIFFERS')
    result = {'schema': 'p26_cell01_git_transport_received_v1',
              'status': 'PASS_EXACT_THREE_FILE_TRANSPORT_RECEIPT', 'repository': REPOSITORY,
              'branch': BRANCH, 'commit': commit, 'destination': str(payload),
              'files': {name: pinned(payload / name, name) for name in sorted(PINS)},
              'archive_extracted': False, 'existing_providers_written': False,
              'Lean_commands': 0, 'new_proof_credit': 0}
    write_new(incoming / 'RECEIVED.json', result)
    print(json.dumps(result, sort_keys=True), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation', choices=['publish-p1', 'fetch-p3'])
    parser.add_argument('--commit')
    args = parser.parse_args()
    here = canonical(Path(__file__).parent)
    pinned(here / 'TRANSPORT.json', 'TRANSPORT.json')
    if args.operation == 'publish-p1':
        need(args.commit is None, 'PUBLISH_COMMIT_NOT_ACCEPTED_AS_INPUT')
        publish_p1(here)
    else:
        need(args.commit is not None, 'FETCH_REQUIRES_EXACT_COMMIT')
        fetch_p3(here, args.commit)


if __name__ == '__main__':
    try:
        main()
    except RuntimeError as error:
        print(json.dumps({'status': 'STOPPED_NO_AUTOMATIC_RETRY', 'reason': str(error)}), flush=True)
        sys.exit(1)
    except Exception as error:
        # Exception text can contain a remote URL; preserve only its class.
        print(json.dumps({'status': 'STOPPED_NO_AUTOMATIC_RETRY',
                          'reason': 'LOCAL_OPERATION_FAILED', 'exception_type': type(error).__name__}), flush=True)
        sys.exit(1)
