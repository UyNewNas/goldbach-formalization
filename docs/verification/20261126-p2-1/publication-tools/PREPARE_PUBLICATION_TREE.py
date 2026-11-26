#!/usr/bin/env python3
"""Prepare exact local P2.1 trees and GitHub API inputs; never call a write API.

Root reviews and runs this script explicitly. It uses a private temporary index,
preserves stage payload bytes, keeps HEAD/refs and the main worktree index intact,
and records every actual Git command through the already reviewed retrieval code.
Only an explicit fetch of a missing fixed base commit can access the network.
No Lean change, compilation, verifier execution, commit, or ref update is allowed.

Upload requested binary blobs and check their returned OIDs first. Submit tree
groups in order, requiring each returned tree to equal its local expected tree.
Before any later CAS ref operation, root must check the final expected tree and
the fixed expected old commit in PUBLICATION_TREE_RESULT.json.
"""
import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import sys
import tempfile
import types

REPOSITORY = 'UyNewNas/goldbach-formalization'
REMOTE = 'https://github.com/UyNewNas/goldbach-formalization.git'
DEFAULT_BARE = Path('/dev/shm/p21-authorized-20261126/retrieve-_av1f6nl/repository.git')
RETRIEVER_SHA = '45a3281db9a41230ab516e3c18ec2777c6865a2c2705e63dd135b14f83c7c849'
HELPER_SHA = '5c0369eb49ce5aed7798d0b69e58e26d0805f7d3d3b680c480d45f9654982a4d'
SOURCE_BINDING_SHA = 'b1a40f8656b00300077f4d10702a40a347a3c59fb10c5aaec7129d0936b28b55'
SOURCE_BINDING_BYTES = 72938
ACCEPTED_COMMIT = '1de0453bee55bf1128be422787216937b8fda9c9'
ACCEPTED_TREE = 'af74f02d263c72b0bb8e003ce49d1134ac04c5d5'
BASES = {
    'evidence': ('947a5dd8fb3c32c8a2688b767f559d7ab31d46d1',
                 '14b67d3e5a4435fb02046d7d541e0d5531aff719',
                 'refs/heads/evidence/p2-1-20261126-6c7864ad'),
    'code': ('48b343279639cb3a289628d35cc23b2710eedd05',
             '4a970a2b85f35cc28bd29bc7d7fab138ee036a87',
             'refs/heads/work/p2-1-formal-proof-20261125'),
}
ALLOWED_PREFIX = 'docs/verification/20261126-p2-1/'
ALLOWED_EXACT = {
    'docs/verification/20261125-p2-1/RUNS.json',
    'docs/superpowers/plans/2026-11-25-p2-1-original-query-closure.md',
    'verification/part2/retrieve_git_archive_restored.py',
    'verification/part2/test_retrieve_git_archive_restored.py',
}
GROUP_TARGET_BYTES = 300000
HEX40 = re.compile('[0-9a-f]{40}')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(',', ':')) + '\n').encode('utf-8')


def put_json(path, value):
    raw = encoded(value)
    with path.open('xb') as target:
        target.write(raw)
    require(path.read_bytes() == raw, 'Written JSON readback differs: ' + str(path))
    return {'path': str(path), 'bytes': len(raw), 'sha256': sha(raw)}


def stable_stat(value):
    return tuple(getattr(value, key) for key in
                 ('st_dev', 'st_ino', 'st_mode', 'st_nlink', 'st_size', 'st_mtime_ns', 'st_ctime_ns'))


def load_reviewed_retriever(path):
    require(path.is_absolute() and path.resolve(strict=True) == path, 'Reviewed retriever path is redirected')
    before = path.lstat()
    require(stat.S_ISREG(before.st_mode), 'Reviewed retriever is not regular')
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(fd, 'rb') as source:
        require(stable_stat(os.fstat(source.fileno())) == stable_stat(before), 'Reviewed source changed on open')
        raw = source.read()
        require(stable_stat(os.fstat(source.fileno())) == stable_stat(before)
                and stable_stat(path.lstat()) == stable_stat(before), 'Reviewed source changed while reading')
    require(sha(raw) == RETRIEVER_SHA, 'Reviewed retriever SHA differs')
    module = types.ModuleType('p21_reviewed_retriever_for_tree_preparation')
    module.__file__ = str(path)
    exec(compile(raw, str(path), 'exec'), module.__dict__)
    return module


def stage_paths(stage):
    require(stage.is_absolute() and stage.resolve(strict=True) == stage and stage.is_dir(),
            'Stage must be an existing canonical directory')
    found = []
    for directory, dirs, names in os.walk(stage, followlinks=False):
        directory = Path(directory)
        for name in dirs:
            path = directory / name
            require(stat.S_ISDIR(path.lstat().st_mode) and path.resolve(strict=True) == path,
                    'Stage contains a redirected/non-directory entry: ' + str(path))
        for name in names:
            path = directory / name
            require(stat.S_ISREG(path.lstat().st_mode) and path.resolve(strict=True) == path,
                    'Stage contains a non-regular/redirected file: ' + str(path))
            relative = path.relative_to(stage).as_posix()
            relative.encode('utf-8', errors='strict')
            require(not any(character in relative for character in '\0\n\r\t')
                    and not any(part in ('', '.', '..', '.git') for part in Path(relative).parts),
                    'Unsafe Git path: ' + relative)
            require(relative.startswith(ALLOWED_PREFIX) or relative in ALLOWED_EXACT,
                    'Stage path is outside the exact publication allowlist: ' + relative)
            found.append(relative)
    require(found and len(found) == len(set(found)), 'Stage is empty or contains duplicate paths')
    return sorted(found)


def parse_tree(raw):
    result = {}
    for record in raw.split(b'\0'):
        if not record:
            continue
        metadata, path = record.split(b'\t', 1)
        mode, kind, oid = metadata.decode('ascii').split(' ')
        name = path.decode('utf-8', errors='strict')
        require(name not in result and HEX40.fullmatch(oid), 'Invalid/duplicate Git tree record')
        result[name] = {'mode': mode, 'type': kind, 'sha': oid}
    return result


def parse_diff(raw):
    fields = raw.split(b'\0')
    require(fields[-1] == b'', 'Raw diff lacks terminating NUL')
    fields.pop()
    require(len(fields) % 2 == 0, 'Unexpected raw diff structure')
    result = {}
    for offset in range(0, len(fields), 2):
        header = fields[offset].decode('ascii').split(' ')
        name = fields[offset + 1].decode('utf-8', errors='strict')
        require(len(header) == 5 and header[0].startswith(':') and header[4] in ('A', 'M')
                and HEX40.fullmatch(header[2]) and HEX40.fullmatch(header[3]) and name not in result,
                'Raw diff is not a unique regular addition/modification: ' + name)
        result[name] = {'old_mode': header[0][1:], 'new_mode': header[1],
                        'old_sha': header[2], 'new_sha': header[3], 'status': header[4]}
    return result


def guarded_optional_file(path, helper):
    if not os.path.lexists(path):
        return {'exists': False}
    source, before = helper.regular(path)
    with source:
        raw = source.read()
        helper.unchanged(path, source, before)
    return {'exists': True, 'bytes': len(raw), 'sha256': sha(raw), 'stamp': before}


def tree_request(base_tree, elements):
    return {'repository_full_name': REPOSITORY, 'base_tree_sha': base_tree, 'tree_elements': elements}


def group_elements(elements, base_tree):
    groups, current = [], []
    for element in elements:
        candidate = current + [element]
        if current and len(encoded(tree_request(base_tree, candidate))) > GROUP_TARGET_BYTES:
            groups.append(current)
            current = [element]
        else:
            current = candidate
    if current:
        groups.append(current)
    return groups


def prepare(args):
    stage, output, bare = args.stage, args.output, args.bare
    require(output.is_absolute() and output.parent.resolve(strict=True) == output.parent
            and not os.path.lexists(output), 'Output must be a new canonical directory')
    require(not output.is_relative_to(stage), 'Output cannot be inside the input stage')
    require(bare.is_absolute() and bare.resolve(strict=True) == bare and bare.is_dir(),
            'Bare repository must be an existing canonical directory')
    paths = stage_paths(stage)
    output.mkdir(mode=0o700)
    runtime = Path(__file__).resolve()
    repository_root = runtime.parents[2]
    retriever_path = runtime.with_name('retrieve_git_archive_restored.py')
    base_commit, base_tree, intended_ref = BASES[args.kind]
    report = {'schema': 'p21-publication-tree-preparation/v1', 'kind': args.kind,
              'status': 'PREPARING', 'stage': str(stage), 'output': str(output), 'bare': str(bare),
              'repository_full_name': REPOSITORY, 'base_commit': base_commit, 'base_tree': base_tree,
              'intended_ref': intended_ref, 'required_CAS_old_commit': base_commit,
              'accepted_source_commit': ACCEPTED_COMMIT, 'accepted_source_tree': ACCEPTED_TREE,
              'retriever_sha256': RETRIEVER_SHA, 'helper_sha256': HELPER_SHA,
              'script_sha256': sha(runtime.read_bytes()), 'compile_credit': False, 'kernel_credit': False,
              'full_p2_complete': False, 'remote_write_performed': False, 'api_calls_performed': 0,
              'ref_updates_performed': False,
              'write_tree_missing_ok_scope': 'The fixed base is a blob:none partial repository. --missing-ok preserves existing fixed-base blob references without implicit fetch; every staged blob is independently calculated in Python and actually written by hash-object -w before any index update.',
              'publication_gate': 'Upload binary blobs and verify their expected OIDs. For every tree API response require the exact corresponding local expected_tree. Require final API tree == expected_final_tree before any separate CAS ref operation against required_CAS_old_commit. This script performs no commit/ref/API write.'}
    git = helper = None
    guards_before = refs_before = None
    try:
        reviewed = load_reviewed_retriever(retriever_path)
        helper = reviewed.load_helper(repository_root / 'verification/part2/transfer_p21_evidence.py')
        binding_raw = helper.frozen_bytes(args.source_bindings, SOURCE_BINDING_SHA, SOURCE_BINDING_BYTES)
        bindings = json.loads(binding_raw)
        require(bindings['accepted_source_commit'] == ACCEPTED_COMMIT
                and bindings['accepted_source_tree'] == ACCEPTED_TREE
                and bindings['current_source_count'] == 140 and len(bindings['sources']) == 140,
                'Frozen canonical-source binding scope differs')
        canonical = {row['source']: row['accepted_git_blob'] for row in bindings['sources']}
        require(len(canonical) == 140 and all(path.startswith('ImbalancedChen/') and path.endswith('.lean')
                                             and HEX40.fullmatch(oid) for path, oid in canonical.items()),
                'Canonical source paths/OIDs differ')
        report['source_bindings'] = {'path': str(args.source_bindings), 'bytes': len(binding_raw), 'sha256': sha(binding_raw)}
        git = reviewed.AuditedGit(bare, output / 'git-audit', helper)
        index_directory = Path(tempfile.mkdtemp(prefix='private-index-', dir=output))
        index_path = index_directory / 'index'
        require(not os.path.lexists(index_path), 'Private index already exists')
        git.environment['GIT_INDEX_FILE'] = str(index_path)
        report['exclusive_temporary_GIT_INDEX_FILE'] = str(index_path)
        require(git.run(['rev-parse', '--is-bare-repository']) == b'true\n', 'Repository is not bare')
        require(git.run(['rev-parse', '--absolute-git-dir']).decode().strip() == str(bare), 'Actual Git directory differs')
        require(git.run(['rev-parse', '--show-object-format']) == b'sha1\n', 'Repository object format is not sha1')
        guard_paths = [bare / 'HEAD', bare / 'index', bare / 'FETCH_HEAD', repository_root / '.git/index']
        guards_before = {str(path): guarded_optional_file(path, helper) for path in guard_paths}
        refs_before = git.run(['for-each-ref', '--format=%(refname) %(objectname)'])
        present = git.run(['cat-file', '--batch-check=%(objectname) %(objecttype)'], stdin=(base_commit + '\n').encode())
        if present == (base_commit + ' missing\n').encode():
            git.run(['fetch', '--no-auto-gc', '--no-tags', '--no-prune', '--no-prune-tags',
                     '--no-write-fetch-head', '--no-recurse-submodules', '--no-write-commit-graph',
                     '--refmap=', '--filter=blob:none', '--depth=1', REMOTE, base_commit])
            report['missing_fixed_base_explicitly_fetched'] = True
        else:
            require(present == (base_commit + ' commit\n').encode(), 'Fixed base object has unexpected kind')
            report['missing_fixed_base_explicitly_fetched'] = False
        require(git.run(['rev-parse', '--verify', base_commit + '^{tree}']) == (base_tree + '\n').encode(),
                'Fixed base tree differs')
        tree_path = git.run(['ls-tree', '-r', '-t', '-z', '--full-tree', base_tree], return_path=True)
        base_entries = parse_tree(tree_path.read_bytes())
        for path, oid in canonical.items():
            require(base_entries.get(path) == {'mode': '100644', 'type': 'blob', 'sha': oid},
                    'Base canonical source differs: ' + path)
        report['canonical_source_count'] = 140
        staged, file_rows, elements, binary_requests = {}, [], [], []
        request_directory = output / 'api-requests'
        request_directory.mkdir()
        for path in paths:
            absolute = stage / path
            source, before = helper.regular(absolute)
            with source:
                raw = source.read()
                helper.unchanged(absolute, source, before)
            staged[path] = {'bytes': len(raw), 'sha256': sha(raw), 'stamp': before}
            previous = base_entries.get(path)
            require(previous is None or previous['type'] == 'blob' and previous['mode'] in ('100644', '100755'),
                    'Stage would replace a tree, symlink or gitlink: ' + path)
            for ancestor in Path(path).parents:
                ancestor_name = ancestor.as_posix()
                if ancestor_name != '.' and ancestor_name in base_entries:
                    require(base_entries[ancestor_name]['type'] == 'tree', 'Stage would replace an ancestor file: ' + path)
            mode = previous['mode'] if previous is not None else '100644'
            oid = helper.blob_sha(raw)
            changed = previous is None or previous['sha'] != oid or previous['mode'] != mode
            require(not path.lower().endswith('.lean') or not changed,
                    'A Lean file would be added or changed: ' + path)
            actual_oid = git.run(['hash-object', '-w', '--stdin'], stdin=raw).decode('ascii').strip()
            require(actual_oid == oid, 'Git/Python raw blob digest differs: ' + path)
            row = {'path': path, 'bytes': len(raw), 'sha256': sha(raw), 'git_blob_sha': oid, 'mode': mode,
                   'status': 'added' if previous is None else 'modified' if changed else 'unchanged',
                   'base_git_blob_sha': None if previous is None else previous['sha']}
            try:
                content = raw.decode('utf-8', errors='strict')
                text = not path.endswith('.tar.xz') and '\0' not in content
            except UnicodeDecodeError:
                text = False
            row['api_representation'] = 'content_exact_utf8' if text else 'sha_after_base64_blob_upload'
            file_rows.append(row)
            if not changed:
                continue
            element = {'path': path, 'mode': mode, 'type': 'blob'}
            if text:
                require(content.encode('utf-8') == raw, 'UTF-8 round-trip changes staged bytes')
                element['content'] = content
            else:
                element['sha'] = oid
                request = {'repository_full_name': REPOSITORY, 'encoding': 'base64',
                           'content': base64.b64encode(raw).decode('ascii')}
                saved = put_json(request_directory / f'create_blob_{len(binary_requests):03d}.json', request)
                require(base64.b64decode(json.loads(Path(saved['path']).read_bytes())['content'], validate=True) == raw,
                        'Binary API request does not restore exact staged bytes')
                binary_requests.append({'stage_path': path, 'expected_blob_sha': oid, 'bytes': len(raw),
                                        'sha256': sha(raw), 'request': saved})
            elements.append(element)
        report['files_manifest'] = put_json(output / 'FILES.json', file_rows)
        report['binary_blob_requests'] = put_json(output / 'BINARY_BLOBS.json', binary_requests)
        git.run(['read-tree', base_tree])
        require(git.run(['write-tree', '--missing-ok']) == (base_tree + '\n').encode(), 'Initial private index differs from base tree')
        current_tree, group_records = base_tree, []
        by_path = {row['path']: row for row in file_rows}
        for number, group in enumerate(group_elements(elements, base_tree)):
            request = tree_request(current_tree, group)
            saved = put_json(request_directory / f'create_tree_{number:03d}.json', request)
            reread = json.loads(Path(saved['path']).read_bytes())
            for element in reread['tree_elements']:
                if 'content' in element:
                    require(sha(element['content'].encode('utf-8')) == by_path[element['path']]['sha256'],
                            'Text API request changes stage bytes')
            index_info = b''.join(f"{by_path[element['path']]['mode']} {by_path[element['path']]['git_blob_sha']}\t{element['path']}\0".encode('utf-8')
                                  for element in group)
            git.run(['update-index', '-z', '--index-info'], stdin=index_info)
            expected = git.run(['write-tree', '--missing-ok']).decode('ascii').strip()
            require(HEX40.fullmatch(expected), 'Invalid resulting tree OID')
            group_records.append({'index': number, 'base_tree_sha': current_tree, 'expected_tree': expected,
                                  'request': saved, 'paths': [element['path'] for element in group],
                                  'element_count': len(group),
                                  'single_element_exceeds_approximate_target': len(group) == 1 and saved['bytes'] > GROUP_TARGET_BYTES})
            current_tree = expected
        report['tree_group_requests'] = put_json(output / 'TREE_GROUPS.json', group_records)
        diff_raw = git.run(['diff-tree', '-r', '--raw', '--no-abbrev', '--no-commit-id', '--no-renames',
                            '--no-ext-diff', '--no-textconv', '-z', base_tree, current_tree])
        differences = parse_diff(diff_raw)
        changed_rows = {row['path']: row for row in file_rows if row['status'] != 'unchanged'}
        require(set(differences) == set(changed_rows), 'Final tree diff is not exactly the staged changed paths')
        for path, difference in differences.items():
            expected = changed_rows[path]
            require(difference['new_sha'] == expected['git_blob_sha'] and difference['new_mode'] == expected['mode']
                    and difference['status'] == ('A' if expected['status'] == 'added' else 'M')
                    and not path.lower().endswith('.lean'), 'Final diff detail differs: ' + path)
            require(difference['old_sha'] == (expected['base_git_blob_sha'] or '0' * 40), 'Final diff old blob differs')
            require(difference['old_mode'] == ('000000' if expected['status'] == 'added' else expected['mode']),
                    'Final diff old mode differs')
        final_source_rows = parse_tree(git.run(['ls-tree', '-r', '-z', '--full-tree', current_tree, '--', *sorted(canonical)]))
        require(set(final_source_rows) == set(canonical), 'Final canonical source path set differs')
        for path, oid in canonical.items():
            require(final_source_rows[path] == {'mode': '100644', 'type': 'blob', 'sha': oid},
                    'Final canonical source differs: ' + path)
        require(stage_paths(stage) == paths, 'Stage file set changed during preparation')
        for path, info in staged.items():
            source, before = helper.regular(stage / path)
            with source:
                require(before == info['stamp'], 'Stage file metadata changed: ' + path)
                raw = source.read()
                helper.unchanged(stage / path, source, before)
            require((len(raw), sha(raw)) == (info['bytes'], info['sha256']), 'Stage file bytes changed: ' + path)
        helper.frozen_bytes(args.source_bindings, SOURCE_BINDING_SHA, SOURCE_BINDING_BYTES)
        helper.frozen_bytes(retriever_path, RETRIEVER_SHA)
        helper.frozen_bytes(Path(helper.__file__), HELPER_SHA)
        helper.frozen_bytes(runtime, report['script_sha256'])
        report.update(status='PREPARED_TREE_INPUTS' if elements else 'PREPARED_NO_CHANGES',
                      expected_final_tree=current_tree, staged_file_count=len(paths), changed_file_count=len(elements),
                      binary_blob_request_count=len(binary_requests), tree_group_count=len(group_records),
                      canonical_sources_equal_accepted_in_base_and_final=True, exact_changed_paths_verified=True,
                      stage_originals_unchanged=True, diff=differences)
    except BaseException as error:
        report.update(status='FAILED', error=f'{type(error).__name__}: {error}')
    finally:
        if git is not None and helper is not None and guards_before is not None:
            try:
                guards_after = {path: guarded_optional_file(Path(path), helper) for path in guards_before}
                refs_after = git.run(['for-each-ref', '--format=%(refname) %(objectname)'])
                require(guards_after == guards_before and refs_after == refs_before,
                        'HEAD/refs/FETCH_HEAD or an original index changed during preparation')
                report.update(head_refs_and_original_indexes_unchanged=True, protected_files=guards_before,
                              refs_before_sha256=sha(refs_before), refs_after_sha256=sha(refs_after))
            except BaseException as error:
                report.update(status='FAILED', protection_error=f'{type(error).__name__}: {error}',
                              head_refs_and_original_indexes_unchanged=False)
        report['git_commands'] = [] if git is None else git.records
        report['preparation_checks_passed'] = report['status'] in ('PREPARED_TREE_INPUTS', 'PREPARED_NO_CHANGES')
        result_path = output / 'PUBLICATION_TREE_RESULT.json'
        put_json(result_path, report)
    print(json.dumps({'status': report['status'], 'result': str(result_path),
                      'expected_final_tree': report.get('expected_final_tree'), 'error': report.get('error'),
                      'protection_error': report.get('protection_error')}))
    return 0 if report['status'] in ('PREPARED_TREE_INPUTS', 'PREPARED_NO_CHANGES') else 1


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kind', required=True, choices=sorted(BASES))
    parser.add_argument('--stage', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--bare', type=Path, default=DEFAULT_BARE)
    parser.add_argument('--source-bindings', type=Path,
                        default=Path(__file__).resolve().parent / 'recovered-history/RETAINED_REVIEW_AND_SOURCE_BINDINGS.json')
    return prepare(parser.parse_args(argv))


if __name__ == '__main__':
    sys.exit(main())
