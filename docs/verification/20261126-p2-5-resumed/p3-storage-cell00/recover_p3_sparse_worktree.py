#!/usr/bin/env python3
"""Preserve P3 Cell00 history while omitting unrelated published working copies.

Only ordinary Git-identical files in docs/evidence/owned-frontiers/ are eligible.
This resource adapter never invokes Lean, advances HEAD, fetches, deletes caches,
or grants proof acceptance. Without --apply it writes a preflight report only.
All evidence is written to a fresh directory outside every registered worktree.
The original 1 GiB gate and both 16 MiB reserves remain unchanged.
"""
from collections import deque
from pathlib import Path
import argparse
import datetime
import gzip
import hashlib
import json
import os
import posixpath
import re
import shutil
import stat
import subprocess
import sys
import traceback
import types

ROOT = Path('/workspace/p25-q96-20261125')
COMMON = Path('/workspace/goldbach-p3/.git')
PRIVATE = COMMON / 'worktrees/p25-q96-20261125'
PUBLICATION = 'be20f0b050bb787ecb98f9afdd9b6a386706f45a'
TREE = 'a8ea84a6d46d9567aa3e0e7cbfe3016c6ab18acc'
ADAPTED_FROM = 'docs/verification/20261126-p2-5-resumed/p2-storage-round4-v3/recover_p2_sparse_worktree_round4_v3.py'
ADAPTED_FROM_SHA = '23260e963c3cb4c28e8895e6a2c462afd7fc795e848d5271df2ef83b098eb04e'
FAILED004 = ROOT / '.lake/diagnostic/p25-cell00-five-consumers-attempt004/RESULT.json'
FAILED004_SHA = '2c8f7b252d2e42f8ac09a6be391401258b0ed8fda1da57dd50cc7269f50b193a'
FAILED005 = ROOT / '.lake/diagnostic/p25-cell00-five-consumers-attempt005/RESULT.json'
FAILED005_SHA = 'bc26ddfa2b6a06ce4935430f6bedaf2419c7a1033723c98efe499f24116fdf88'
FROZEN_INPUTS_SHA = '0dbe082539a483d002c6d690f93647d14bf51f19c5f6d1e502e2e3cb7cbecd8d'
SOURCE_GRAPH_SHA = '485626190fc67de290b64316d71209dbf6da73a76a6ef7fe1b13dd80fc9a1f24'
REQUIRED_COUNT = 45
REQUIRED_SHA = '2a873136ea8a70067bbbb1f086ad1cebf742b941a9c72e42790df32112ed3b7c'
V6_PUBLICATION = '4653b261828f127ba0b5082eaf1106a3fea09d46'
V6_RUNNER = 'docs/verification/20261126-p2-5-resumed/run_cell00_four_consumers_v6.py'
V6_RUNNER_SHA = '064fa8414660f7036b51bf6bf336f1aef168913dca5722cd4050b9d005174f7a'
EXECUTED_V6 = Path('/workspace/p25-four-consumers-v6-20261126.py')
V6_OUT = ROOT / '.lake/diagnostic/p25-cell00-four-consumers-attempt006'
INPUT_MANIFEST = 'docs/verification/20261125-p2-5-saving16/Q96_EXISTING_INPUTS_AND_SOURCES.json'
INPUT_MANIFEST_SHA = '79404a0f8ed17c2d49fd377363a5169936628ff88e8e7fdd6d5165c8c6a917e0'
CAPACITY_SNAPSHOT_SHA = '9876a9a961d666e27118398195985e773d41e0139df672fcdf8434f773129c3b'
MIN_FREE = 1073741824
WRITE_BUFFER = 16 * 1024 * 1024
NEXT_PREPARATION_RESERVE = 16 * 1024 * 1024
COMPRESSED_DIAGNOSTIC_REPORTS = ('PROTECTED_PATHS.json', 'PATH_RESOLUTIONS_BEFORE.json')
BASE_CANDIDATE_PREFIXES = ('docs/evidence/owned-frontiers/',)
ENV = dict(os.environ, GIT_OPTIONAL_LOCKS='0', GIT_NO_LAZY_FETCH='1')
GIT = ['git', '-c', 'gc.auto=0', '-c', 'maintenance.auto=false', '-c', 'core.fsmonitor=false']


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest_bytes(raw):
    return hashlib.sha256(raw).hexdigest()


def canonical(value):
    return digest_bytes(json.dumps(value, sort_keys=True, separators=(',', ':')).encode())


def sha(path):
    before = path.stat()
    with path.open('rb') as stream:
        result = hashlib.file_digest(stream, 'sha256').hexdigest()
    after = path.stat()
    require((before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns) ==
            (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns),
            'File changed while hashing: ' + str(path))
    return result


def git(args, cwd=ROOT, data=None, allowed=(0,)):
    result = subprocess.run(GIT + list(args), cwd=cwd, env=ENV, input=data,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60)
    require(result.returncode in allowed, 'Git failed: ' + repr(args) + ': ' + os.fsdecode(result.stderr))
    return result.stdout


def text(args, cwd=ROOT):
    return os.fsdecode(git(args, cwd)).strip()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def write_compressed_diagnostic(path, value):
    require(path.name in COMPRESSED_DIAGNOSTIC_REPORTS, 'Only the two reviewed diagnostic reports may be compressed')
    raw = (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()
    compressed = gzip.compress(raw, mtime=0)
    require(gzip.decompress(compressed) == raw, 'Diagnostic compression did not preserve the exact JSON bytes')
    output = path.with_name(path.name + '.gz')
    output.write_bytes(compressed)
    return {'compression': 'gzip', 'filename': output.name, 'bytes': len(compressed),
            'sha256': digest_bytes(compressed), 'uncompressed_filename': path.name,
            'uncompressed_bytes': len(raw), 'uncompressed_sha256': digest_bytes(raw)}


def under(path, parent):
    return path == parent or parent in path.parents


def fs_resolution(path):
    """Record every link traversed, including links whose final target is outside."""
    require(path.is_absolute(), 'Expected an absolute path: ' + str(path))
    pending, current, links = deque(path.parts[1:]), Path('/'), []
    while pending:
        part = pending.popleft()
        if part in ('', '.'):
            continue
        if part == '..':
            current = current.parent
            continue
        candidate = current / part
        if candidate.is_symlink():
            require(len(links) < 64, 'Excessive or cyclic symlinks: ' + str(path))
            target = os.readlink(candidate)
            links.append({'path': str(candidate), 'target': target})
            target_path = Path(target)
            if target_path.is_absolute():
                current = Path('/')
                parts = target_path.parts[1:]
            else:
                parts = target_path.parts
            pending.extendleft(reversed(parts))
        else:
            current = candidate
    require(current == path.resolve(strict=False), 'Inconsistent realpath: ' + str(path))
    return current, links


def entry(path):
    info = path.lstat()
    result = {'mode': stat.S_IMODE(info.st_mode)}
    if stat.S_ISLNK(info.st_mode):
        resolved, links = fs_resolution(path)
        result.update(kind='symlink', target=os.readlink(path), resolved=str(resolved), links=links)
    elif stat.S_ISREG(info.st_mode):
        result.update(kind='file', bytes=info.st_size, sha256=sha(path))
    elif stat.S_ISDIR(info.st_mode):
        result.update(kind='directory')
    else:
        raise RuntimeError('Unsupported special file: ' + str(path))
    return result


def inventory(directory):
    require(directory.is_dir() and not directory.is_symlink(), 'Expected a physical directory: ' + str(directory))
    found = {'.': entry(directory)}
    for base, dirs, files in os.walk(directory, followlinks=False):
        for name in sorted(dirs + files):
            path = Path(base) / name
            found[str(path.relative_to(directory))] = entry(path)
    return found


def untracked_inventory():
    # Deliberately omit --exclude-standard: ignored files are included too.
    names = [os.fsdecode(x) for x in git(['ls-files', '--others', '-z']).split(b'\0') if x]
    found = {}
    for name in names:
        path = ROOT / name
        require(under(path, ROOT), 'Untracked path escapes worktree')
        if path.is_dir() and not path.is_symlink():
            for sub, value in inventory(path).items():
                found[str((path if sub == '.' else path / sub).relative_to(ROOT))] = value
        else:
            found[str(path.relative_to(ROOT))] = entry(path)
    return found


def config_file(path):
    if not path.exists():
        return {}
    result = {}
    for item in git(['config', '--null', '--file', str(path), '--list']).split(b'\0'):
        if item:
            key, _, value = os.fsdecode(item).partition('\n')
            result.setdefault(key.lower(), []).append(value)
    return result


def stages(cwd):
    raw = git(['ls-files', '--stage', '-z'], cwd)
    rows = {}
    for item in raw.split(b'\0'):
        if not item:
            continue
        header, path = item.split(b'\t', 1)
        mode, oid, stage = header.decode().split()
        require(stage == '0', 'Unmerged index in ' + str(cwd))
        rows[os.fsdecode(path)] = {'mode': mode, 'oid': oid}
    return raw, rows


def git_state():
    listing = git(['worktree', 'list', '--porcelain', '-z'])
    worktrees = [Path(os.fsdecode(item)[9:]) for item in listing.split(b'\0') if item.startswith(b'worktree ')]
    result = {'worktree_listing_sha256': digest_bytes(listing),
              'refs': text(['for-each-ref', '--format=%(refname) %(objectname)']), 'worktrees': {}}
    require(ROOT in worktrees, 'Target absent from worktree registration')
    for path in worktrees:
        require(path.is_dir() and path.resolve() == path, 'Missing or aliased sibling worktree: ' + str(path))
        gd = Path(text(['rev-parse', '--absolute-git-dir'], path))
        require(not (gd/'index.lock').exists() and not (gd/'config.worktree.lock').exists(), 'A worktree is locked: ' + str(path))
        raw, rows = stages(path)
        settings = {key: os.fsdecode(git(['config', '--bool', '--get', key], path, allowed=(0, 1))).strip() or None
                    for key in ('core.sparsecheckout', 'core.sparsecheckoutcone', 'index.sparse', 'core.bare')}
        result['worktrees'][str(path)] = {
            'gitdir': str(gd), 'common_gitdir': text(['rev-parse', '--path-format=absolute', '--git-common-dir'], path),
            'head': text(['rev-parse', 'HEAD'], path), 'tree': text(['rev-parse', 'HEAD^{tree}'], path),
            'head_ref': os.fsdecode(git(['symbolic-ref', '-q', 'HEAD'], path, allowed=(0, 1))).strip(),
            'staged_sha256': digest_bytes(raw), 'index_sha256': sha(gd/'index'), 'sparse_settings': settings,
            'worktree_config': config_file(gd/'config.worktree'),
            'tracked_links': {name: entry(path/name) for name, row in rows.items()
                              if row['mode'] == '120000' and (path/name).is_symlink()
                              and (path != ROOT or not name.startswith('docs/source-only/'))},
        }
    return result


def published_resolution(path, rows):
    current, chain = path, []
    while True:
        require(current in rows and len(chain) < 32, 'Unresolved/cyclic published input: ' + path)
        row = rows[current]
        if row['mode'] != '120000':
            require(row['mode'] in ('100644', '100755'), 'Unexpected published input mode')
            return current, row['oid'], chain
        raw = git(['cat-file', 'blob', row['oid']])
        target = raw.decode()
        require(target and not target.startswith('/') and '\x00' not in target and '\n' not in target,
                'Unsafe published symlink: ' + current)
        require((ROOT/current).is_symlink() and os.readlink(ROOT/current) == target, 'Worktree symlink differs: ' + current)
        following = posixpath.normpath(posixpath.join(posixpath.dirname(current), target))
        require(following != '..' and not following.startswith('../'), 'Published link escapes repository')
        chain.append({'link_path': current, 'target': target, 'resolved_path': following})
        current = following


def json_paths(value):
    if isinstance(value, dict):
        for key, item in value.items():
            yield from json_paths(key)
            yield from json_paths(item)
    elif isinstance(value, list):
        for item in value:
            yield from json_paths(item)
    elif isinstance(value, str) and '\n' not in value and '\x00' not in value:
        if value.startswith('/'):
            yield Path(value)
        else:
            relative = Path(value)
            if relative.parts and relative.parts[0] in (
                    '.lake', 'ImbalancedChen', 'docs', 'verification', 'proof-continuation-data'):
                yield ROOT / relative


def validate_consumer_history(previous, disk_failure, helpers):
    """Reuse the published v6 predicates; neither failed aggregate is accepted."""
    require(helpers.ROOT == ROOT and helpers.FAILED_PARSE == FAILED005.parent and
            helpers.FAILED_CONSUMER == FAILED004.parent, 'Published receipt helper roots differ')
    helpers.validate_failed_consumer(disk_failure)
    helpers.validate_failed_parse(previous, disk_failure)
    frozen = previous['frozen_inputs']
    require(len(frozen) == 16646 and canonical(frozen) == FROZEN_INPUTS_SHA and
            all(isinstance(path, str) and Path(path).is_absolute() and
                isinstance(expected, str) and re.fullmatch('[0-9a-f]{64}', expected)
                for path, expected in frozen.items()), 'The exact 16646 frozen input hashes changed')
    require(len(disk_failure['frozen_inputs']) == 16584 and
            all(frozen.get(path) == expected for path, expected in disk_failure['frozen_inputs'].items()),
            'The failed004 frozen history is no longer an unchanged subset')
    graph = previous['source_graph']
    require(len(graph) == 45 and canonical(graph) == SOURCE_GRAPH_SHA and
            all(frozen.get(str(ROOT / row['path'])) == row['source_sha256'] for row in graph.values()),
            'The current 45-module source graph differs from actual005')
    return {'actual004_result_sha256': FAILED004_SHA, 'actual005_result_sha256': FAILED005_SHA,
            'aggregate_accepted': False, 'frozen_input_count': len(frozen),
            'frozen_inputs_sha256': canonical(frozen), 'source_graph_count': len(graph),
            'source_graph_sha256': canonical(graph), 'accepted_dependency_count': 40,
            'accepted_decoded_owned_count': previous['modules'][helpers.DECODED]['owned_count'],
            'v6_output_absent_required': True, 'new_formal_credit': False}


def history_files(previous, disk_failure):
    """Bind every prior frozen file plus the actual failure evidence and v6 code."""
    files = dict(previous['frozen_inputs'])
    pending = [previous, disk_failure]
    while pending:
        value = pending.pop()
        if isinstance(value, dict):
            for path_key, hash_key, size_key in [('path', 'sha256', 'bytes'), ('log', 'log_sha256', 'log_bytes')]:
                if isinstance(value.get(path_key), str) and isinstance(value.get(hash_key), str) and size_key in value:
                    path, expected = value[path_key], value[hash_key]
                    require(Path(path).is_absolute() and re.fullmatch('[0-9a-f]{64}', expected) and
                            type(value[size_key]) is int and value[size_key] >= 0, 'Malformed historical artifact identity')
                    require(path not in files or files[path] == expected, 'A historical artifact has conflicting hashes: ' + path)
                    files[path] = expected
            pending.extend(value.values())
        elif isinstance(value, list):
            pending.extend(value)
    for path, expected in {**disk_failure['frozen_inputs'], str(FAILED004): FAILED004_SHA,
                           str(FAILED005): FAILED005_SHA, str(EXECUTED_V6): V6_RUNNER_SHA}.items():
        require(path not in files or files[path] == expected, 'A required historical file has conflicting hashes: ' + path)
        files[path] = expected
    require(len(files) == 16649, 'Actual005 history plus new result/exception/v6 runner file count differs')
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('publication_commit')
    parser.add_argument('--runner-sha256', required=True)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    require(sys.flags.optimize == 0, 'Do not run Python with -O')
    require(args.publication_commit == PUBLICATION and re.fullmatch('[0-9a-f]{64}', args.runner_sha256), 'Exact pins required')
    require(sha(Path(__file__)) == args.runner_sha256, 'Storage runner differs from independent review pin')
    require(args.output.parent == Path('/workspace') and args.output.name.startswith('p25-p3-storage-cell00-20261126-')
            and not os.path.lexists(args.output), 'Use a fresh, git-external evidence directory directly under /workspace')
    require(ROOT.resolve() == ROOT and PRIVATE.resolve() == PRIVATE and COMMON.resolve() == COMMON, 'Unexpected root/gitdir aliases')
    require(not any(os.environ.get(k) for k in ('GIT_DIR', 'GIT_WORK_TREE', 'GIT_INDEX_FILE', 'GIT_COMMON_DIR',
                                               'GIT_CONFIG_COUNT', 'GIT_CONFIG_PARAMETERS')), 'Unexpected Git environment overrides')
    require(text(['--version']).startswith('git version 2.56.'), 'This recovery was reviewed for Git 2.56')
    require(text(['rev-parse', '--show-toplevel']) == str(ROOT)
            and text(['rev-parse', '--absolute-git-dir']) == str(PRIVATE)
            and text(['rev-parse', '--path-format=absolute', '--git-common-dir']) == str(COMMON), 'Wrong dedicated worktree')
    require(text(['rev-parse', 'HEAD']) == PUBLICATION and text(['rev-parse', 'HEAD^{tree}']) == TREE, 'Publication changed')
    require(not text(['status', '--porcelain', '--untracked-files=no']), 'Tracked worktree is not clean')
    require(all(item[:2] == b'H ' for item in git(['ls-files', '-v', '-z']).split(b'\0') if item),
            'Existing skip-worktree/assume-unchanged flags require separate review')
    require(not (COMMON/'config.lock').exists() and not (PRIVATE/'info/sparse-checkout.lock').exists(), 'Git metadata is locked')
    registered = git(['worktree', 'list', '--porcelain', '-z'])
    require(all(not under(args.output, Path(os.fsdecode(item)[9:])) for item in registered.split(b'\0')
                if item.startswith(b'worktree ')), 'Evidence output must be outside every registered worktree')
    sys.dont_write_bytecode = True
    args.output.mkdir()
    state = {'schema': 'p25-p3-cell00-guarded-sparse-storage-recovery-v1', 'root': str(ROOT), 'source_commit': PUBLICATION,
             'runner_sha256': args.runner_sha256, 'apply_requested': args.apply, 'mutation_started': False,
             'storage_recovery_verified': False, 'compiled': False, 'accepted': False, 'finite_guard_credit': False,
             'P2_5_proved': False, 'Q96_proved': False, 'minimum_free_bytes': MIN_FREE,
             'v6_publication': V6_PUBLICATION, 'adapted_from_sha256': ADAPTED_FROM_SHA,
             'next_preparation_reserve_bytes': NEXT_PREPARATION_RESERVE,
             'selection_free_target_bytes': MIN_FREE + WRITE_BUFFER + NEXT_PREPARATION_RESERVE,
             'compressed_diagnostic_reports': {},
             'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        require(not os.path.lexists(V6_OUT), 'The blocked v6 output must still be absent')
        require(sha(FAILED004) == FAILED004_SHA and sha(FAILED005) == FAILED005_SHA,
                'Exact failed004/005 result bytes differ')
        disk_failure = json.loads(FAILED004.read_text())
        previous = json.loads(FAILED005.read_text())
        require(EXECUTED_V6.is_file() and not EXECUTED_V6.is_symlink() and
                EXECUTED_V6.stat().st_size == 127860 and sha(EXECUTED_V6) == V6_RUNNER_SHA,
                'The reviewed externally delivered v6 runner changed')
        require(text(['rev-parse', V6_PUBLICATION + '^{commit}']) == V6_PUBLICATION,
                'The exact v6 publication must already exist locally; fetching is not allowed')
        git(['merge-base', '--is-ancestor', PUBLICATION, V6_PUBLICATION])
        published_v6 = git(['show', V6_PUBLICATION + ':' + V6_RUNNER])
        require(digest_bytes(published_v6) == V6_RUNNER_SHA and published_v6 == EXECUTED_V6.read_bytes(),
                'Delivered v6 code differs from its exact fetched publication')
        helpers = types.ModuleType('p25_pinned_v6_receipt_predicates')
        helpers.__file__ = str(EXECUTED_V6)
        exec(compile(published_v6, str(EXECUTED_V6), 'exec'), helpers.__dict__)
        history_summary = validate_consumer_history(previous, disk_failure, helpers)
        bound_files = history_files(previous, disk_failure)
        executed_adapter = Path(__file__).absolute()
        require(not executed_adapter.is_symlink() and executed_adapter.resolve() == executed_adapter and
                not under(executed_adapter, ROOT) and not under(executed_adapter, COMMON) and
                str(executed_adapter) not in bound_files, 'Use a fresh physical externally delivered storage adapter')
        bound_files[str(executed_adapter)] = args.runner_sha256
        required = {row['path']: row['source_sha256'] for row in previous['source_graph'].values()}
        require(len(required) == REQUIRED_COUNT and canonical(required) == REQUIRED_SHA,
                'Exact current 45-source table differs')
        raw_stages, rows = stages(ROOT)
        protected, resolutions = {}, {}

        def protect(path, reason, must_exist=False):
            path = Path(os.path.abspath(path))
            if must_exist:
                require(path.exists(), 'Missing required path: ' + str(path))
            resolved, links = fs_resolution(path)
            resolution = {'resolved': str(resolved), 'links': links}
            require(str(path) not in resolutions or resolutions[str(path)] == resolution,
                    'A protected path changed during inventory: ' + str(path))
            resolutions[str(path)] = resolution
            candidates = [path, resolved] + [Path(link['path']) for link in links]
            for candidate in candidates:
                protected.setdefault(str(candidate), set()).add(reason)

        for path, expected in sorted(bound_files.items()):
            require(sha(Path(path)) == expected, 'Frozen history/input/runtime file differs: ' + path)
            protect(Path(path), 'actual005 frozen input or preserved history artifact', True)
        links = {}
        for path, expected in sorted(required.items()):
            require(sha(ROOT/path) == expected, 'Required current source differs: ' + path)
            resolved, oid, chain = published_resolution(path, rows)
            raw = (ROOT/path).read_bytes()
            require(hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == oid,
                    'Dereferenced published bytes differ: ' + path)
            require((ROOT/path).resolve() == (ROOT/resolved).resolve(), 'Published and physical source targets differ')
            if chain:
                links[path] = {'resolved': resolved, 'chain': chain, 'sha256': expected}
            protect(ROOT/path, 'fixed 45 current source graph', True)
        write_json(args.output/'REQUIRED_PATHS.json', required)
        write_json(args.output/'REQUIRED_SYMLINKS.json', links)
        write_json(args.output/'BOUND_HISTORY_FILES.json', bound_files)
        write_json(args.output/'PRIOR_HISTORY_IDENTITY.json', history_summary)
        for value in [previous, disk_failure]:
            for path in json_paths(value):
                protect(path, 'actual004/005 nested prior receipt/source/artifact reference')
        require(sha(ROOT/INPUT_MANIFEST) == INPUT_MANIFEST_SHA and
                bound_files.get(str(ROOT/INPUT_MANIFEST)) == INPUT_MANIFEST_SHA,
                'Original fourteen-input manifest is no longer frozen')
        raw_inputs = json.loads((ROOT/INPUT_MANIFEST).read_text())['saving16_inputs']
        require(len(raw_inputs) == 14 and sum(row['bytes'] for row in raw_inputs) == 93508187,
                'Original input set changed')
        original_inputs = {}
        for row in raw_inputs:
            path = Path(os.path.abspath(ROOT/row['install_path']))
            require(stat.S_ISREG(path.lstat().st_mode) and path.stat().st_size == row['bytes'] and sha(path) == row['sha256'],
                    'All original inputs must already be ready; no archive discovery/download is permitted')
            protect(path, 'original saving16 raw input', True)
            original_inputs[str(path)] = row['sha256']
        before_git = git_state()
        target_state = before_git['worktrees'][str(ROOT)]
        require(target_state['sparse_settings']['core.sparsecheckout'] in (None, 'false')
                and target_state['sparse_settings']['index.sparse'] in (None, 'false'), 'Existing sparse state requires separate review')
        common_config = config_file(COMMON/'config')
        require('core.worktree' not in common_config and common_config.get('core.bare', ['false']) == ['false'],
                'Shared core.worktree/bare config migration requires separate review')
        worktree_config_active = os.fsdecode(git(
            ['config', '--bool', '--get', 'extensions.worktreeConfig'], allowed=(0, 1))).strip() or None
        require(worktree_config_active == 'true', 'The observed P3 worktreeConfig setting changed')
        if worktree_config_active != 'true':
            require(all(not value['worktree_config'] for value in before_git['worktrees'].values()),
                    'Enabling worktreeConfig would activate a nonempty dormant private config; stop before mutation')
        before_lake = inventory(ROOT/'.lake')
        before_untracked = untracked_inventory()
        before_objects = inventory(COMMON/'objects')
        for base, mapping in ((ROOT/'.lake', before_lake), (ROOT, before_untracked)):
            for relative, value in mapping.items():
                protect(base if relative == '.' else base/relative, 'all prior .lake/untracked including ignored')
                if value['kind'] == 'symlink':
                    protect(Path(value['resolved']), 'preserved symlink target')
        for worktree, value in before_git['worktrees'].items():
            for relative in value['tracked_links']:
                protect(Path(worktree)/relative, 'existing tracked worktree symlink')
        for relative, row in rows.items():
            if row['mode'] == '120000':
                require((ROOT/relative).is_symlink(), 'A tracked symlink is no longer materialized: ' + relative)
                protect(ROOT/relative, 'every current tracked symlink including source-only', True)
        protect(Path(__file__).absolute(), 'executed storage runner', True)
        require(all(not under(args.output, Path(path)) for path in before_git['worktrees']),
                'Evidence output must be outside every registered worktree')
        protected_names = set()
        protected_subtrees = set()
        candidate_roots = [ROOT/prefix.rstrip('/') for prefix in BASE_CANDIDATE_PREFIXES]
        for path in protected:
            candidate = Path(path)
            if not under(candidate, ROOT):
                continue
            relative = str(candidate.relative_to(ROOT))
            protected_names.add(relative)
            # A recorded directory inside one candidate area is treated as an
            # entire protected subtree. Common ancestor locators such as cwd=ROOT
            # are preserved as directories, with their actual selected files
            # separately bound by the fixed graph and receipt inventories.
            if candidate.is_dir() and any(under(candidate, area) for area in candidate_roots):
                protected_subtrees.add(relative.rstrip('/') + '/')
        for path, row in rows.items():
            # Preserve all tracked symlinks, Git attribute/ignore files, and the
            # source-only directory's immediate metadata files.
            if (row['mode'] == '120000' or Path(path).name in ('.gitattributes', '.gitignore', '.gitmodules')
                    or (path.startswith('docs/source-only/') and len(Path(path).parts) == 3)):
                protected_names.add(path)

        def is_protected(path):
            return path in protected_names or any(path.startswith(prefix) for prefix in protected_subtrees)

        def allocated_bytes(path):
            info = (ROOT/path).lstat()
            require(stat.S_ISREG(info.st_mode), 'Only ordinary tracked working files may be omitted: ' + path)
            return info.st_blocks * 512 if info.st_nlink == 1 else 0

        # Only unreferenced published owned-frontiers working copies are eligible.
        # All current graph/history inputs, symlink targets, .lake, unique files,
        # source-only packages and other evidence remain outside this candidate set.
        base_omissions = {path for path in rows
                          if path.startswith(BASE_CANDIDATE_PREFIXES) and not is_protected(path)}
        require(base_omissions, 'No unrelated tracked base candidates are available')
        excluded = set(base_omissions)
        allocated = sum(allocated_bytes(path) for path in excluded)
        free_before = shutil.disk_usage(ROOT).free
        require(free_before + allocated >= MIN_FREE + WRITE_BUFFER + NEXT_PREPARATION_RESERVE,
                'Safe published working copies cannot recover the unchanged disk gate, evidence-write buffer and next preparation reserve')
        require(not (set(required) & excluded) and all(not is_protected(path) for path in excluded),
                'A required, cached or otherwise protected file was selected for omission')

        def literal_pattern(path):
            require('\n' not in path and '\r' not in path and '\x00' not in path,
                    'Unsupported control character in a tracked path')
            return ''.join('\\' + char if char in '\\*?[] ' else char for char in path)

        # Exact file omissions keep all other paths included by default. This
        # also prevents a broad directory pattern from hiding ignored or newly
        # created unique files. Git check-rules must confirm the exact set.
        rules = ('/*\n' + ''.join('!/' + literal_pattern(path) + '\n' for path in sorted(excluded))).encode()
        rulefile = args.output/'SPARSE_RULES.txt'
        rulefile.write_bytes(rules)
        checked = git(['sparse-checkout', 'check-rules', '--no-cone', '--rules-file', str(rulefile), '-z'],
                      data=b'\0'.join(os.fsencode(p) for p in rows) + b'\0')
        included = {os.fsdecode(p) for p in checked.split(b'\0') if p}
        require(set(rows) - included == excluded, 'Git rule interpretation differs from the exact approved file set')
        require(not any(path in excluded for path in before_untracked), 'An untracked/ignored file would be excluded')
        for path in protected:
            candidate = Path(path)
            if under(candidate, ROOT):
                rel = str(candidate.relative_to(ROOT))
                require(rel not in excluded, 'A protected realpath would be excluded: ' + path)
        candidate_blob_lines = git(
            ['cat-file', '--batch-check=%(objectname) %(objecttype) %(objectsize)'],
            data=(''.join(rows[path]['oid'] + '\n' for path in sorted(excluded))).encode()).decode().splitlines()
        require(len(candidate_blob_lines) == len(excluded), 'Candidate Git blob availability inventory differs')
        candidate_blob_sizes = {}
        for path, line in zip(sorted(excluded), candidate_blob_lines):
            fields = line.split()
            require(len(fields) == 3 and fields[0] == rows[path]['oid'] and fields[1] == 'blob' and
                    fields[2].isdigit(), 'Candidate Git blob is missing or has a different identity: ' + path)
            candidate_blob_sizes[path] = int(fields[2])
        omitted = {}
        verified_allocated = 0
        for path in sorted(excluded):
            current = ROOT/path
            value = entry(current)
            require(value['kind'] == 'file', 'Only ordinary tracked copies may be omitted')
            require(value['bytes'] == candidate_blob_sizes[path], 'Working copy size differs from its extant Git blob: ' + path)
            raw = current.read_bytes()
            require(hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == rows[path]['oid'],
                    'Candidate contains non-published work: ' + path)
            info = current.lstat()
            if info.st_nlink == 1:
                verified_allocated += info.st_blocks * 512
            omitted[path] = value
        require(verified_allocated == allocated and shutil.disk_usage(ROOT).free + allocated >= MIN_FREE,
                'Candidate allocation or available storage changed during verification')
        for filename, value in [('GIT_BEFORE.json', before_git), ('COMMON_CONFIG_BEFORE.json', common_config),
                                ('LAKE_BEFORE.json', before_lake), ('UNTRACKED_BEFORE.json', before_untracked),
                                ('GIT_OBJECTS_BEFORE.json', before_objects), ('OMITTED_TRACKED_FILES.json', omitted),
                                ('PATH_RESOLUTIONS_BEFORE.json', resolutions),
                                ('PROTECTED_PATHS.json', {p: sorted(v) for p, v in sorted(protected.items())})]:
            if filename in COMPRESSED_DIAGNOSTIC_REPORTS:
                state['compressed_diagnostic_reports'][filename] = write_compressed_diagnostic(args.output/filename, value)
            else:
                write_json(args.output/filename, value)
        (args.output/'INDEX_STAGED_BEFORE.bin').write_bytes(raw_stages)
        for path, name in [(COMMON/'config', 'common-config.before'), (ROOT/'.git', 'worktree-git-pointer.before')]:
            (args.output/name).write_bytes(path.read_bytes())
        write_json(args.output/'PRIVATE_METADATA_BEFORE.json', {
            str(path): path.read_bytes().hex() if path.is_file() else None
            for path in (PRIVATE/'config.worktree', PRIVATE/'info/sparse-checkout')})
        state.update(required_path_count=REQUIRED_COUNT, required_paths_sha256=REQUIRED_SHA,
                     required_symlinks=len(links), prior_history=history_summary,
                     bound_history_file_count=len(bound_files), bound_history_files_sha256=canonical(bound_files),
                     capacity_snapshot_sha256=CAPACITY_SNAPSHOT_SHA,
                     omission_base_prefixes=list(BASE_CANDIDATE_PREFIXES), base_omission_count=len(base_omissions),
                     protected_tracked_file_count=sum(is_protected(path) for path in rows),
                     protected_directory_prefixes=sorted(protected_subtrees),
                     extra_source_omissions=[], evidence_write_buffer_bytes=WRITE_BUFFER,
                     sparse_rules_sha256=digest_bytes(rules),
                     omitted_tracked_file_count=len(excluded), conservative_reclaimable_bytes=allocated,
                     disk_free_before=free_before, lake_before_sha256=canonical(before_lake),
                     untracked_before_sha256=canonical(before_untracked),
                     git_objects_before_sha256=canonical(before_objects), status='PREFLIGHT_VERIFIED_NO_MUTATION')
        write_json(args.output/'RESULT.json', state)
        # Fresh pre-mutation checks detect newly written unique files and changed
        # proof history during the inventory. No checkout mutation occurs first.
        require(git_state() == before_git and untracked_inventory() == before_untracked
                and inventory(ROOT/'.lake') == before_lake and config_file(COMMON/'config') == common_config
                and inventory(COMMON/'objects') == before_objects
                and not os.path.lexists(V6_OUT), 'Worktree/proof state changed during preflight')
        require(all({'resolved': str(fs_resolution(Path(p))[0]), 'links': fs_resolution(Path(p))[1]} == v
                    for p, v in resolutions.items()), 'A required realpath changed before sparse set')
        require(all(sha(Path(p)) == expected for p, expected in bound_files.items()) and
                all(sha(ROOT/p) == expected for p, expected in required.items()),
                'Bound history, sources or external inputs changed before sparse set')
        require(not text(['status', '--porcelain', '--untracked-files=no']), 'Tracked state changed before sparse set')
        state['disk_free_after_evidence_before_mutation'] = shutil.disk_usage(ROOT).free
        require(state['disk_free_after_evidence_before_mutation'] + allocated >= MIN_FREE,
                'The completed preflight evidence consumed the remaining safe recovery margin')
        require(state['disk_free_after_evidence_before_mutation'] + allocated >= MIN_FREE + NEXT_PREPARATION_RESERVE,
                'The completed preflight evidence cannot retain the next preparation reserve')
        write_json(args.output/'RESULT.json', state)
        if not args.apply:
            return 0
        command = GIT + ['sparse-checkout', 'set', '--no-cone', '--no-sparse-index', '--stdin']
        state.update(mutation_started=True, mutation_command=command)
        write_json(args.output/'RESULT.json', state)
        operation = subprocess.run(command, cwd=ROOT, env=ENV, input=rules, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, timeout=120)
        (args.output/'SPARSE_SET.stdout').write_bytes(operation.stdout)
        (args.output/'SPARSE_SET.stderr').write_bytes(operation.stderr)
        require(operation.returncode == 0, 'Sparse set did not complete; preserve evidence and inspect without cleanup')
        after_git = git_state()
        require(after_git['refs'] == before_git['refs'] and after_git['worktree_listing_sha256'] == before_git['worktree_listing_sha256'],
                'References or worktree registrations changed')
        for path, value in before_git['worktrees'].items():
            after = after_git['worktrees'][path]
            if path != str(ROOT):
                require(after == value, 'A sibling worktree changed: ' + path)
            else:
                require(all(after[k] == value[k] for k in value if k not in ('index_sha256', 'sparse_settings', 'worktree_config')),
                        'Target HEAD/tree/staged entries/links changed')
                require(after['sparse_settings'] == dict(value['sparse_settings'], **{
                    'core.sparsecheckout': 'true', 'core.sparsecheckoutcone': 'false', 'index.sparse': 'false'}), 'Unexpected sparse mode')
                permitted = {'core.sparsecheckout', 'core.sparsecheckoutcone', 'index.sparse'}
                require({k:v for k,v in after['worktree_config'].items() if k not in permitted} ==
                        {k:v for k,v in value['worktree_config'].items() if k not in permitted}, 'Unexpected private config mutation')
        common_after = config_file(COMMON/'config')
        require(common_after.get('extensions.worktreeconfig') == ['true'] and
                {k:v for k,v in common_after.items() if k != 'extensions.worktreeconfig'} ==
                {k:v for k,v in common_config.items() if k != 'extensions.worktreeconfig'}, 'Unexpected shared config mutation')
        require((COMMON/'config').read_bytes() == (args.output/'common-config.before').read_bytes(),
                'The already active shared worktreeConfig file must remain byte-identical')
        require((ROOT/'.git').read_bytes() == (args.output/'worktree-git-pointer.before').read_bytes(), 'Worktree gitdir pointer changed')
        require((PRIVATE/'info/sparse-checkout').read_bytes() == rules, 'Installed sparse rules differ')
        after_lake, after_untracked, after_objects = inventory(ROOT/'.lake'), untracked_inventory(), inventory(COMMON/'objects')
        require(after_lake == before_lake and after_untracked == before_untracked, 'Original .lake or untracked state changed')
        require(after_objects == before_objects, 'Git objects/history files changed')
        require(all(not os.path.lexists(ROOT/p) for p in excluded), 'Some intended tracked omissions remain materialized')
        require(all(os.path.lexists(ROOT/p) for p in included), 'A retained tracked path is missing')
        require(all(sha(ROOT/p) == expected for p, expected in required.items()), 'Required source/gate bytes changed')
        require(all(sha(Path(p)) == expected for p, expected in original_inputs.items()), 'Original raw input changed')
        require(all(sha(Path(p)) == expected for p, expected in bound_files.items()), 'Frozen history or runtime bytes changed')
        require(all({'resolved': str(fs_resolution(Path(p))[0]), 'links': fs_resolution(Path(p))[1]} == v
                    for p, v in resolutions.items()), 'A protected realpath changed during sparse set')
        require(not os.path.lexists(V6_OUT) and not text(['status', '--porcelain', '--untracked-files=no']),
                'Blocked v6 output or clean tracked state changed')
        free_after = shutil.disk_usage(ROOT).free
        require(free_after >= MIN_FREE, 'Recovery did not reach the unchanged 1 GiB gate; no compile is authorized by this result')
        require(free_after >= MIN_FREE + NEXT_PREPARATION_RESERVE,
                'Recovery did not retain the next preparation reserve; no compile is authorized by this result')
        write_json(args.output/'GIT_AFTER.json', after_git)
        write_json(args.output/'COMMON_CONFIG_AFTER.json', common_after)
        state.update(storage_recovery_verified=True, status='RECOVERY_VERIFIED_NO_LEAN', disk_free_after=free_after,
                     observed_free_increase=free_after-free_before, lake_after_sha256=canonical(after_lake),
                     untracked_after_sha256=canonical(after_untracked), git_objects_after_sha256=canonical(after_objects),
                     bound_history_after_matches=True, ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
        write_json(args.output/'RESULT.json', state)
        return 0
    except Exception as error:
        state.update(status='STOPPED_WITHOUT_PROOF_CREDIT', error=str(error), traceback=traceback.format_exc(),
                     disk_free_now=shutil.disk_usage(ROOT).free, ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
        write_json(args.output/'RESULT.json', state)
        return 1
    finally:
        print('P25_STORAGE_RECOVERY '+json.dumps({k:state.get(k) for k in
              ('status','mutation_started','storage_recovery_verified','disk_free_before','disk_free_after','error')})
              +' evidence='+str(args.output), flush=True)


if __name__ == '__main__':
    sys.exit(main())
