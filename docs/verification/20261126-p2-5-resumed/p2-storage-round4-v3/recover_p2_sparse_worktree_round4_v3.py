#!/usr/bin/env python3
"""Preserve completed P2 round4 while omitting unrelated published working copies.

This is a storage operation only. It never invokes Lean, changes the source
publication, deletes caches, or grants proof acceptance. Without --apply it
writes a bounded preflight report only. All evidence goes outside the worktree.
Version 2 losslessly compresses two diagnostic inventories and reserves space
for the next runner's existing preparation, following the failed v1 dry-run.
Version 3 also permits unreferenced published owned-frontiers working copies,
following the failed v2 capacity preflight and an exact read-only inventory.
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

ROOT = Path('/workspace/p2-saving16-20261125')
COMMON = Path('/workspace/goldbach-p2/.git')
PRIVATE = COMMON / 'worktrees/p2-saving16-20261125'
PUBLICATION = '168973571f795dbe8fb1c1bccfd7f7c54899b36a'
TREE = '218fda5cb14eaebb2d364b276ba6b8ecacbd8833'
FAILED_PUBLICATION = '6a4bfce285e1512b3ba31fb408812040b8aee368'
FAILED_TREE = 'aec06046068332e74e27d732eb946684e53eeec4'
PREVIOUS = '59e552b5459f6c0b8852e02c037c00d34a86e32f'
FOLDER = 'docs/verification/20261126-p2-5-continuation/p2-round2-incremental'
RUNNER = FOLDER + '/run_followup_round2.py'
RUNNER_SHA = 'bd3a0e94025c837897ec12d9c1350cb6f236c2902c09844517cab7a0a91b3591'
REQUIRED_SHA = '49ba0d56b1840fb7e789aafd57e0295baa8ec6f29db42755b9d7214a25d2c431'
REQUIRED_COUNT = 397
ADAPTED_FROM = 'docs/verification/20261126-p2-5-continuation/p2-storage-recovery/recover_p2_sparse_worktree.py'
ADAPTED_FROM_SHA = '634990c899cc26cf9df366c62a5555f0549e62fe62b37c7455699aa6ab675d79'
ROUND4_RUNNER = 'docs/verification/20261126-p2-5-resumed/run_p2_round4.py'
ROUND4_RUNNER_SHA = '803a84486461cf1b5f775c2b4d6af1a380826680de94648233cfa86e45d89ad3'
ROUND4_SELECTION = 'docs/source-only/20261126-p2-5-round4-repairs/SOURCE_SELECTION.json'
ROUND4_SELECTION_SHA = '196e4617434c4f11daef8f13a1b29cece718125a945805292c1783c9100ee574'
COMPLETED = ROOT / '.lake/p25-followup-repairs-attempt004'
COMPLETED_RESULT_SHA = 'bf84d4551c73db7ff634c95f797df967815d2e8c5ded65bd5f0b04a756b0c17e'
COMPLETED_SUMMARY = ROOT / '.lake/p2-private/audit/p25-round4-repairs-owned-audit.json'
ARCHIVE = 'ImbalancedChen/P2OriginalSaving16OriginalArchive.lean'
ARCHIVE_SHA = 'f51c3fdc3507d8ddbb1ea9471b667a07326abf5c3ac68a696e9b475ae9c2aaf9'
SOURCE_ONLY = ROOT / 'docs/source-only'
STATIC_KEEP = 'docs/source-only/20261124-p2-winner9-original-full87'
MIN_FREE = 1073741824
WRITE_BUFFER = 16 * 1024 * 1024
NEXT_PREPARATION_RESERVE = 16 * 1024 * 1024
COMPRESSED_DIAGNOSTIC_REPORTS = ('PROTECTED_PATHS.json', 'PATH_RESOLUTIONS_BEFORE.json')
BASE_CANDIDATE_PREFIXES = (
    'docs/source-only/',
    'proof-continuation-data/',
    'verification/proof-continuation/',
    'verification/parts/',
    'docs/evidence/owned-frontiers/',
)
EXTRA_SOURCE_PREFIX = 'ImbalancedChen/'
FAILED = ROOT / '.lake/p25-followup-repairs-attempt002'
FAILED_PINS = {
    'RUN_RESULT.json': '85b8cbef58b5db277de1770c80c907fb448fd342457feaa85911cefc1a13a507',
    'PREVIOUS_RECORDS.json': 'd985d34e7a94dd8cd955226bae7e62d86854ade812755fc533ef994fbf95538e',
    'previous-records.json.gz': 'dfaa5c15443ea6c8b0271da8841c39b38264178964dd743b19c53c39e14a17e8',
    'PRIOR_RUN_RESULT.json': 'acc0adffc72fd90625da9821a6cd482ebbf26a69fa3ba04ab98a7118ae947e97',
    'p25-unused-cache-reclamation-second-recovery.json': 'feaf028b54ee589bc605c0c04acc7c73f417b92b440b25b05058bc6c69171428',
    'p25-empty-baseline-setup.json': '6b7aaf695a39f01eb0e16d23390631c9b6f70f7d3115ee4791991e83dfd96baf',
}
ENV = dict(os.environ, GIT_OPTIONAL_LOCKS='0')
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


def validate_completed_round4(value, graph, targets):
    """Bind the observed completed round4 result without awarding new proof credit."""
    require(value['schema'] == 'p25-round4-reused-drivers-v1' and
            value['source_commit'] == PUBLICATION and value['source_tree'] == TREE and
            value['previous_commit'] == FAILED_PUBLICATION and value.get('ended_utc') and
            value['runner_sha256'] == ROUND4_RUNNER_SHA and
            value['source_selection_sha256'] == ROUND4_SELECTION_SHA and
            value['project_modules'] == 377 and value['owned_targets'] == 69 and
            value['compile_roots'] == graph['roots'] and value['accepted'] is False and
            value['finite_guard_credit'] is False and value['P2_5_proved'] is False,
            'Completed round4 identity or proof boundary differs')
    compiled, audited = value['compile_summary'], value['audit_summary']
    require(value['input_preparation_exit'] == 0 and value['compile_exit'] == value['audit_exit'] == 1 and
            compiled['roots'] == graph['roots'] and compiled['total'] == 377 and
            compiled['successful_closure'] == 330 and compiled['pending'] == [] and
            compiled['complete'] is False and compiled['budget_exhausted'] is False and
            len(compiled['failed_or_blocked']) == len(set(compiled['failed_or_blocked'])) == 47 and
            set(compiled['failed_or_blocked']) <= set(graph['modules']) and
            audited['requested'] == 69 and audited['accepted'] == 41 and audited['all_accepted'] is False and
            set(audited['modules']) == set(targets) and
            sum(row['accepted'] is True for row in audited['modules'].values()) == 41,
            'Completed round4 must preserve the actual 330 normal / 41 owned state')
    require(all(value[key] is True for key in (
        'source_after_matches', 'gate_after_matches', 'runner_after_matches', 'external_after_matches',
        'head_after_matches', 'history_after_matches', 'baseline_after_matches')),
        'Completed round4 preservation checks are incomplete')


def validate_current_records(value, graph, completed):
    """Check the current record identities, then freeze their actual bytes at preflight."""
    require(isinstance(value, dict), 'Current compilation records are not an object')
    successful = {name for name in graph['modules'] if value.get(name, {}).get('exit_code') == 0}
    require(len(successful) == 330 and successful ==
            set(graph['modules']) - set(completed['compile_summary']['failed_or_blocked']),
            "Current records do not retain exactly round4's 330 successful closure modules")
    for name in successful:
        row = value[name]
        require(row['source'] == graph['modules'][name]['source'] and
                row['source_sha256'] == graph['modules'][name]['sha256'],
                'Current successful record source differs from round4: ' + name)
    return successful


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
    require(args.output.parent == Path('/workspace') and args.output.name.startswith('p25-p2-storage-round4-20261126-')
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
    sys.dont_write_bytecode = True
    args.output.mkdir()
    state = {'schema': 'p25-round4-guarded-sparse-storage-recovery-v3', 'root': str(ROOT), 'source_commit': PUBLICATION,
             'runner_sha256': args.runner_sha256, 'apply_requested': args.apply, 'mutation_started': False,
             'storage_recovery_verified': False, 'compiled': False, 'accepted': False, 'finite_guard_credit': False,
             'P2_5_proved': False, 'minimum_free_bytes': MIN_FREE,
             'next_preparation_reserve_bytes': NEXT_PREPARATION_RESERVE,
             'selection_free_target_bytes': MIN_FREE + WRITE_BUFFER + NEXT_PREPARATION_RESERVE,
             'compressed_diagnostic_reports': {},
             'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        original = types.ModuleType('p25_pinned_round2_storage_helpers')
        original.__file__ = str(ROOT/RUNNER)
        require(sha(ROOT/RUNNER) == RUNNER_SHA, 'Original runner hash differs')
        exec(compile((ROOT/RUNNER).read_bytes(), str(ROOT/RUNNER), 'exec'), original.__dict__)
        require(original.ROOT == ROOT and original.PREVIOUS_COMMIT == PREVIOUS, 'Original runner constants changed')
        require(sha(ROOT/ADAPTED_FROM) == ADAPTED_FROM_SHA and
                sha(ROOT/ROUND4_RUNNER) == ROUND4_RUNNER_SHA and
                sha(ROOT/ROUND4_SELECTION) == ROUND4_SELECTION_SHA, 'Pinned storage/round4 controls differ')
        round4 = types.ModuleType('p25_pinned_round4_storage_graph')
        round4.__file__ = str(ROOT/ROUND4_RUNNER)
        exec(compile((ROOT/ROUND4_RUNNER).read_bytes(), str(ROOT/ROUND4_RUNNER), 'exec'), round4.__dict__)
        require(round4.ROOT == ROOT and round4.PREVIOUS == FAILED_PUBLICATION,
                'Round4 graph helper origin differs')
        base_graph = json.loads((ROOT/FOLDER/'CONTINUATION_SOURCE_CLOSURE.json').read_text())
        target_document = json.loads((ROOT/FOLDER/'CONTINUATION_AUDIT_TARGETS.json').read_text())
        round4_selection = json.loads((ROOT/ROUND4_SELECTION).read_text())
        graph, _ = round4.validated_graph(base_graph, target_document, round4_selection)
        targets = target_document['modules']
        require(json.loads((COMPLETED/'SOURCE_CLOSURE.json').read_text()) == graph and
                json.loads((COMPLETED/'AUDIT_TARGETS.json').read_text()) == target_document,
                'Completed round4 source graph or target set differs')
        require(sha(COMPLETED/'RUN_RESULT.json') == COMPLETED_RESULT_SHA,
                'Exact completed round4 result differs')
        completed_raw = (COMPLETED/'RUN_RESULT.json').read_bytes()
        completed = json.loads(completed_raw)
        validate_completed_round4(completed, graph, targets)
        require(completed['source_and_gate_pins'] == original.PINS and
                completed['changed_sources'] == round4_selection['sources'],
                'Completed round4 source/gate selection differs')
        for filename, expected in (
                ('COMPILE.log', completed['compile_log_sha256']),
                ('AUDIT.log', completed['audit_log_sha256']),
                ('EXECUTED_RUNNER.py', ROUND4_RUNNER_SHA),
                ('SOURCE_SELECTION.json', ROUND4_SELECTION_SHA)):
            require(sha(COMPLETED/filename) == expected, 'Completed round4 artifact differs: ' + filename)
        require(json.loads(COMPLETED_SUMMARY.read_text()) == completed['audit_summary'] and
                json.loads((COMPLETED/'CACHE_ORIGIN.json').read_text()) == completed['cache_origin'],
                'Completed round4 audit summary or cache origin differs')
        (args.output/'COMPLETED_ROUND4_RESULT.json').write_bytes(completed_raw)
        required = dict(original.PINS, **{RUNNER: RUNNER_SHA, ARCHIVE: ARCHIVE_SHA,
            ADAPTED_FROM: ADAPTED_FROM_SHA, ROUND4_RUNNER: ROUND4_RUNNER_SHA,
            ROUND4_SELECTION: ROUND4_SELECTION_SHA})
        required.update({row['source']: row['sha256'] for row in graph['modules'].values()})
        require(len(graph['modules']) == 377 and len(graph['roots']) == 5 and len(set(targets)) == len(targets) == 69,
                '377-module / 69-owner scope changed')
        require(len(required) == REQUIRED_COUNT and canonical(required) == REQUIRED_SHA, '397 input table differs')
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

        links = {}
        for path, expected in sorted(required.items()):
            require(sha(ROOT/path) == expected, 'Required input differs: ' + path)
            resolved, oid, chain = published_resolution(path, rows)
            raw = (ROOT/path).read_bytes()
            require(hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == oid,
                    'Dereferenced published bytes differ: ' + path)
            require((ROOT/path).resolve() == (ROOT/resolved).resolve(), 'Published and physical source targets differ')
            if chain:
                links[path] = {'resolved': resolved, 'chain': chain, 'sha256': expected}
            protect(ROOT/path, 'fixed 397 input', True)
        require(len(links) == 15 and {str(Path(value['resolved']).parents[1]) for value in links.values()
                                    if value['resolved'].startswith('docs/source-only/')} == {STATIC_KEEP},
                'The published required source-only symlink package changed')
        write_json(args.output/'REQUIRED_PATHS.json', required)
        write_json(args.output/'REQUIRED_SYMLINKS.json', links)
        require({p.name for p in FAILED.iterdir()} == set(FAILED_PINS), 'Attempt002 file set changed')
        for name, expected in FAILED_PINS.items():
            require(sha(FAILED/name) == expected, 'Failed preflight bytes changed: ' + name)
            protect(FAILED/name, 'failed attempt002', True)
        failure = json.loads((FAILED/'RUN_RESULT.json').read_text())
        require(failure['source_commit'] == FAILED_PUBLICATION and failure['source_tree'] == FAILED_TREE
                and failure['disk_free_start'] < MIN_FREE and failure['accepted'] is False
                and not any(k in failure for k in ('compile_command', 'compile_exit', 'audit_exit', 'ended_utc')),
                'Actual failed-before-Lean state differs')
        historical_records = json.loads((FAILED/'PREVIOUS_RECORDS.json').read_text())
        require(historical_records['source_commit'] == PREVIOUS and
                digest_bytes(gzip.decompress((FAILED/'previous-records.json.gz').read_bytes())) ==
                    historical_records['sha256'], 'Historical attempt002 record snapshot changed')
        records = ROOT/'.lake/p2-private/records.json'
        records_raw = records.read_bytes()
        record_values = json.loads(records_raw)
        successful_records = validate_current_records(record_values, graph, completed)
        previous = {'source_commit': PUBLICATION, 'sha256': digest_bytes(records_raw),
                    'bytes': len(records_raw), 'normal_successful': len(successful_records),
                    'owned_accepted': 41, 'owned_requested': 69,
                    'completed_round4_result_sha256': COMPLETED_RESULT_SHA}
        (args.output/'CURRENT_RECORDS.json.gz').write_bytes(gzip.compress(records_raw, mtime=0))
        write_json(args.output/'CURRENT_RECORDS_METADATA.json', previous)
        for path in json_paths(completed):
            protect(path, 'completed round4 receipt/input/artifact')
        protect(COMPLETED_SUMMARY, 'completed round4 owned summary', True)
        sys.path.insert(0, str(ROOT/'verification/part2'))
        from winner9_external_snapshot import ExternalSnapshot
        original.baseline_checks()
        external = ExternalSnapshot(original.SNAPSHOT, lean=original.LEAN, mathlib_pin=original.MATHLIB_COMMIT,
                                    project_lib=ROOT/'.lake/p2-private/lib')
        external_before = external.verify()
        require(external_before == failure['external_before'] == completed['external_before'] == completed['external_after'],
                'Qualified external environment differs from preserved round4/history')
        protect(original.SNAPSHOT, 'qualified snapshot', True)
        for path in json_paths(external.value):
            protect(path, 'external snapshot/runtime/provider')
        for path in json_paths(json.loads(records.read_text())):
            protect(path, 'preserved compilation records')
        current_audits = {}
        for name in targets:
            latest = ROOT/'.lake/p2-private/audit'/name/'latest.json'
            protect(latest, 'current owner audit receipt', True)
            require(latest.is_file(), 'Missing current owned receipt: ' + name)
            if latest.is_file():
                value = json.loads(latest.read_text())
                require(value['module'] == name and value.get('accepted') is
                        completed['audit_summary']['modules'][name]['accepted'],
                        'Current owner status differs from completed round4: ' + name)
                current_audits[name] = value
                for path in json_paths(value):
                    protect(path, 'current owner audit/replay/artifacts')
                if value.get('accepted') is True:
                    for path, expected in value['artifacts'].items():
                        require(sha(ROOT/path) == expected, 'Accepted audit artifact differs: ' + path)
        require(len(current_audits) == 69 and
                sum(value.get('accepted') is True for value in current_audits.values()) == 41,
                'Current owner receipts do not preserve the actual 41/69 round4 state')
        write_json(args.output/'CURRENT_AUDIT_RECEIPTS.json', current_audits)
        raw_inputs = json.loads((ROOT/original.OLD/'Q96_EXISTING_INPUTS_AND_SOURCES.json').read_text())['saving16_inputs']
        require(len(raw_inputs) == 14 and sum(row['bytes'] for row in raw_inputs) == 93508187, 'Original input set changed')
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
        require(worktree_config_active in (None, 'false', 'true'), 'Invalid shared worktreeConfig setting')
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
        protect(Path(__file__).absolute(), 'executed storage runner', True)
        protected_names = set()
        protected_subtrees = set()
        candidate_roots = [ROOT/prefix.rstrip('/') for prefix in BASE_CANDIDATE_PREFIXES]
        candidate_roots.append(ROOT/EXTRA_SOURCE_PREFIX.rstrip('/'))
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

        # The 397 pinned files, all existing cache/receipt references and all
        # symlink targets are exact exceptions, not entire source-only packages.
        # Only unreferenced owned-frontiers Git copies are added from docs/evidence.
        # Other docs/evidence, docs/verification, verification/part2, .lake and
        # unique untracked content remain outside the base omission area.
        base_omissions = {path for path in rows
                          if path.startswith(BASE_CANDIDATE_PREFIXES) and not is_protected(path)}
        require(base_omissions, 'No unrelated tracked base candidates are available')
        excluded = set(base_omissions)
        allocated = sum(allocated_bytes(path) for path in excluded)
        free_before = shutil.disk_usage(ROOT).free
        extra_candidates = sorted(
            ((allocated_bytes(path), path) for path, row in rows.items()
             if path.startswith(EXTRA_SOURCE_PREFIX) and path.endswith('.lean')
             and row['mode'] in ('100644', '100755') and not is_protected(path)),
            key=lambda row: (-row[0], row[1]))
        extras = []
        for size, path in extra_candidates:
            if free_before + allocated >= MIN_FREE + WRITE_BUFFER + NEXT_PREPARATION_RESERVE:
                break
            if not size:
                continue
            excluded.add(path)
            allocated += size
            extras.append({'path': path, 'conservative_allocated_bytes': size, 'git_blob_sha': rows[path]['oid']})
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
        omitted = {}
        verified_allocated = 0
        for path in sorted(excluded):
            current = ROOT/path
            value = entry(current)
            require(value['kind'] == 'file', 'Only ordinary tracked copies may be omitted')
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
        state.update(required_path_count=REQUIRED_COUNT, required_paths_sha256=REQUIRED_SHA, required_symlinks=15,
                     completed_round4_result_sha256=COMPLETED_RESULT_SHA, current_records=previous,
                     current_owned_accepted=41, current_owned_requested=69,
                     omission_base_prefixes=list(BASE_CANDIDATE_PREFIXES), base_omission_count=len(base_omissions),
                     protected_tracked_file_count=sum(is_protected(path) for path in rows),
                     protected_directory_prefixes=sorted(protected_subtrees),
                     extra_source_omissions=extras, source_only_whole_packages_retained=False,
                     evidence_write_buffer_bytes=WRITE_BUFFER, sparse_rules_sha256=digest_bytes(rules),
                     omitted_tracked_file_count=len(excluded), conservative_reclaimable_bytes=allocated,
                     disk_free_before=free_before, external_before=external_before,
                     lake_before_sha256=canonical(before_lake), untracked_before_sha256=canonical(before_untracked),
                     git_objects_before_sha256=canonical(before_objects), status='PREFLIGHT_VERIFIED_NO_MUTATION')
        write_json(args.output/'RESULT.json', state)
        # Fresh pre-mutation checks detect newly written unique files and changed
        # proof history during the inventory. No checkout mutation occurs first.
        require(git_state() == before_git and untracked_inventory() == before_untracked
                and inventory(ROOT/'.lake') == before_lake and config_file(COMMON/'config') == common_config
                and sha(records) == previous['sha256'], 'Worktree/proof state changed during preflight')
        require(all({'resolved': str(fs_resolution(Path(p))[0]), 'links': fs_resolution(Path(p))[1]} == v
                    for p, v in resolutions.items()), 'A required realpath changed before sparse set')
        require(external.verify() == external_before and all(sha(ROOT/p) == expected for p, expected in required.items()),
                'Required sources or external inputs changed before sparse set')
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
        require((ROOT/'.git').read_bytes() == (args.output/'worktree-git-pointer.before').read_bytes(), 'Worktree gitdir pointer changed')
        require((PRIVATE/'info/sparse-checkout').read_bytes() == rules, 'Installed sparse rules differ')
        after_lake, after_untracked, after_objects = inventory(ROOT/'.lake'), untracked_inventory(), inventory(COMMON/'objects')
        require(after_lake == before_lake and after_untracked == before_untracked, 'Original .lake or untracked state changed')
        require(after_objects == before_objects, 'Git objects/history files changed')
        require(all(not os.path.lexists(ROOT/p) for p in excluded), 'Some intended tracked omissions remain materialized')
        require(all(os.path.lexists(ROOT/p) for p in included), 'A retained tracked path is missing')
        require(all(sha(ROOT/p) == expected for p, expected in required.items()), 'Required source/gate bytes changed')
        require(all(sha(Path(p)) == expected for p, expected in original_inputs.items()), 'Original raw input changed')
        require(all(sha(FAILED/name) == expected for name, expected in FAILED_PINS.items()), 'Failed attempt evidence changed')
        require(all({'resolved': str(fs_resolution(Path(p))[0]), 'links': fs_resolution(Path(p))[1]} == v
                    for p, v in resolutions.items()), 'A protected realpath changed during sparse set')
        original.baseline_checks()
        require(external.verify() == external_before and not text(['status', '--porcelain', '--untracked-files=no']),
                'External environment or clean tracked state changed')
        free_after = shutil.disk_usage(ROOT).free
        require(free_after >= MIN_FREE, 'Recovery did not reach the unchanged 1 GiB gate; no compile is authorized by this result')
        require(free_after >= MIN_FREE + NEXT_PREPARATION_RESERVE,
                'Recovery did not retain the next preparation reserve; no compile is authorized by this result')
        write_json(args.output/'GIT_AFTER.json', after_git)
        write_json(args.output/'COMMON_CONFIG_AFTER.json', common_after)
        state.update(storage_recovery_verified=True, status='RECOVERY_VERIFIED_NO_LEAN', disk_free_after=free_after,
                     observed_free_increase=free_after-free_before, lake_after_sha256=canonical(after_lake),
                     untracked_after_sha256=canonical(after_untracked), git_objects_after_sha256=canonical(after_objects),
                     external_after=external_before, ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
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
