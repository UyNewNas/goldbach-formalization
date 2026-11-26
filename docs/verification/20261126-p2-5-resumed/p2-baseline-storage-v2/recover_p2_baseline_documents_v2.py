#!/usr/bin/env python3
"""Omit only restorable, unreferenced published documents in our empty baseline.

This fixed-purpose adapter reuses the pinned round4-v3 storage helpers. It never
compiles, fetches, advances HEAD, touches proof-root files, or removes caches.
Plan mode writes evidence outside all worktrees. Apply requires that exact plan.
"""
from pathlib import Path
import argparse
import datetime
import gzip
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import traceback
import types

PROOF_ROOT = Path('/workspace/p2-saving16-20261125')
PROOF_HEAD = '7926999deb30b63976739355b3076990b370e66f'
PROOF_TREE = '1c499b283fd6fa2ae83c8d66d0b2e1ea9e934099'
BASELINE = Path('/workspace/p25-analytic-baseline-8657-20261125')
BASELINE_HEAD = '8657cfffef159185f73c6a04ae4d31c846c0d0a9'
BASELINE_TREE = 'd48c5f773a7fc213e4da7897d3a4a042016a151e'
COMMON = Path('/workspace/goldbach-p2/.git')
PREFIXES = (
    'docs/source-only/',
    'proof-continuation-data/',
    'verification/proof-continuation/',
    'verification/parts/',
    'docs/evidence/owned-frontiers/',
)
V3_PATH = 'docs/verification/20261126-p2-5-resumed/p2-storage-round4-v3/recover_p2_sparse_worktree_round4_v3.py'
V3_SHA = '23260e963c3cb4c28e8895e6a2c462afd7fc795e848d5271df2ef83b098eb04e'
ROUND7_COMMIT = '1e80a5fa2fa2dbb346dbdef5760a7361a8001a46'
ROUND7_PATH = 'docs/verification/20261126-p2-5-resumed/run_p2_round7.py'
ROUND7_SHA = '7599eb65dd43cf83d9664a719216f546be3b0c7c91100a42ae30de3c7174b8a0'
PLANNED_MINIMUM_RECLAIM = 512 * 1024 * 1024
PROOF_MINIMUM_FREE = 1073741824
WRITE_BUFFER = 16 * 1024 * 1024
NEXT_PREPARATION_RESERVE = 16 * 1024 * 1024
CACHE_SUFFIXES = ('.olean', '.ilean', '.ir', '.o', '.so', '.a', '.c', '.bc', '.wasm')
DOCUMENT_SUFFIXES = {'.raw', '.gz', '.json', '.txt', '.nul'}
GIT = ['git', '-c', 'gc.auto=0', '-c', 'maintenance.auto=false',
       '-c', 'core.fsmonitor=false', '-c', 'protocol.allow=never']


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def git(args, cwd, data=None):
    env = dict(os.environ, GIT_OPTIONAL_LOCKS='0', GIT_NO_LAZY_FETCH='1')
    result = subprocess.run(GIT + list(args), cwd=cwd, env=env, input=data,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60)
    require(result.returncode == 0, 'Git failed: ' + repr(args) + ': ' + os.fsdecode(result.stderr))
    return result.stdout


def load_checked(raw, expected, path, name):
    require(digest(raw) == expected, 'Pinned helper differs: ' + str(path))
    module = types.ModuleType(name)
    module.__file__ = str(path)
    exec(compile(raw, str(path), 'exec'), module.__dict__)
    return module


def untracked(h, root):
    # Same v3 inventory policy, with the explicit baseline cwd; ignored included.
    found = {}
    for raw in git(['ls-files', '--others', '-z'], root).split(b'\0'):
        if not raw:
            continue
        path = root / os.fsdecode(raw)
        require(h.under(path, root), 'Untracked path escapes root')
        if path.is_dir() and not path.is_symlink():
            for sub, value in h.inventory(path).items():
                found[str((path if sub == '.' else path / sub).relative_to(root))] = value
        else:
            found[str(path.relative_to(root))] = h.entry(path)
    return found


def qualify_candidates(h, root, rows, protected_names, protected_subtrees):
    """Exact v3 ordinary-file/Git-byte rule, limited to five reviewed document prefixes."""
    selected = {}
    for name, row in sorted(rows.items()):
        if (not name.startswith(PREFIXES) or row['mode'] not in ('100644', '100755')
                or name in protected_names or any(name.startswith(p) for p in protected_subtrees)
                or name.lower().endswith(('.lean', *CACHE_SUFFIXES)) or '.lake' in Path(name).parts
                or Path(name).suffix not in DOCUMENT_SUFFIXES
                or Path(name).name in ('.gitattributes', '.gitignore', '.gitmodules')):
            continue
        path = root / name
        info = path.lstat()
        require(stat.S_ISREG(info.st_mode), 'Candidate is not an ordinary file: ' + name)
        if info.st_nlink != 1:
            continue  # No conservative release is attributed to shared inodes.
        value = h.entry(path)
        raw = path.read_bytes()
        require(hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == row['oid'],
                'Candidate differs from its indexed HEAD blob: ' + name)
        blob = git(['cat-file', 'blob', row['oid']], root)
        require(blob == raw, 'Locally restorable Git blob differs: ' + name)
        require(h.entry(path) == value, 'Candidate changed during verification: ' + name)
        fresh = path.lstat()
        identity = lambda s: (s.st_dev, s.st_ino, s.st_mode, s.st_size, s.st_nlink,
                              s.st_blocks, s.st_mtime_ns, s.st_ctime_ns)
        require(identity(info) == identity(fresh), 'Candidate inode changed: ' + name)
        selected[name] = dict(value, git_blob_sha1=row['oid'],
                              conservative_allocated_bytes=info.st_blocks * 512)
    return selected


def exact_rules(excluded):
    def literal(path):
        require(not any(c in path for c in ('\n', '\r', '\0')), 'Control character in tracked path')
        return ''.join('\\' + c if c in '\\*?[] ' else c for c in path)
    return ('/*\n' + ''.join('!/' + literal(path) + '\n' for path in sorted(excluded))).encode()


def apply_sparse(root, rules, output):
    command = ['sparse-checkout', 'set', '--no-cone', '--no-sparse-index', '--stdin']
    result = subprocess.run(GIT + command, cwd=root,
                            env=dict(os.environ, GIT_OPTIONAL_LOCKS='0', GIT_NO_LAZY_FETCH='1'),
                            input=rules, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
    (output / 'SPARSE_SET.stdout').write_bytes(result.stdout)
    (output / 'SPARSE_SET.stderr').write_bytes(result.stderr)
    require(result.returncode == 0, 'Sparse set failed; preserve all evidence without cleanup')


def verified_readonly_result(plan_path, plan_sha, runner_sha):
    raw = (plan_path.parent / 'RESULT.json').read_bytes()
    value = json.loads(raw)
    require(value.get('status') == 'READ_ONLY_PLAN_VERIFIED' and value.get('ended_utc')
            and value.get('apply_requested') is False and value.get('mutation_started') is False
            and value.get('runner_sha256') == runner_sha and value.get('plan_sha256') == plan_sha,
            'Prior read-only plan did not finish successfully with the reviewed runner and exact plan')
    return digest(raw)


def proof_context(h, r7):
    """Reuse the actual round7 prior-round validator and original baseline checks."""
    require(git(['rev-parse', 'HEAD'], PROOF_ROOT).decode().strip() == PROOF_HEAD
            and git(['rev-parse', 'HEAD^{tree}'], PROOF_ROOT).decode().strip() == PROOF_TREE,
            'P2 proof publication changed')
    require(not git(['status', '--porcelain', '--untracked-files=no'], PROOF_ROOT).strip(),
            'P2 proof tracked state is not clean')
    require(not os.path.lexists(PROOF_ROOT / r7.NEW_OUT), 'Round7 attempt007 is no longer unused')
    original = load_checked((PROOF_ROOT / r7.HELPER).read_bytes(), r7.HELPER_SHA,
                            PROOF_ROOT / r7.HELPER, 'baseline_storage_round2')
    require(original.ROOT == PROOF_ROOT and original.BASELINE == BASELINE
            and original.BASELINE_COMMIT == BASELINE_HEAD, 'Original proof/baseline roots differ')
    required = dict(original.PINS, **{r7.HELPER: r7.HELPER_SHA, V3_PATH: V3_SHA,
                                     h.ARCHIVE: h.ARCHIVE_SHA})
    graph = json.loads((PROOF_ROOT / r7.ROUND2 / 'CONTINUATION_SOURCE_CLOSURE.json').read_bytes())
    targets = json.loads((PROOF_ROOT / r7.ROUND2 / 'CONTINUATION_AUDIT_TARGETS.json').read_bytes())
    for number in (4, 5, 6):
        runner_path = getattr(r7, f'ROUND{number}_RUNNER')
        runner_sha = getattr(r7, f'ROUND{number}_RUNNER_SHA')
        selection_path = getattr(r7, f'ROUND{number}_SELECTION')
        selection_sha = getattr(r7, f'ROUND{number}_SELECTION_SHA')
        required.update({runner_path: runner_sha, selection_path: selection_sha})
        runner = load_checked((PROOF_ROOT / runner_path).read_bytes(), runner_sha,
                              PROOF_ROOT / runner_path, f'baseline_storage_round{number}')
        raw = (PROOF_ROOT / selection_path).read_bytes()
        require(digest(raw) == selection_sha, 'Prior selection differs')
        prior_selection = json.loads(raw)
        graph, _ = runner.validated_graph(graph, targets, prior_selection)
    sys.path.insert(0, str(PROOF_ROOT / 'verification/part2'))
    for path, expected in required.items():
        require(h.sha(PROOF_ROOT / path) == expected, 'P2 control differs: ' + path)
    from inspect_winner9_owner_native import imports
    from winner9_external_snapshot import ExternalSnapshot
    r7.verify_sources(PROOF_ROOT, graph, imports)
    required.update({row['source']: row['sha256'] for row in graph['modules'].values()})
    previous_path = PROOF_ROOT / r7.PRIOR_OUT / 'RUN_RESULT.json'
    previous_raw = previous_path.read_bytes()
    require(digest(previous_raw) == r7.PRIOR_RESULT_SHA, 'Original remote round6 receipt differs')
    previous = json.loads(previous_raw)
    r7.validate_previous_result(previous, graph['roots'], targets['modules'], prior_selection)
    require(json.loads((PROOF_ROOT / r7.PRIOR_OUT / 'SOURCE_CLOSURE.json').read_bytes()) == graph,
            'Saved round6 graph differs')
    require(json.loads((PROOF_ROOT / r7.PRIOR_OUT / 'AUDIT_TARGETS.json').read_bytes()) == targets
            and (PROOF_ROOT / r7.PRIOR_OUT / 'SOURCE_SELECTION.json').read_bytes() == raw,
            'Saved round6 target/selection provenance differs')
    require(previous['source_and_gate_pins'] == original.PINS
            and json.loads((PROOF_ROOT / r7.PRIOR_OUT / 'CACHE_ORIGIN.json').read_bytes()) == previous['cache_origin'],
            'Saved round6 gate/cache provenance differs')
    require(json.loads((PROOF_ROOT / r7.PRIOR_SUMMARY).read_bytes()) == previous['audit_summary'],
            'Round6 audit summary differs')
    for filename, key in [('COMPILE.log', 'compile_log_sha256'), ('AUDIT.log', 'audit_log_sha256'),
                          ('EXECUTED_RUNNER.py', 'runner_sha256')]:
        require(h.sha(PROOF_ROOT / r7.PRIOR_OUT / filename) == previous[key], 'Prior evidence differs: ' + filename)
    records_path = PROOF_ROOT / '.lake/p2-private/records.json'
    records = json.loads(records_path.read_bytes())
    successful = {n for n in graph['modules'] if records.get(n, {}).get('exit_code') == 0}
    require(len(successful) == 339 and successful == set(graph['modules']) -
            set(previous['compile_summary']['failed_or_blocked']), 'Current normal record scope differs')
    require(all(records[n]['source'] == graph['modules'][n]['source'] and
                records[n]['source_sha256'] == graph['modules'][n]['sha256'] for n in successful),
            'Successful record source identity differs')
    audits = {}
    for name in targets['modules']:
        path = PROOF_ROOT / '.lake/p2-private/audit' / name / 'latest.json'
        value = json.loads(path.read_bytes())
        require(value['module'] == name and value.get('accepted') is previous['audit_summary']['modules'][name]['accepted'],
                'Current owned status differs: ' + name)
        if value.get('accepted') is True:
            require(all(h.sha(PROOF_ROOT / p) == expected for p, expected in value['artifacts'].items()),
                    'Accepted owned evidence differs: ' + name)
        audits[name] = h.sha(path)
    original.baseline_checks()
    external = ExternalSnapshot(original.SNAPSHOT, lean=original.LEAN,
                                mathlib_pin=original.MATHLIB_COMMIT, project_lib=PROOF_ROOT / '.lake/p2-private/lib')
    binding = external.verify()
    require(binding == previous['external_after'], 'Qualified external context differs from round6')
    frozen = {'source_commit': PROOF_HEAD, 'source_tree': PROOF_TREE,
              'required_sources_and_controls': required, 'round6_result_sha256': digest(previous_raw),
              'records_sha256': h.sha(records_path), 'latest_audit_sha256': audits,
              'normal_successful': 339, 'owned_accepted': 45, 'owned_targets': 69,
              'external_binding': binding}
    return original, external, frozen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runner-sha256', required=True)
    parser.add_argument('--minimum-reclaim-bytes', type=int, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--apply', action='store_true')
    parser.add_argument('--plan', type=Path)
    parser.add_argument('--plan-sha256')
    args = parser.parse_args()
    require(sys.flags.optimize == 0, 'Do not run Python with -O')
    require(re.fullmatch('[0-9a-f]{64}', args.runner_sha256) is not None
            and digest(Path(__file__).read_bytes()) == args.runner_sha256, 'Reviewed runner pin differs')
    require(args.minimum_reclaim_bytes == PLANNED_MINIMUM_RECLAIM,
            'This reviewed storage plan requires exactly the recorded 512 MiB minimum reclaim target')
    require(args.apply == bool(args.plan) == bool(args.plan_sha256), 'Apply requires the exact prior read-only plan and SHA')
    require(args.output.parent == Path('/workspace')
            and args.output.name.startswith('p25-p2-baseline-storage-v2-20261126-')
            and not os.path.lexists(args.output), 'Use a fresh evidence directory directly under /workspace')
    require(not any(os.environ.get(k) for k in ('GIT_DIR', 'GIT_WORK_TREE', 'GIT_INDEX_FILE', 'GIT_COMMON_DIR',
                                               'GIT_CONFIG_COUNT', 'GIT_CONFIG_PARAMETERS')), 'Unexpected Git override')
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    os.environ['GIT_NO_LAZY_FETCH'] = '1'
    sys.dont_write_bytecode = True
    h = load_checked((PROOF_ROOT / V3_PATH).read_bytes(), V3_SHA, PROOF_ROOT / V3_PATH, 'baseline_storage_v3_helpers')
    # Harden only the reused helper's Git transport policy; no validation is removed.
    h.GIT = GIT
    require(h.ROOT == PROOF_ROOT and h.COMMON == COMMON, 'Pinned helper roots differ')
    require(git(['--version'], BASELINE).decode().startswith('git version 2.56.'), 'Expected reviewed Git 2.56')
    for path in (PROOF_ROOT, BASELINE, COMMON):
        require(path.resolve() == path, 'Unexpected root alias: ' + str(path))
    require(BASELINE.stat().st_dev == PROOF_ROOT.stat().st_dev,
            'Baseline reclamation must serve the same filesystem as the unchanged P2 proof-space gate')
    require(git(['rev-parse', '--show-toplevel'], BASELINE).decode().strip() == str(BASELINE)
            and git(['rev-parse', 'HEAD'], BASELINE).decode().strip() == BASELINE_HEAD
            and git(['rev-parse', 'HEAD^{tree}'], BASELINE).decode().strip() == BASELINE_TREE
            and git(['rev-parse', '--path-format=absolute', '--git-common-dir'], BASELINE).decode().strip() == str(COMMON),
            'Wrong isolated baseline worktree')
    require(not git(['status', '--porcelain', '--untracked-files=no'], BASELINE).strip(), 'Baseline is not clean')
    require(not (BASELINE / '.lake/build/lib/lean').exists(), 'Baseline must keep its intentionally absent build objects')
    require(all(x[:2] == b'H ' for x in git(['ls-files', '-v', '-z'], BASELINE).split(b'\0') if x),
            'Existing baseline skip-worktree/assume-unchanged flags need separate review')
    require(git(['config', '--bool', '--get', 'extensions.worktreeConfig'], BASELINE).decode().strip() == 'true',
            'Do not migrate shared Git configuration; worktreeConfig must already be enabled')
    r7_raw = git(['show', ROUND7_COMMIT + ':' + ROUND7_PATH], PROOF_ROOT)
    r7 = load_checked(r7_raw, ROUND7_SHA, ROUND7_PATH, 'baseline_storage_round7')
    git_before = h.git_state()
    require(str(BASELINE) in git_before['worktrees'], 'Baseline is not registered')
    require(all(not h.under(args.output, Path(p)) for p in git_before['worktrees']), 'Output overlaps a worktree')
    args.output.mkdir()
    state = {'schema': 'p25-baseline-published-documents-storage-v2', 'apply_requested': args.apply,
             'runner_sha256': args.runner_sha256, 'helper_sha256': V3_SHA,
             'mutation_started': False, 'storage_recovery_verified': False, 'compiled': False,
             'accepted': False, 'P2_5_proved': False, 'prefixes': list(PREFIXES),
             'minimum_reclaim_bytes': args.minimum_reclaim_bytes, 'proof_minimum_free_bytes': PROOF_MINIMUM_FREE,
             'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    save = lambda: (args.output / 'RESULT.json').write_bytes(encoded(state))
    save()
    try:
        original, external, proof_before = proof_context(h, r7)
        require(h.git_state() == git_before, 'Git state changed during proof preflight')
        private = Path(git_before['worktrees'][str(BASELINE)]['gitdir'])
        require(private.parent == COMMON / 'worktrees' and private.resolve() == private, 'Unexpected baseline gitdir')
        require(not (COMMON / 'config.lock').exists() and not (private / 'info/sparse-checkout.lock').exists(),
                'Git metadata is locked')
        before_settings = git_before['worktrees'][str(BASELINE)]['sparse_settings']
        require(before_settings['core.sparsecheckout'] in (None, 'false')
                and before_settings['index.sparse'] in (None, 'false'), 'Baseline is already sparse')
        common_before = h.config_file(COMMON / 'config')
        common_config_sha = h.sha(COMMON / 'config')
        staged, rows = h.stages(BASELINE)
        tree_rows = {}
        for item in git(['ls-tree', '-r', '-z', BASELINE_HEAD], BASELINE).split(b'\0'):
            if item:
                info, name = item.split(b'\t', 1)
                mode, kind, oid = info.decode().split()
                require(kind == 'blob', 'Unexpected baseline Git entry kind')
                tree_rows[os.fsdecode(name)] = {'mode': mode, 'oid': oid}
        require(rows == tree_rows, 'Baseline staged entries differ from the fixed HEAD tree')
        baseline_before = h.inventory(BASELINE)
        proof_files_before = h.inventory(PROOF_ROOT)
        baseline_untracked = untracked(h, BASELINE)
        objects_before = h.inventory(COMMON / 'objects')
        protected_names, protected_subtrees, resolutions = set(), set(), {}

        def protect(path):
            path = Path(os.path.abspath(path))
            resolved, links = h.fs_resolution(path)
            resolutions[str(path)] = {'resolved': str(resolved), 'links': links}
            for candidate in [path, resolved, *[Path(x['path']) for x in links]]:
                if not h.under(candidate, BASELINE):
                    continue
                relative = str(candidate.relative_to(BASELINE))
                protected_names.add(relative)
                if candidate != BASELINE and candidate.is_dir():
                    protected_subtrees.add(relative.rstrip('/') + '/')

        for name, value in baseline_before.items():
            if value['kind'] == 'symlink' or name.lower().endswith('.lean') or name == '.lake' or name.startswith('.lake/'):
                protect(BASELINE / name)
        for name in baseline_untracked:
            protect(BASELINE / name)
        for path, value in proof_files_before.items():
            if value['kind'] == 'symlink':
                protect(PROOF_ROOT / path)
        for worktree, value in git_before['worktrees'].items():
            for name in value['tracked_links']:
                protect(Path(worktree) / name)
            if Path(worktree) not in (BASELINE, PROOF_ROOT):
                # Metadata only: protect even ignored/untracked sibling links;
                # no other worktree's regular file content is read or selected.
                for directory, dirs, files in os.walk(
                        worktree, followlinks=False,
                        onerror=lambda error: require(False, 'Cannot inspect sibling symlinks: ' + str(error))):
                    for name in dirs + files:
                        path = Path(directory) / name
                        if stat.S_ISLNK(path.lstat().st_mode):
                            protect(path)
        # v3.json_paths is intentionally still bound to PROOF_ROOT, not BASELINE.
        for directory, dirs, files in os.walk(PROOF_ROOT / '.lake', followlinks=False):
            dirs[:] = [d for d in dirs if not (Path(directory) / d).is_symlink()]
            for name in files:
                path = Path(directory) / name
                if name.endswith('.json') or name.endswith('.json.gz'):
                    raw = path.read_bytes()
                    value = json.loads(gzip.decompress(raw) if name.endswith('.gz') else raw)
                    for reference in h.json_paths(value):
                        protect(reference)
        for reference in h.json_paths(external.value):
            protect(reference)
        candidates = qualify_candidates(h, BASELINE, rows, protected_names, protected_subtrees)
        allocated = sum(r['conservative_allocated_bytes'] for r in candidates.values())
        rules = exact_rules(candidates)
        rulefile = args.output / 'SPARSE_RULES.txt'
        rulefile.write_bytes(rules)
        checked = git(['sparse-checkout', 'check-rules', '--no-cone', '--rules-file', str(rulefile), '-z'],
                      BASELINE, b'\0'.join(os.fsencode(n) for n in rows) + b'\0')
        included = {os.fsdecode(n) for n in checked.split(b'\0') if n}
        require(set(rows) - included == set(candidates), 'Git rules differ from exact selected files')
        require(not set(candidates) & set(baseline_untracked), 'Untracked/ignored path selected')
        binding = {'baseline_commit': BASELINE_HEAD, 'baseline_tree': BASELINE_TREE,
                   'proof_context_sha256': h.canonical(proof_before),
                   'proof_root_inventory_sha256': h.canonical(proof_files_before),
                   'baseline_inventory_sha256': h.canonical(baseline_before),
                   'baseline_untracked_sha256': h.canonical(baseline_untracked),
                   'git_state_sha256': h.canonical(git_before), 'git_objects_sha256': h.canonical(objects_before),
                   'common_config_sha256': common_config_sha, 'rules_sha256': digest(rules),
                   'candidate_set_sha256': h.canonical(candidates),
                   'protected_resolutions_sha256': h.canonical(resolutions)}
        plan = {'schema': 'p25-baseline-published-documents-plan-v2', 'runner_sha256': args.runner_sha256,
                'helper_sha256': V3_SHA, 'prefixes': list(PREFIXES), 'minimum_reclaim_bytes': args.minimum_reclaim_bytes,
                'document_suffixes': sorted(DOCUMENT_SUFFIXES),
                'proof_minimum_free_bytes': PROOF_MINIMUM_FREE, 'evidence_write_buffer_bytes': WRITE_BUFFER,
                'next_preparation_reserve_bytes': NEXT_PREPARATION_RESERVE,
                'conservative_reclaimable_bytes': allocated, 'candidate_count': len(candidates),
                'binding': binding, 'candidates': candidates,
                'capacity_sufficient': allocated >= args.minimum_reclaim_bytes,
                'compiled': False, 'accepted': False, 'P2_5_proved': False}
        (args.output / 'PLAN.json').write_bytes(encoded(plan))
        state.update(conservative_reclaimable_bytes=allocated, candidate_count=len(candidates),
                     disk_free_before=shutil.disk_usage(BASELINE).free,
                     plan_sha256=digest(encoded(plan)), status='READ_ONLY_PLAN_PREPARED')
        save()
        require(allocated >= args.minimum_reclaim_bytes, 'Reviewed-prefix capacity is below 512 MiB; do not expand scope')
        require(state['disk_free_before'] + allocated >= PROOF_MINIMUM_FREE + WRITE_BUFFER + NEXT_PREPARATION_RESERVE,
                'Insufficient space for the unchanged proof gate and evidence/preparation reserves')
        for filename, value in [('PROOF_ROOT_BEFORE', proof_files_before), ('BASELINE_BEFORE', baseline_before),
                                ('GIT_OBJECTS_BEFORE', objects_before), ('PROTECTED_RESOLUTIONS', resolutions),
                                ('PROOF_CONTEXT_BEFORE', proof_before)]:
            raw = encoded(value)
            packed = gzip.compress(raw, mtime=0)
            require(gzip.decompress(packed) == raw, 'Inventory compression changed bytes')
            (args.output / (filename + '.json.gz')).write_bytes(packed)
        (args.output / 'GIT_BEFORE.json').write_bytes(encoded(git_before))
        (args.output / 'BASELINE_INDEX_STAGED_BEFORE.bin').write_bytes(staged)
        if args.apply:
            raw = args.plan.read_bytes()
            require(digest(raw) == args.plan_sha256, 'Approved read-only plan SHA differs')
            require(json.loads(raw) == plan, 'Current inputs/selection differ from the approved read-only plan')
            state['prior_readonly_result_sha256'] = verified_readonly_result(
                args.plan, args.plan_sha256, args.runner_sha256)
        require(h.git_state() == git_before and h.inventory(PROOF_ROOT) == proof_files_before
                and h.inventory(BASELINE) == baseline_before and h.inventory(COMMON / 'objects') == objects_before
                and untracked(h, BASELINE) == baseline_untracked, 'Frozen inputs changed before mutation')
        require(h.config_file(COMMON / 'config') == common_before and h.sha(COMMON / 'config') == common_config_sha
                and proof_context(h, r7)[2] == proof_before,
                'P2 controls or qualified context changed during preflight')
        require(all({'resolved': str(h.fs_resolution(Path(p))[0]), 'links': h.fs_resolution(Path(p))[1]} == v
                    for p, v in resolutions.items()), 'Protected realpath changed')
        require(shutil.disk_usage(BASELINE).free + allocated >= PROOF_MINIMUM_FREE + NEXT_PREPARATION_RESERVE,
                'Evidence writes consumed the safe preparation reserve')
        state['status'] = 'READ_ONLY_PLAN_VERIFIED'
        save()
        if not args.apply:
            state['ended_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
            save()
            print('P25_BASELINE_STORAGE_PLAN ' + json.dumps(state), flush=True)
            return 0
        state.update(mutation_started=True, status='APPLYING_EXACT_BASELINE_DOCUMENT_OMISSIONS')
        save()
        apply_sparse(BASELINE, rules, args.output)
        after_git = h.git_state()
        require(after_git['refs'] == git_before['refs']
                and after_git['worktree_listing_sha256'] == git_before['worktree_listing_sha256'], 'Git refs/worktrees changed')
        for name, before in git_before['worktrees'].items():
            after = after_git['worktrees'][name]
            if name != str(BASELINE):
                require(after == before, 'Another worktree changed: ' + name)
            else:
                require(all(after[k] == before[k] for k in before
                            if k not in ('index_sha256', 'sparse_settings', 'worktree_config')), 'Baseline source identity changed')
                require(after['sparse_settings'] == dict(before['sparse_settings'], **{
                    'core.sparsecheckout': 'true', 'core.sparsecheckoutcone': 'false', 'index.sparse': 'false'}),
                    'Unexpected baseline sparse mode')
                allowed = {'core.sparsecheckout', 'core.sparsecheckoutcone', 'index.sparse'}
                require({k:v for k,v in after['worktree_config'].items() if k not in allowed} ==
                        {k:v for k,v in before['worktree_config'].items() if k not in allowed}, 'Unrelated private config changed')
        require(h.config_file(COMMON / 'config') == common_before and h.sha(COMMON / 'config') == common_config_sha,
                'Shared Git config changed')
        require((private / 'info/sparse-checkout').read_bytes() == rules, 'Installed sparse rules differ')
        baseline_after = h.inventory(BASELINE)
        files = lambda snapshot: {p:v for p,v in snapshot.items() if v['kind'] != 'directory'}
        require(files(baseline_after) == {p:v for p,v in files(baseline_before).items() if p not in candidates},
                'A nonselected baseline file or symlink changed')
        require(untracked(h, BASELINE) == baseline_untracked, 'Baseline untracked/ignored files changed')
        require(h.inventory(PROOF_ROOT) == proof_files_before, 'P2 proof root changed')
        require(h.inventory(COMMON / 'objects') == objects_before, 'Git objects/history changed')
        require(proof_context(h, r7)[2] == proof_before, 'P2 frozen state or original baseline checks changed')
        require(all({'resolved': str(h.fs_resolution(Path(p))[0]), 'links': h.fs_resolution(Path(p))[1]} == v
                    for p, v in resolutions.items()), 'Protected realpath changed after sparse set')
        require(all(not os.path.lexists(BASELINE / p) for p in candidates)
                and all(os.path.lexists(BASELINE / p) for p in included), 'Materialized file set differs')
        free_after = shutil.disk_usage(BASELINE).free
        require(free_after >= PROOF_MINIMUM_FREE + NEXT_PREPARATION_RESERVE,
                'Recovered space does not satisfy the unchanged proof gate plus preparation reserve')
        (args.output / 'GIT_AFTER.json').write_bytes(encoded(after_git))
        state.update(status='BASELINE_DOCUMENT_RECOVERY_VERIFIED_NO_LEAN', storage_recovery_verified=True,
                     ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                     disk_free_after=free_after, observed_free_increase=free_after-state['disk_free_before'],
                     all_proof_sources_receipts_caches_and_other_worktrees_unchanged=True,
                     baseline_Lean_symlinks_untracked_and_all_nonselected_files_unchanged=True)
        save()
        print('P25_BASELINE_STORAGE_RESULT ' + json.dumps(state), flush=True)
        return 0
    except Exception as error:
        state.update(error=str(error), traceback=traceback.format_exc(),
                     status='STOPPED_PRESERVE_EVIDENCE_NO_AUTOMATIC_SCOPE_EXPANSION',
                     ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
        save()
        print('P25_BASELINE_STORAGE_STOP ' + json.dumps(state), flush=True)
        return 1


if __name__ == '__main__':
    sys.exit(main())
