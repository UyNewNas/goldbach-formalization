#!/usr/bin/env python3
"""Validate the explicit Batch12 symbolic group or single literal pilot.

No source installation. All candidate/ancestor sources must match commit 220c1463.
Normal provenance and completed e9 validation reuse the published Batch11 caller.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import sys
import types

sys.dont_write_bytecode = True
SOURCE = '220c14630ffd266f824bdbf0977147ecb740c0dd'
TOOLS = '9246927b8faebca3c06e4a5a47e733b5f13536db'
PROJECT = Path('/workspace/blue-member-build')
REPO = Path('/workspace/goldbach-formalization')
RETRY = 'docs/p1/20261125/batch11-repairs/retry_four.py'
RETRY_SHA = '290228a30d7a773a52a27241d6d3fbf18efb3d5e3fd9b30c8f0db4d670e5717e'
CANDIDATES = 'docs/p1/20261125/next-frontier/batch12-candidates/CANDIDATES.json'
CANDIDATES_SHA = 'd7c1e944853ecf78d7c8c7d3179f9ca54333b21841c8d849a3b8dcf314532115'
GROUPS = {
    'symbolic': ['ImbalancedChen.P4AOriginalFull87PrefixBinding',
                 'ImbalancedChen.P4AOriginalFull87HistoryCore',
                 'ImbalancedChen.Part3ActualWResidualCompletion',
                 'ImbalancedChen.P1OriginalFifthMovingHarmonicEnvelope'],
    'literal-pilot': ['ImbalancedChen.P4AOriginalFull87AscendingAllInteriors'],
}
ROOTS = {group: Path('/workspace/p1-complete-proof/20261125-batch12-' + group + '-v1') for group in GROUPS}


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def inputs(repo, project, group):
    def git(commit, path):
        return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=repo)

    raw = {RETRY: git(TOOLS, RETRY), CANDIDATES: git(TOOLS, CANDIDATES)}
    need(sha(raw[RETRY]) == RETRY_SHA and sha(raw[CANDIDATES]) == CANDIDATES_SHA, 'published caller/candidate pin differs')
    api = types.ModuleType('published_batch11_primitives')
    api.__file__ = '<pinned Git object: ' + RETRY + '>'
    exec(compile(raw[RETRY], api.__file__, 'exec'), api.__dict__)
    need(api.COMMIT == SOURCE and api.PROJECT == PROJECT and api.REPO == REPO, 'published primitive environment differs')
    pins = {RETRY: RETRY_SHA, CANDIDATES: CANDIDATES_SHA}
    for path in (api.HELPER, api.OPS, api.PRIMITIVES, api.E9):
        raw[path] = git(SOURCE, path)
        pins[path] = api.PINS[path]
        need(sha(raw[path]) == pins[path], 'unchanged helper pin differs: ' + path)
    h = api.load(raw[api.HELPER], 'batch5')
    ops = api.load(raw[api.OPS], 'batch6')
    d = api.load(raw[api.PRIMITIVES], 'snapshot_primitives')
    catalog = json.loads(raw[CANDIDATES])
    need(catalog['schema'] == 'p1_batch12_candidate_review_v1' and
         catalog['anchor']['published_commit'] == SOURCE, 'candidate source anchor differs')
    rows = {row['module']: row for row in catalog['candidates']}
    targets = GROUPS[group]
    graph, actual = h.project_graph(project, targets)
    sources = {}
    for m in graph:
        source = git(SOURCE, h.module_path(m))
        sources[m] = sha(source)
        need(actual[m]['sha256'] == sources[m], 'source differs; no installation permitted: ' + m)
    for m in targets:
        need(rows[m]['source']['path'] == h.module_path(m) and rows[m]['source']['sha256'] == sources[m] and
             rows[m]['direct_project_imports'] == graph[m], 'candidate catalog differs: ' + m)
        need(not (set().union(*map(set, GROUPS.values())) - {m}) & h.closure(graph, [m]), 'candidate groups overlap by dependency')
    need(not set(api.TARGETS) & set(graph), 'candidate closure includes a separately repaired Batch11 target')
    need(all(sha((project / h.module_path(m)).read_bytes()) == value for m, value in h.FOUR_ROOTS.items()),
         'protected original root source differs')
    return api, h, ops, d, raw, pins, graph, sources


def audit(root, passed, graph, sources, api, h, ops, d, run, accepted):
    partials = []
    for directory in sorted((root / 'audits').glob('*')):
        need(directory.is_dir(), 'unexpected audit entry')
        if not (directory / 'lane-0/VALIDATION_RESULTS.json').is_file():
            partials.append(str(directory))
        else:
            accepted.update(api.audit_valid(directory, api.read_json(directory / 'AUDIT_PLAN.json'),
                                           passed, graph, sources, h, d))
    need(not partials, 'PARTIAL_AUDIT_REQUIRES_INSPECTION: ' + ', '.join(partials))
    selected = sorted(set(passed) - accepted)
    if not selected:
        return
    key = sha(json.dumps({m: passed[m]['normal_command']['command_sha256'] for m in selected}, sort_keys=True).encode())[:20]
    directory = root / 'audits' / key
    plan = {'schema': 'p1_completed_normal_multibatch_audit_plan_v1', 'status': 'NORMAL_REUSED_KERNEL_FULL_OWNED_PENDING',
            'source_review_head': SOURCE, 'project': str(PROJECT), 'receipt_root': str(directory),
            'runtime_states': list(map(str, h.STATES)),
            'audit_template': {'path': str(d.AUDIT_TEMPLATE), 'sha256': d.AUDIT_TEMPLATE_SHA},
            'normal_logs': {}, 'modules': {}, 'expected_project_sources': {},
            'lanes': [{'id': 0, 'modules': selected}, {'id': 1, 'modules': []}],
            'excluded_prior13': [], 'reused_complete_modules': sorted(accepted),
            'runner_binding': {'path': api.E9, 'sha256': api.PINS[api.E9]}, 'whole_P1_complete': False}
    for m in selected:
        api.normal_valid(m, passed[m], api.context(PROJECT, m, graph, sources, h, d), h, d)
        command = passed[m]['normal_command']
        closure = sorted(h.closure(graph, [m]))
        plan['normal_logs'][m] = {'path': command['log'], 'sha256': command['log_sha256'],
                                  'source_commit': SOURCE, 'expected_built_modules': [m]}
        plan['modules'][m] = {'source_sha256': sources[m], 'normal_log': m, 'project_closure': closure}
        plan['expected_project_sources'].update({dep: sources[dep] for dep in closure})
    plan_path = root / 'plans' / (key + '.json')
    d.save(plan_path, plan)
    (root / 'audits').mkdir(exist_ok=True)
    runner = root / 'inputs/e9.py'
    need(d.fingerprint(runner)['sha256'] == api.PINS[api.E9], 'frozen e9 runner differs')
    prepared = ops.run(run, 'audit-prepare', ['python3', '-B', str(runner), '--plan', str(plan_path), '--prepare-only'])
    need(prepared['exit_code'] == 0, 'audit preparation failed; preserve partial evidence')
    # This worker already holds the unchanged lane-0 serializer. e9 supplies guards.
    completed = ops.run(run, 'audit-lane-0', ['python3', '-B', str(runner), '--plan', str(directory / 'AUDIT_PLAN.json'),
                        '--receipt-root', str(directory), '--lane', '0'])
    need(completed['exit_code'] == 0, 'audit failed; preserve partial evidence')
    accepted.update(api.audit_valid(directory, plan, passed, graph, sources, h, d))


def worker(spec, group, run):
    api, h, ops, d, raw, pins, graph, sources = spec
    root, targets = ROOTS[group], GROUPS[group]
    d.verify_lane(h)
    binding = api.read_json(root / 'BINDING.json')
    need(binding['driver_sha256'] == sha(Path(__file__).read_bytes()) and binding['source_commit'] == SOURCE and
         binding['tooling_commit'] == TOOLS and binding['inputs'] == pins and binding['group'] == group and
         binding['targets'] == targets and binding['runtime'] == d.runtime_binding(h), 'worker binding differs')
    d.save(run / 'PROJECT_SOURCES.json', sources)
    passed, failures, accepted = {}, {}, set()
    for m in targets:
        try:
            passed[m] = api.normal_one(m, graph, sources, h, ops, d, root=root, project=PROJECT)
        except Exception as error:
            failures[m] = str(error)
            ops.emit('CANDIDATE_NORMAL_HELD_OR_FAILED', group=group, module=m, reason=str(error))
    audit_error = None
    try:
        audit(root, passed, graph, sources, api, h, ops, d, run, accepted)
    except Exception as error:
        audit_error = str(error)
        ops.emit('CANDIDATE_AUDIT_HELD_OR_FAILED', group=group, reason=audit_error)
    d.save(run / 'RESULT.json', {'source_commit': SOURCE, 'group': group, 'targets': targets,
           'normal_passed': sorted(passed), 'normal_failed_or_held': failures, 'accepted_owners': sorted(accepted),
           'audit_error': audit_error, 'all_group_owners_accepted': set(targets) == accepted,
           'source_installation_performed': False, 'whole_P1_complete': False, 'protected_roots': h.check_roots()})
    return 0 if set(targets) == accepted and not failures and audit_error is None else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--group', choices=GROUPS, required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--run', action='store_true')
    parser.add_argument('--source-repo', type=Path, default=REPO)
    parser.add_argument('--project', type=Path, default=PROJECT)
    parser.add_argument('--inside-lane', action='store_true', help=argparse.SUPPRESS)
    parser.add_argument('--run-dir', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    sys.setrecursionlimit(10000)
    repo, project, root = args.source_repo.resolve(), args.project.resolve(), ROOTS[args.group]
    spec = inputs(repo, project, args.group)
    api, h, ops, d, raw, pins, graph, sources = spec
    if args.check:
        need(not args.inside_lane and args.run_dir is None, 'invalid check arguments')
        print(json.dumps({'status': 'READ_ONLY_SOURCE_CHECK_PASS_NOT_ACCEPTANCE', 'group': args.group,
                          'source_commit': SOURCE, 'targets': GROUPS[args.group], 'source_closure_count': len(sources),
                          'source_installation_performed': False, 'whole_P1_complete': False}))
        return 0
    need(repo == REPO and project == PROJECT, 'execution is restricted to the existing cloud project')
    if args.inside_lane:
        need(args.run_dir is not None, 'serialized worker requires a run directory')
        run = args.run_dir.resolve()
        need(run.parent == root / 'runs' and re.fullmatch(r'attempt-[0-9]{5}', run.name) and run.is_dir(), 'invalid run directory')
        return worker(spec, args.group, run)
    need(args.run_dir is None, 'run-dir requires the serialized worker')
    original = d.original_git_state(repo)
    d.save(root / 'BINDING.json', {'source_commit': SOURCE, 'tooling_commit': TOOLS, 'group': args.group,
           'targets': GROUPS[args.group], 'driver_sha256': sha(Path(__file__).read_bytes()), 'inputs': pins,
           'runtime': d.runtime_binding(h), 'project': str(PROJECT)})
    for path, data in raw.items():
        d.write_frozen(root / 'inputs' / ('e9.py' if path == api.E9 else Path(path).name), data)
    executed = root / 'executed-driver.py'
    d.write_frozen(executed, Path(__file__).read_bytes())
    run = d.attempt(root / 'runs')
    d.save(run / 'GIT_BEFORE.json', original)
    try:
        command = ops.run(run, 'serialized-worker', h.serialize(0, run / 'VALIDATION_LANE.json', [
            'python3', '-B', str(executed), '--group', args.group, '--run', '--inside-lane', '--run-dir', str(run)]), relay=True)
        return command['exit_code']
    finally:
        after = d.original_git_state(repo)
        d.save(run / 'GIT_AFTER.json', after)
        need(after == original, 'original dirty source Git worktree changed')


if __name__ == '__main__':
    raise SystemExit(main())
