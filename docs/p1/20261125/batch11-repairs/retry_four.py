#!/usr/bin/env python3
"""Retry exactly the four published Batch11 repairs with unchanged validation tools.

--check reads pinned Git objects and project sources only. --run serializes the
four-source installation, independent normal attempts and one populated e9 lane.
Completed normal/audit receipts are validated before reuse; partial audits hold.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import types

sys.dont_write_bytecode = True
COMMIT = '220c14630ffd266f824bdbf0977147ecb740c0dd'
PROJECT = Path('/workspace/blue-member-build')
REPO = Path('/workspace/goldbach-formalization')
ROOT = Path('/workspace/p1-complete-proof/20261125-batch11-four-repairs-v1')
PREFIX = 'docs/p1/20261124/'
MANIFEST = 'docs/p1/20261125/batch11-repairs/SOURCE_REPAIRS.json'
HELPER = PREFIX + 'batch5-parallel/run_batch5_parallel.py'
OPS = PREFIX + 'batch6-parallel/run_batch6_parallel.py'
E9 = PREFIX + 'normal-supplement-audit/run_parallel_acceptance_multibatch.py'
PRIMITIVES = 'docs/p1/20261125/batch10-resume/resume_batch10.py'
PINS = {
    MANIFEST: 'f8c6b1f330c651e088330fa8d733c61c3752bfb95ef07617ebf14f76312eca1c',
    HELPER: '1d166b6a36362e185559ea08a82100a49ba9edbeefcb98b1a904b9ff9330cbd5',
    OPS: 'e1338ef756fba98b126bb089413f2c489ed4de8682a61c11dfb8e61c8e518d11',
    E9: 'e9dadb4ee5cd0a9ad50e298a77c6133fe5e0d012f8b194ae02bd5118460fc9e1',
    PRIMITIVES: '63e999403a1d39251642097c8a03e8b60983df785267fcca32f118b57aab2f71',
}
TARGETS = [
    'ImbalancedChen.P2OriginalSaving19SimplexMoments',
    'ImbalancedChen.P4AUpperTaggedContinuationAccounting',
    'ImbalancedChen.P4BPrimeEulerOperatorWords',
    'ImbalancedChen.P5OriginalCommonRefinedPreservation',
]
PASS = 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS'


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_json(path):
    return json.loads(Path(path).read_bytes())


def load(raw, name):
    module = types.ModuleType(name)
    module.__file__ = '<pinned Git object: ' + name + '>'
    exec(compile(raw, module.__file__, 'exec'), module.__dict__)
    return module


def inputs(repo, project):
    cache = {}

    def git(path):
        if path not in cache:
            cache[path] = subprocess.check_output(['git', 'show', COMMIT + ':' + path], cwd=repo)
        return cache[path]

    raw = {p: git(p) for p in PINS}
    need(all(sha(raw[p]) == digest for p, digest in PINS.items()), 'pinned input changed')
    h, ops, d = load(raw[HELPER], 'batch5'), load(raw[OPS], 'batch6'), load(raw[PRIMITIVES], 'primitives')
    manifest = json.loads(raw[MANIFEST])
    need(manifest['schema'] == 'p1_four_failed_target_source_repair_manifest_v1' and
         [r['module'] for r in manifest['modules']] == TARGETS, 'four-owner manifest scope')
    updates, payloads = [], {}
    for row in manifest['modules']:
        need(row['path'] == h.module_path(row['module']), 'source path differs')
        payload = git(row['path'])
        need(sha(payload) == row['source_sha256'], 'published repair payload differs')
        payloads[row['path']] = payload
        updates.append({'module': row['module'], 'path': row['path'],
                        'before_sha256': row['expected_before_sha256'],
                        'after_sha256': row['source_sha256'], 'cloud_source_mutation_required': True})
    # Whole-batch read-only preflight precedes any project source or backup write.
    for row in updates:
        path = project / row['path']
        need(path.is_file() and not path.is_symlink(), 'source must be an existing regular file: ' + str(path))
        need(sha(path.read_bytes()) in (row['before_sha256'], row['after_sha256']),
             'unknown source preimage: ' + row['module'])
    graph, actual = h.project_graph(project, TARGETS)
    sources = {m: sha(git(h.module_path(m))) for m in graph}
    for m in graph:
        published_imports = [x for x in h.imports(git(h.module_path(m))) if x.startswith('ImbalancedChen.')]
        need(graph[m] == published_imports, 'project imports differ: ' + m)
        need(m in TARGETS or actual[m]['sha256'] == sources[m], 'dependency source differs: ' + m)
    for m in TARGETS:
        need(not (set(TARGETS) - {m}) & h.closure(graph, [m]), 'repair targets are not independent')
    need(all(sha((project / h.module_path(m)).read_bytes()) == s for m, s in h.FOUR_ROOTS.items()),
         'protected original roots changed')
    return h, ops, d, raw, updates, payloads, graph, sources


def context(project, m, graph, sources, h, d):
    owners = h.closure(graph, [m])
    actual = {x: sha((project / h.module_path(x)).read_bytes()) for x in sorted(owners)}
    need(actual == {x: sources[x] for x in sorted(owners)}, 'normal source context changed: ' + m)
    objects = {}
    for dep in sorted(owners - {m}):
        for ext in ('.olean', '.trace'):
            rel = '.lake/build/lib/lean/' + dep.replace('.', '/') + ext
            objects[rel] = d.fingerprint(project / rel)
    configs = {p: d.fingerprint(project / p) for p in
               ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'lakefile.lean')
               if (project / p).is_file()}
    return {'source_commit': COMMIT, 'project_sources': actual,
            'dependency_objects_and_traces': objects, 'configuration': configs,
            'existing_runtime': d.runtime_binding(h)}


def normal_valid(m, receipt, binding, h, d, project=PROJECT):
    need(receipt['module'] == m and receipt['source_commit'] == COMMIT and
         receipt['status'] == 'NORMAL_PASS_AUDIT_PENDING', 'normal receipt identity differs: ' + m)
    need(receipt['dependency_context'] == binding and
         receipt['source_plus_five_outputs'] == d.snapshot(project, m), 'stale normal binding: ' + m)
    command = receipt['normal_command']
    path = Path(command['command_receipt'])
    need(d.fingerprint(path)['sha256'] == command['command_sha256'], 'normal command hash differs')
    rec = read_json(path)
    need(all(command.get(k) == v for k, v in rec.items()), 'normal command copy differs')
    need(rec['exit_code'] == 0 and rec['cwd'] == str(project) and
         rec['argv'] == h.guard(0, ['lake', 'build', '+' + m + ':olean']), 'normal command scope differs')
    log = Path(rec['log'])
    need(d.fingerprint(log) == {'bytes': rec['log_bytes'], 'sha256': rec['log_sha256']}, 'normal log differs')
    need(d.BUILT.findall(d.ANSI.sub('', log.read_text())) == [m] and
         rec['actual_built_modules'] == [m] and rec['actual_failed_modules'] == [], 'normal build scope differs')


def normal_one(m, graph, sources, h, ops, d, root=ROOT, project=PROJECT):
    folder = root / 'normal' / m
    durable = folder / 'NORMAL_PASS.json'
    binding = lambda: context(project, m, graph, sources, h, d)
    prior = read_json(durable) if durable.exists() else None
    if prior:
        normal_valid(m, prior, binding(), h, d, project)
    directory = d.attempt(folder)
    if graph[m]:
        deps = ops.run(directory, 'directdeps', h.guard(0, ['lake', '--no-build', 'build'] +
                       ['+' + dep + ':olean' for dep in graph[m]]), cwd=project)
        need(deps['exit_code'] == 0, 'DIRECT_DEPENDENCIES_NOT_READY: ' + m)
    before = binding()
    d.save(directory / 'CONTEXT_BEFORE.json', before)
    ready = ops.run(directory, 'target-ready', h.guard(0, ['lake', '--no-build', 'build', '+' + m + ':olean']), cwd=project)
    if ready['exit_code'] == 0:
        need(prior is not None, 'READY_WITHOUT_NORMAL_PROVENANCE: ' + m)
        normal_valid(m, prior, binding(), h, d, project)
        ops.emit('NORMAL_REUSED', module=m)
        return prior
    need(prior is None and ready['exit_code'] == 3, 'normal receipt/readiness conflict: ' + m)
    ops.emit('NORMAL_START', module=m)
    command = ops.run(directory, 'normal', h.guard(0, ['lake', 'build', '+' + m + ':olean']), cwd=project)
    need(command['exit_code'] == 0 and command['actual_built_modules'] == [m] and
         d.BUILT.findall(d.ANSI.sub('', Path(command['log']).read_text())) == [m], 'normal failed/scope differs: ' + m)
    need(binding() == before, 'dependency context changed during normal: ' + m)
    command_path = directory / 'normal-command.json'
    receipt = {'status': 'NORMAL_PASS_AUDIT_PENDING', 'source_commit': COMMIT, 'module': m,
               'source_plus_five_outputs': d.snapshot(project, m), 'dependency_context': before,
               'normal_command': dict(command, command_receipt=str(command_path),
                                      command_sha256=d.fingerprint(command_path)['sha256']),
               'whole_P1_complete': False, 'kernel_or_full_owned_claim': False}
    normal_valid(m, receipt, binding(), h, d, project)
    d.save(durable, receipt)
    ops.emit('NORMAL_PASS_AUDIT_PENDING', module=m)
    return receipt


def audit_valid(directory, plan, passed, graph, sources, h, d):
    selected = plan['lanes'][0]['modules']
    need(plan['schema'] == 'p1_completed_normal_multibatch_audit_plan_v1' and plan['project'] == str(PROJECT) and
         plan['receipt_root'] == str(directory) and plan['runner_binding'] == {'path': E9, 'sha256': PINS[E9]} and
         selected and set(selected) <= set(passed) and plan['lanes'][1]['modules'] == [] and
         set(plan['modules']) == set(selected) and plan['source_review_head'] == COMMIT, 'audit owner scope differs')
    need(plan['audit_template'] == {'path': str(d.AUDIT_TEMPLATE), 'sha256': d.AUDIT_TEMPLATE_SHA} and
         plan['runtime_states'] == list(map(str, h.STATES)), 'audit runtime/template differs')
    for m in selected:
        normal_valid(m, passed[m], context(PROJECT, m, graph, sources, h, d), h, d)
        cmd = passed[m]['normal_command']
        need(plan['normal_logs'][m] == {'path': cmd['log'], 'sha256': cmd['log_sha256'],
             'source_commit': COMMIT, 'expected_built_modules': [m]}, 'audit normal log binding differs')
        need(plan['modules'][m] == {'source_sha256': sources[m], 'normal_log': m,
             'project_closure': sorted(h.closure(graph, [m]))}, 'audit source closure differs')
    expected = {m: sources[m] for m in sorted(h.closure(graph, selected))}
    need(plan['expected_project_sources'] == expected, 'audit source map differs')
    lane = directory / 'lane-0'
    result = read_json(lane / 'VALIDATION_RESULTS.json')
    need(result['status'] == PASS and result['modules'] == {m: sources[m] for m in selected} and
         result['plan_sha256'] == d.fingerprint(directory / 'AUDIT_PLAN.json')['sha256'] and
         result['project_dependency_sources'] == expected, 'audit result binding differs')
    evidence = result['reused_normal_evidence']
    need(set(evidence) == set(selected) and read_json(lane / 'REUSED_NORMAL_EVIDENCE.json') == evidence and
         all(evidence[m]['path'] == plan['normal_logs'][m]['path'] and
             evidence[m]['sha256'] == plan['normal_logs'][m]['sha256'] and evidence[m]['source_commit'] == COMMIT and
             evidence[m]['all_actual_built_modules'] == [m] and evidence[m]['selected_sources'] == {m: sources[m]}
             for m in selected), 'audit reused-normal evidence differs')
    need(result['source_plus_five_outputs'] == {m: d.snapshot(PROJECT, m) for m in selected} and
         result['runtime_state'] == str(h.STATES[0]) and
         result['runtime_state_sha256'] == d.fingerprint(h.STATES[0])['sha256'] and
         result['audit_template_sha256'] == d.AUDIT_TEMPLATE_SHA, 'stale audit outputs/runtime')
    commands = [result['stock_readiness_before'], *result['kernel_commands'].values(),
                result['audit_command'], result['stock_readiness_after']]
    need(set(result['kernel_commands']) == set(selected), 'audit kernel owner scope differs')
    for cmd in commands:
        log = lane / cmd['log']
        need(cmd['exit_code'] == 0 and cmd['cwd'] == str(PROJECT) and
             d.fingerprint(log)['sha256'] == cmd['log_sha256'] and
             read_json(log.with_name(log.stem + '-command.json')) == cmd, 'audit command/log differs')
    for m, cmd in result['kernel_commands'].items():
        need(cmd['argv'] == h.guard(0, ['lake', 'env', 'leanchecker', '--verbose', m]), 'kernel argv differs')
    readiness_argv = h.guard(0, ['lake', '--no-build', 'build'] + ['+' + m + ':olean' for m in selected])
    need(result['stock_readiness_before']['argv'] == result['stock_readiness_after']['argv'] == readiness_argv,
         'audit readiness argv differs')
    need(result['audit_command']['argv'] == h.guard(0, ['lake', 'env', 'lean', '-DmaxRecDepth=100000',
         '-DmaxHeartbeats=4000000', '--root=' + str(lane), str(lane / 'PublicAudit.lean')]), 'owned audit argv differs')
    text = (lane / 'all-owned-types-axioms.log').read_text()
    records = [json.loads(x) for x in re.findall(r'AUDIT_RECORD (\{[^\n]+\})', text)]
    inventory = [json.loads(x)['names'] for x in re.findall(r'MEMBER_OWNED_NAMES (\{[^\n]+\})', text)]
    names = [x['name'] for x in records]
    need(len(inventory) == 1 and sorted(names) == sorted(inventory[0]) and len(names) == len(set(names)) and
         {x['module'] for x in records} == set(selected) and read_json(lane / 'OWNED_EXPORTS.json') == records and
         all(x['kind'] != 'axiom' and set(x['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for x in records) and
         not any(x in text for x in ['sorryAx', '…', '⋯', '...']), 'full-owned audit evidence differs')
    return set(selected)


def audit(passed, graph, sources, h, ops, d, run, accepted):
    partials = []
    for directory in sorted((ROOT / 'audits').glob('*')):
        need(directory.is_dir(), 'unexpected audit entry')
        if not (directory / 'lane-0/VALIDATION_RESULTS.json').is_file():
            partials.append(str(directory))
            continue
        accepted.update(audit_valid(directory, read_json(directory / 'AUDIT_PLAN.json'), passed, graph, sources, h, d))
    need(not partials, 'PARTIAL_AUDIT_REQUIRES_INSPECTION: ' + ', '.join(partials))
    selected = sorted(set(passed) - accepted)
    if not selected:
        return accepted
    key = sha(json.dumps({m: passed[m]['normal_command']['command_sha256'] for m in selected}, sort_keys=True).encode())[:20]
    directory = ROOT / 'audits' / key
    plan = {'schema': 'p1_completed_normal_multibatch_audit_plan_v1',
            'status': 'NORMAL_REUSED_KERNEL_FULL_OWNED_PENDING', 'source_review_head': COMMIT,
            'project': str(PROJECT), 'receipt_root': str(directory), 'runtime_states': list(map(str, h.STATES)),
            'audit_template': {'path': str(d.AUDIT_TEMPLATE), 'sha256': d.AUDIT_TEMPLATE_SHA},
            'normal_logs': {}, 'modules': {}, 'expected_project_sources': {},
            'lanes': [{'id': 0, 'modules': selected}, {'id': 1, 'modules': []}],
            'excluded_prior13': [], 'reused_complete_modules': sorted(accepted),
            'runner_binding': {'path': E9, 'sha256': PINS[E9]}, 'whole_P1_complete': False}
    for m in selected:
        normal_valid(m, passed[m], context(PROJECT, m, graph, sources, h, d), h, d)
        cmd = passed[m]['normal_command']
        closure = sorted(h.closure(graph, [m]))
        plan['normal_logs'][m] = {'path': cmd['log'], 'sha256': cmd['log_sha256'],
                                  'source_commit': COMMIT, 'expected_built_modules': [m]}
        plan['modules'][m] = {'source_sha256': sources[m], 'normal_log': m, 'project_closure': closure}
        plan['expected_project_sources'].update({x: sources[x] for x in closure})
    plan_path = ROOT / 'plans' / (key + '.json')
    d.save(plan_path, plan)
    (ROOT / 'audits').mkdir(exist_ok=True)
    runner = ROOT / 'inputs' / 'e9.py'
    need(d.fingerprint(runner)['sha256'] == PINS[E9], 'frozen e9 runner changed')
    prepared = ops.run(run, 'audit-prepare', ['python3', '-B', str(runner), '--plan', str(plan_path), '--prepare-only'])
    need(prepared['exit_code'] == 0, 'audit preparation failed; preserve partial evidence')
    # The worker already holds the original lane-0 serializer; e9 supplies guards.
    completed = ops.run(run, 'audit-lane-0', ['python3', '-B', str(runner), '--plan', str(directory / 'AUDIT_PLAN.json'),
                        '--receipt-root', str(directory), '--lane', '0'])
    need(completed['exit_code'] == 0, 'audit failed; preserve partial evidence for inspection')
    accepted.update(audit_valid(directory, plan, passed, graph, sources, h, d))
    return accepted


def worker(spec, run):
    h, ops, d, raw, updates, payloads, graph, sources = spec
    d.verify_lane(h)
    binding = read_json(ROOT / 'BINDING.json')
    need(binding['driver_sha256'] == sha(Path(__file__).read_bytes()) and
         binding['source_commit'] == COMMIT and binding['inputs'] == PINS and
         binding['runtime'] == d.runtime_binding(h), 'worker binding changed')
    installed = h.install_sources(PROJECT, updates, payloads, run / 'source-backups')
    d.save(run / 'SOURCE_INSTALL.json', {'source_commit': COMMIT, 'sources': installed, 'protected_roots': h.check_roots()})
    passed, failures = {}, {}
    for m in TARGETS:
        try:
            passed[m] = normal_one(m, graph, sources, h, ops, d)
        except Exception as error:
            failures[m] = str(error)
            ops.emit('NORMAL_HELD_OR_FAILED', module=m, reason=str(error))
    accepted, audit_error = set(), None
    try:
        audit(passed, graph, sources, h, ops, d, run, accepted)
    except Exception as error:
        audit_error = str(error)
        ops.emit('AUDIT_HELD_OR_FAILED', reason=audit_error)
    d.save(run / 'RESULT.json', {'source_commit': COMMIT, 'normal_passed': sorted(passed),
           'normal_failed_or_held': failures, 'accepted_owners': sorted(accepted), 'audit_error': audit_error,
           'all_four_accepted': set(TARGETS) == accepted, 'whole_P1_complete': False, 'protected_roots': h.check_roots()})
    return 0 if set(TARGETS) == accepted and not failures and audit_error is None else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--run', action='store_true')
    parser.add_argument('--source-repo', type=Path, default=REPO)
    parser.add_argument('--project', type=Path, default=PROJECT)
    parser.add_argument('--inside-lane', action='store_true', help=argparse.SUPPRESS)
    parser.add_argument('--run-dir', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    sys.setrecursionlimit(10000)
    repo, project = args.source_repo.resolve(), args.project.resolve()
    spec = inputs(repo, project)
    h, ops, d, raw, updates, payloads, graph, sources = spec
    if args.check:
        need(not args.inside_lane and args.run_dir is None, 'invalid check arguments')
        print(json.dumps({'status': 'READ_ONLY_SOURCE_CHECK_PASS', 'source_commit': COMMIT,
                          'targets': TARGETS, 'source_closure_count': len(sources), 'whole_P1_complete': False}))
        return 0
    need(repo == REPO and project == PROJECT, 'execution is restricted to the existing cloud project')
    if args.inside_lane:
        run = args.run_dir.resolve()
        need(run.parent == ROOT / 'runs' and re.fullmatch(r'attempt-[0-9]{5}', run.name) and run.is_dir(), 'invalid run directory')
        return worker(spec, run)
    need(args.run_dir is None, 'run-dir requires the serialized worker')
    original = d.original_git_state(repo)
    binding = {'source_commit': COMMIT, 'driver_sha256': sha(Path(__file__).read_bytes()),
               'inputs': PINS, 'runtime': d.runtime_binding(h), 'project': str(PROJECT), 'targets': TARGETS}
    d.save(ROOT / 'BINDING.json', binding)
    for path, data in raw.items():
        d.write_frozen(ROOT / 'inputs' / ('e9.py' if path == E9 else Path(path).name), data)
    executed = ROOT / 'executed-driver.py'
    d.write_frozen(executed, Path(__file__).read_bytes())
    run = d.attempt(ROOT / 'runs')
    d.save(run / 'GIT_BEFORE.json', original)
    try:
        command = ops.run(run, 'serialized-worker', h.serialize(0, run / 'VALIDATION_LANE.json', [
            'python3', '-B', str(executed), '--run', '--inside-lane', '--run-dir', str(run)]), relay=True)
        return command['exit_code']
    finally:
        after = d.original_git_state(repo)
        d.save(run / 'GIT_AFTER.json', after)
        need(after == original, 'original dirty source Git worktree changed')


if __name__ == '__main__':
    raise SystemExit(main())
