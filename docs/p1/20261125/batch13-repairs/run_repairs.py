#!/usr/bin/env python3
"""Retry the five manifest-bound Batch13 repairs as two separate groups.

--check reads Git objects and project sources only. --run installs the selected
group and uses lane 0 serially; --normal-only leaves kernel/full-owned work pending.
The source commit is explicit throughout. Historical fixed-source callers remain
unchanged, and neither an orphan ready object nor a partial audit is replayed.
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
TOOLS = '220c14630ffd266f824bdbf0977147ecb740c0dd'
PROJECT = Path('/workspace/blue-member-build')
REPO = Path('/workspace/goldbach-formalization')
ROOT = Path('/workspace/p1-complete-proof/20261125-batch13-repairs-v1')
MANIFEST = 'docs/p1/20261125/batch13-repairs/SOURCE_REPAIRS.json'
PREFIX = 'docs/p1/20261124/'
HELPER = PREFIX + 'batch5-parallel/run_batch5_parallel.py'
OPS = PREFIX + 'batch6-parallel/run_batch6_parallel.py'
E9 = PREFIX + 'normal-supplement-audit/run_parallel_acceptance_multibatch.py'
PRIMITIVES = 'docs/p1/20261125/batch10-resume/resume_batch10.py'
PINS = {
    HELPER: '1d166b6a36362e185559ea08a82100a49ba9edbeefcb98b1a904b9ff9330cbd5',
    OPS: 'e1338ef756fba98b126bb089413f2c489ed4de8682a61c11dfb8e61c8e518d11',
    E9: 'e9dadb4ee5cd0a9ad50e298a77c6133fe5e0d012f8b194ae02bd5118460fc9e1',
    PRIMITIVES: '63e999403a1d39251642097c8a03e8b60983df785267fcca32f118b57aab2f71',
}
GROUPS = {
    'symbolic': ['ImbalancedChen.P4AOriginalFull87PrefixBinding',
                 'ImbalancedChen.P4AOriginalFull87HistoryCore',
                 'ImbalancedChen.Part3ActualWResidualCompletion',
                 'ImbalancedChen.P1OriginalFifthMovingHarmonicEnvelope'],
    'literal-pilot': ['ImbalancedChen.P4AOriginalFull87AscendingAllInteriors'],
}
PASS = 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS'


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_json(path):
    path = Path(path)
    need(path.is_file() and not path.is_symlink(), 'receipt must be a regular file: ' + str(path))
    return json.loads(path.read_bytes())


def load(raw, name):
    module = types.ModuleType(name)
    module.__file__ = '<pinned Git object: ' + name + '>'
    exec(compile(raw, module.__file__, 'exec'), module.__dict__)
    return module


def validate_manifest(manifest, source_commit):
    need(re.fullmatch(r'[0-9a-f]{40}', source_commit) is not None, 'source-commit must be a full lowercase Git SHA')
    need(manifest['schema'] == 'p1_five_failed_target_source_repair_manifest_v1' and
         manifest['failed_source_commit'] == TOOLS, 'five-repair manifest schema or failed-source anchor differs')
    expected = [(m, group) for group, modules in GROUPS.items() for m in modules]
    need([(r['module'], r['group']) for r in manifest['modules']] == expected, 'five-owner manifest scope differs')
    for row in manifest['modules']:
        need(row['path'] == row['module'].replace('.', '/') + '.lean' and
             all(re.fullmatch(r'[0-9a-f]{64}', row[k]) for k in ('expected_before_sha256', 'source_sha256')) and
             row['expected_before_sha256'] != row['source_sha256'], 'repair path/hash differs: ' + row['module'])


def preflight_sources(project, updates, payloads, h):
    """Check the complete selected group without writing sources or backups."""
    for row in updates:
        path = project / row['path']
        need(row['path'] == h.module_path(row['module']) and
             sha(payloads[row['path']]) == row['after_sha256'], 'published repair payload differs')
        need(path.is_file() and not path.is_symlink(), 'source must be an existing regular file: ' + str(path))
        need(sha(path.read_bytes()) in (row['before_sha256'], row['after_sha256']),
             'unknown source preimage: ' + row['module'])


def inputs(repo, project, source_commit, group):
    need(re.fullmatch(r'[0-9a-f]{40}', source_commit) is not None, 'source-commit must be a full lowercase Git SHA')
    need(subprocess.check_output(['git', 'cat-file', '-t', source_commit], cwd=repo).strip() == b'commit',
         'source-commit must name an existing commit object')
    cache = {}

    def git(commit, path):
        key = (commit, path)
        if key not in cache:
            cache[key] = subprocess.check_output(['git', 'show', commit + ':' + path], cwd=repo)
        return cache[key]

    raw = {p: git(TOOLS, p) for p in PINS}
    need(all(sha(raw[p]) == digest for p, digest in PINS.items()), 'unchanged helper pin differs')
    raw[MANIFEST] = git(source_commit, MANIFEST)
    pins = {**PINS, MANIFEST: sha(raw[MANIFEST])}
    manifest = json.loads(raw[MANIFEST])
    validate_manifest(manifest, source_commit)
    h, ops, d = load(raw[HELPER], 'batch5'), load(raw[OPS], 'batch6'), load(raw[PRIMITIVES], 'snapshot_primitives')
    updates, payloads = [], {}
    for row in manifest['modules']:
        payload = git(source_commit, row['path'])
        need(sha(payload) == row['source_sha256'] and
             sha(git(manifest['failed_source_commit'], row['path'])) == row['expected_before_sha256'],
             'published repair/preimage differs: ' + row['module'])
        if row['group'] == group:
            payloads[row['path']] = payload
            updates.append({'module': row['module'], 'path': row['path'],
                            'before_sha256': row['expected_before_sha256'], 'after_sha256': row['source_sha256'],
                            'cloud_source_mutation_required': True})
    preflight_sources(project, updates, payloads, h)
    targets = GROUPS[group]
    graph, actual = h.project_graph(project, targets)
    sources = {m: sha(git(source_commit, h.module_path(m))) for m in graph}
    for m in graph:
        published_imports = [x for x in h.imports(git(source_commit, h.module_path(m))) if x.startswith('ImbalancedChen.')]
        need(graph[m] == published_imports, 'project imports differ: ' + m)
        need(m in targets or actual[m]['sha256'] == sources[m], 'dependency source differs: ' + m)
    all_targets = {m for modules in GROUPS.values() for m in modules}
    for m in targets:
        need(not (all_targets - {m}) & h.closure(graph, [m]), 'repair groups overlap by dependency')
    need(all(sha((project / h.module_path(m)).read_bytes()) == s for m, s in h.FOUR_ROOTS.items()),
         'protected original roots changed')
    return h, ops, d, raw, pins, updates, payloads, graph, sources


def context(source_commit, project, m, graph, sources, h, d):
    owners = h.closure(graph, [m])
    actual = {x: sha((project / h.module_path(x)).read_bytes()) for x in sorted(owners)}
    need(actual == {x: sources[x] for x in sorted(owners)}, 'normal source context changed: ' + m)
    objects = {}
    for dep in sorted(owners - {m}):
        for ext in ('.olean', '.trace'):
            rel = '.lake/build/lib/lean/' + dep.replace('.', '/') + ext
            objects[rel] = d.fingerprint(project / rel)
    configs = {p: d.fingerprint(project / p) for p in
               ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml', 'lakefile.lean') if (project / p).is_file()}
    return {'source_commit': source_commit, 'project_sources': actual,
            'dependency_objects_and_traces': objects, 'configuration': configs,
            'existing_runtime': d.runtime_binding(h)}


def normal_valid(source_commit, project, m, receipt, binding, h, d):
    need(receipt['module'] == m and receipt['source_commit'] == binding['source_commit'] == source_commit and
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


def normal_one(source_commit, project, root, m, graph, sources, h, ops, d):
    folder = root / 'normal' / m
    durable = folder / 'NORMAL_PASS.json'
    binding = lambda: context(source_commit, project, m, graph, sources, h, d)
    prior = read_json(durable) if os.path.lexists(durable) else None
    if prior is not None:
        normal_valid(source_commit, project, m, prior, binding(), h, d)
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
        normal_valid(source_commit, project, m, prior, binding(), h, d)
        ops.emit('NORMAL_REUSED', source_commit=source_commit, module=m)
        return prior
    need(prior is None and ready['exit_code'] == 3, 'normal receipt/readiness conflict: ' + m)
    ops.emit('NORMAL_START', source_commit=source_commit, module=m)
    command = ops.run(directory, 'normal', h.guard(0, ['lake', 'build', '+' + m + ':olean']), cwd=project)
    need(command['exit_code'] == 0 and command['actual_built_modules'] == [m] and
         d.BUILT.findall(d.ANSI.sub('', Path(command['log']).read_text())) == [m], 'normal failed/scope differs: ' + m)
    need(binding() == before, 'dependency context changed during normal: ' + m)
    command_path = directory / 'normal-command.json'
    receipt = {'status': 'NORMAL_PASS_AUDIT_PENDING', 'source_commit': source_commit, 'module': m,
               'source_plus_five_outputs': d.snapshot(project, m), 'dependency_context': before,
               'normal_command': dict(command, command_receipt=str(command_path),
                                      command_sha256=d.fingerprint(command_path)['sha256']),
               'whole_P1_complete': False, 'kernel_or_full_owned_claim': False}
    normal_valid(source_commit, project, m, receipt, binding(), h, d)
    d.save(durable, receipt)
    ops.emit('NORMAL_PASS_AUDIT_PENDING', source_commit=source_commit, module=m)
    return receipt


def audit_valid(source_commit, project, directory, plan, passed, graph, sources, h, d):
    selected = plan['lanes'][0]['modules']
    need(plan['schema'] == 'p1_completed_normal_multibatch_audit_plan_v1' and plan['project'] == str(project) and
         plan['receipt_root'] == str(directory) and plan['runner_binding'] == {'path': E9, 'sha256': PINS[E9]} and
         selected and len(selected) == len(set(selected)) and set(selected) <= set(passed) and
         plan['lanes'] == [{'id': 0, 'modules': selected}, {'id': 1, 'modules': []}] and
         set(plan['normal_logs']) == set(plan['modules']) == set(selected) and plan['source_review_head'] == source_commit,
         'audit owner/source scope differs')
    need(read_json(directory / 'AUDIT_PLAN.json') == plan and
         plan['audit_template'] == {'path': str(d.AUDIT_TEMPLATE), 'sha256': d.AUDIT_TEMPLATE_SHA} and
         plan['runtime_states'] == list(map(str, h.STATES)), 'audit frozen plan/runtime/template differs')
    for m in selected:
        normal_valid(source_commit, project, m, passed[m], context(source_commit, project, m, graph, sources, h, d), h, d)
        cmd = passed[m]['normal_command']
        need(plan['normal_logs'][m] == {'path': cmd['log'], 'sha256': cmd['log_sha256'],
             'source_commit': source_commit, 'expected_built_modules': [m]}, 'audit normal log binding differs')
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
         all(evidence[m]['path'] == plan['normal_logs'][m]['path'] and evidence[m]['sha256'] == plan['normal_logs'][m]['sha256'] and
             evidence[m]['source_commit'] == source_commit and evidence[m]['all_actual_built_modules'] == [m] and
             evidence[m]['selected_sources'] == {m: sources[m]} for m in selected), 'audit reused-normal evidence differs')
    need(result['source_plus_five_outputs'] == {m: d.snapshot(project, m) for m in selected} and
         result['runtime_state'] == str(h.STATES[0]) and result['runtime_state_sha256'] == d.fingerprint(h.STATES[0])['sha256'] and
         result['audit_template_sha256'] == d.AUDIT_TEMPLATE_SHA, 'stale audit outputs/runtime')
    commands = [result['stock_readiness_before'], *result['kernel_commands'].values(),
                result['audit_command'], result['stock_readiness_after']]
    need(set(result['kernel_commands']) == set(selected), 'audit kernel owner scope differs')
    for cmd in commands:
        log = lane / cmd['log']
        need(cmd['exit_code'] == 0 and cmd['cwd'] == str(project) and d.fingerprint(log)['sha256'] == cmd['log_sha256'] and
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
         result['total_owned_exports'] == len(records) and result['total_public_exports'] == sum(not x['is_private'] for x in records) and
         all(x['kind'] != 'axiom' and set(x['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for x in records) and
         not any(x in text for x in ['sorryAx', '…', '⋯', '...']), 'full-owned audit evidence differs')
    return set(selected)


def audit(source_commit, project, root, passed, graph, sources, h, ops, d, run, accepted):
    partials = []
    for directory in sorted((root / 'audits').glob('*')):
        need(directory.is_dir() and not directory.is_symlink(), 'unexpected audit entry')
        if not (directory / 'lane-0/VALIDATION_RESULTS.json').is_file():
            partials.append(str(directory))
        else:
            accepted.update(audit_valid(source_commit, project, directory, read_json(directory / 'AUDIT_PLAN.json'),
                                        passed, graph, sources, h, d))
    need(not partials, 'PARTIAL_AUDIT_REQUIRES_INSPECTION: ' + ', '.join(partials))
    selected = sorted(set(passed) - accepted)
    if not selected:
        return
    key = sha(json.dumps({'source_commit': source_commit,
                         'normal_commands': {m: passed[m]['normal_command']['command_sha256'] for m in selected}},
                        sort_keys=True).encode())[:20]
    directory = root / 'audits' / key
    plan = {'schema': 'p1_completed_normal_multibatch_audit_plan_v1', 'status': 'NORMAL_REUSED_KERNEL_FULL_OWNED_PENDING',
            'source_review_head': source_commit, 'project': str(project), 'receipt_root': str(directory),
            'runtime_states': list(map(str, h.STATES)),
            'audit_template': {'path': str(d.AUDIT_TEMPLATE), 'sha256': d.AUDIT_TEMPLATE_SHA},
            'normal_logs': {}, 'modules': {}, 'expected_project_sources': {},
            'lanes': [{'id': 0, 'modules': selected}, {'id': 1, 'modules': []}], 'excluded_prior13': [],
            'reused_complete_modules': sorted(accepted), 'runner_binding': {'path': E9, 'sha256': PINS[E9]},
            'whole_P1_complete': False}
    for m in selected:
        normal_valid(source_commit, project, m, passed[m], context(source_commit, project, m, graph, sources, h, d), h, d)
        cmd = passed[m]['normal_command']
        closure = sorted(h.closure(graph, [m]))
        plan['normal_logs'][m] = {'path': cmd['log'], 'sha256': cmd['log_sha256'],
                                  'source_commit': source_commit, 'expected_built_modules': [m]}
        plan['modules'][m] = {'source_sha256': sources[m], 'normal_log': m, 'project_closure': closure}
        plan['expected_project_sources'].update({x: sources[x] for x in closure})
    plan_path = root / 'plans' / (key + '.json')
    d.save(plan_path, plan)
    (root / 'audits').mkdir(exist_ok=True)
    runner = root / 'inputs/e9.py'
    need(d.fingerprint(runner)['sha256'] == PINS[E9], 'frozen e9 runner changed')
    prepared = ops.run(run, 'audit-prepare', ['python3', '-B', str(runner), '--plan', str(plan_path), '--prepare-only'], cwd=project)
    need(prepared['exit_code'] == 0, 'audit preparation failed; preserve partial evidence')
    # This worker already owns the existing lane-0 serializer; unchanged e9 supplies guards.
    completed = ops.run(run, 'audit-lane-0', ['python3', '-B', str(runner), '--plan', str(directory / 'AUDIT_PLAN.json'),
                        '--receipt-root', str(directory), '--lane', '0'], cwd=project)
    need(completed['exit_code'] == 0, 'audit failed; preserve partial evidence for inspection')
    accepted.update(audit_valid(source_commit, project, directory, plan, passed, graph, sources, h, d))


def worker(spec, source_commit, group, root, run, normal_only):
    h, ops, d, raw, pins, updates, payloads, graph, sources = spec
    d.verify_lane(h)
    binding = read_json(root / 'BINDING.json')
    need(binding == run_binding(source_commit, group, pins, h, d), 'worker binding changed')
    preflight_sources(PROJECT, updates, payloads, h)
    installed = h.install_sources(PROJECT, updates, payloads, run / 'source-backups')
    d.save(run / 'SOURCE_INSTALL.json', {'source_commit': source_commit, 'sources': installed,
                                       'protected_roots': h.check_roots()})
    d.save(run / 'PROJECT_SOURCES.json', {'source_commit': source_commit, 'sources': sources})
    passed, failures, accepted = {}, {}, set()
    for m in GROUPS[group]:
        try:
            passed[m] = normal_one(source_commit, PROJECT, root, m, graph, sources, h, ops, d)
        except Exception as error:
            failures[m] = str(error)
            ops.emit('NORMAL_HELD_OR_FAILED', source_commit=source_commit, group=group, module=m, reason=str(error))
    audit_error = None
    if not normal_only:
        try:
            audit(source_commit, PROJECT, root, passed, graph, sources, h, ops, d, run, accepted)
        except Exception as error:
            audit_error = str(error)
            ops.emit('AUDIT_HELD_OR_FAILED', source_commit=source_commit, group=group, reason=audit_error)
    d.save(run / 'RESULT.json', {'source_commit': source_commit, 'group': group, 'targets': GROUPS[group],
           'normal_passed': sorted(passed), 'normal_failed_or_held': failures, 'accepted_owners': sorted(accepted),
           'audit_error': audit_error, 'audit_requested': not normal_only,
           'all_group_owners_accepted': set(GROUPS[group]) == accepted,
           'whole_P1_complete': False, 'protected_roots': h.check_roots()})
    sufficient = set(passed) == set(GROUPS[group]) if normal_only else accepted == set(GROUPS[group])
    return 0 if sufficient and not failures and audit_error is None else 1


def run_binding(source_commit, group, pins, h, d):
    return {'source_commit': source_commit, 'tooling_commit': TOOLS, 'group': group, 'targets': GROUPS[group],
            'driver_sha256': sha(Path(__file__).read_bytes()), 'inputs': pins,
            'runtime': d.runtime_binding(h), 'project': str(PROJECT)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--group', choices=GROUPS, required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--run', action='store_true')
    parser.add_argument('--normal-only', action='store_true', help='Run normals only; later --run reuses them before audit.')
    parser.add_argument('--source-repo', type=Path, default=REPO)
    parser.add_argument('--project', type=Path, default=PROJECT)
    parser.add_argument('--inside-lane', action='store_true', help=argparse.SUPPRESS)
    parser.add_argument('--run-dir', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    sys.setrecursionlimit(10000)
    repo, project = args.source_repo.resolve(), args.project.resolve()
    spec = inputs(repo, project, args.source_commit, args.group)
    h, ops, d, raw, pins, updates, payloads, graph, sources = spec
    root = ROOT / args.source_commit / args.group
    if args.check:
        need(not args.inside_lane and args.run_dir is None and not args.normal_only, 'invalid check arguments')
        print(json.dumps({'status': 'READ_ONLY_SOURCE_CHECK_PASS_NOT_ACCEPTANCE', 'source_commit': args.source_commit,
              'manifest_sha256': pins[MANIFEST], 'group': args.group, 'targets': GROUPS[args.group],
              'source_closure_count': len(sources), 'source_installation_performed': False, 'whole_P1_complete': False}))
        return 0
    need(repo == REPO and project == PROJECT, 'execution is restricted to the existing cloud project')
    if args.inside_lane:
        need(args.run_dir is not None, 'serialized worker requires a run directory')
        run = args.run_dir.resolve()
        need(run.parent == root / 'runs' and re.fullmatch(r'attempt-[0-9]{5}', run.name) and run.is_dir(), 'invalid run directory')
        return worker(spec, args.source_commit, args.group, root, run, args.normal_only)
    need(args.run_dir is None, 'run-dir requires the serialized worker')
    original = d.original_git_state(repo)
    d.save(root / 'BINDING.json', run_binding(args.source_commit, args.group, pins, h, d))
    for path, data in raw.items():
        d.write_frozen(root / 'inputs' / ('e9.py' if path == E9 else Path(path).name), data)
    executed = root / 'executed-driver.py'
    d.write_frozen(executed, Path(__file__).read_bytes())
    run = d.attempt(root / 'runs')
    d.save(run / 'GIT_BEFORE.json', original)
    child = ['python3', '-B', str(executed), '--source-commit', args.source_commit, '--group', args.group,
             '--run', '--inside-lane', '--run-dir', str(run)] + (['--normal-only'] if args.normal_only else [])
    try:
        command = ops.run(run, 'serialized-worker', h.serialize(0, run / 'VALIDATION_LANE.json', child), relay=True)
        return command['exit_code']
    finally:
        after = d.original_git_state(repo)
        d.save(run / 'GIT_AFTER.json', after)
        need(after == original, 'original dirty source Git worktree changed')


if __name__ == '__main__':
    raise SystemExit(main())
