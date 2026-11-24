#!/usr/bin/env python3
"""Published, receipt-gated Higher-only normal build using the existing lane 0.

prepare() does not install project sources or invoke Lean. lane0_worker() must
be called inside the existing outer serializer; it never acquires a second
serializer. The standalone entry point supplies that one outer serializer.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import traceback

sys.dont_write_bytecode = True
PROJECT = Path('/workspace/blue-member-build')
GIT = Path('/workspace/goldbach-formalization')
PREFIX = 'docs/p1/20261124/higher-full-after-batch8/'
PLAN_PATH = PREFIX + 'EXECUTION_PLAN.json'
DRIVER_PATH = PREFIX + 'run_higher_full_after_batch8.py'
PLAN_SHA = '03b488f5b2df0d5112107a6e44003ad0e8ce0ee095bae5f0264d9596f80612cf'


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def put(path, data):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as stream:
        stream.write(data)


def read_json(path):
    return json.loads(Path(path).read_bytes())


def load_helper(path, expected, name):
    assert sha(path) == expected, ('helper_sha256', str(path))
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def helpers(root, plan):
    rows = plan['reused_python_sources']
    h = load_helper(root / 'inputs' / rows[0]['input_name'], rows[0]['sha256'], 'higher_batch5_exact')
    ops = load_helper(root / 'inputs' / rows[1]['input_name'], rows[1]['sha256'], 'higher_batch6_exact')
    assert h.PROJECT == ops.PROJECT == PROJECT and h.GIT_REPO == GIT
    assert h.HIGHER == plan['normal_target']
    assert h.FOUR_ROOTS == plan['protected_original_four_roots_sha256']
    assert (h.GUARD, h.SERIALIZER, str(h.STATES[0])) == (
        plan['runtime']['guard'], plan['runtime']['serializer'], plan['runtime']['state'])
    return h, ops


def runtime_binding(plan):
    return {plan['runtime'][key]: {'bytes': Path(plan['runtime'][key]).stat().st_size,
                                 'sha256': sha(plan['runtime'][key])}
            for key in ('guard', 'serializer', 'state')}


def artifact_paths(module):
    # Exact six-path layout of e9dadb4... audit runner's snap(); no .olean rename.
    rel = module.replace('.', '/')
    return [rel + '.lean', '.lake/build/lib/lean/' + rel + '.olean',
            '.lake/build/lib/lean/' + rel + '.ilean', '.lake/build/ir/' + rel + '.c',
            '.lake/build/ir/' + rel + '.setup.json', '.lake/build/lib/lean/' + rel + '.trace']


def source_plus_five(module, require_complete=True):
    paths = artifact_paths(module)
    if require_complete:
        assert all((PROJECT / p).is_file() for p in paths), ('missing_source_or_artifact', module)
    return {p: ({'bytes': (PROJECT / p).stat().st_size, 'sha256': sha(PROJECT / p)}
                if (PROJECT / p).is_file() else None) for p in paths}


def dependency_binding(plan, h):
    graph, sources = h.project_graph(PROJECT, [h.HIGHER])
    actual = {m: row['sha256'] for m, row in sources.items() if m != h.HIGHER}
    assert actual == plan['expected_project_dependencies'], 'higher_project_dependencies_changed'
    assert sorted(graph[h.HIGHER]) == plan['direct_project_dependencies']
    return actual


def probe_gate(plan, h):
    """Read actual cloud files. Missing/pending/nonzero/mismatched evidence stops."""
    b = plan['batch8']
    root = Path(b['root'])
    lane = root / 'execution' / 'lane-0'
    evidence = {}

    def bind(path, expected=None):
        path = Path(path)
        digest = sha(path)
        if expected is not None:
            assert digest == expected, ('probe_evidence_sha256', str(path), digest)
        evidence[str(path)] = {'sha256': digest, 'bytes': path.stat().st_size}
        return path

    def record(path, expected=None):
        return read_json(bind(path, expected))

    bind(root / 'executed-driver.py', b['driver_sha256'])
    batch_plan = read_json(bind(root / 'inputs' / 'EXECUTION_PLAN.json', b['plan_sha256']))
    cfg = record(root / 'RUN_CONFIG.json')
    assert cfg['commit'] == b['commit'] == plan['source_commit']
    assert cfg['driver_sha256'] == b['driver_sha256'] and cfg['plan_sha256'] == b['plan_sha256']
    assert cfg['probe_direct_project_dependencies'] == plan['direct_project_dependencies']
    assert batch_plan['higher_full_candidate_installed'] is False
    for row in plan['reused_python_sources']:
        bind(root / 'inputs' / row['input_name'], row['sha256'])
    reads = record(root / 'GIT_SHOW_READS.json')
    source_context = record(root / 'PROJECT_SOURCE_CONTEXT.json', b['project_source_context_sha256'])
    for module, expected in plan['expected_project_dependencies'].items():
        assert source_context[module]['sha256'] == expected, ('probe_dependency_context', module)
    outcome = record(lane / 'PROBE_RESULTS.json')
    assert outcome['old_passed_degree6_probe_repeated'] is False
    assert outcome['higher_full_module_candidate_installed'] is False
    assert outcome['higher_full_module_complete'] is False

    def command(name, expected_argv, expected_log_sha=None):
        path = lane / (name + '-command.json')
        result = record(path)
        started = record(lane / (name + '-started.json'))
        assert result['argv'] == expected_argv and result['cwd'] == str(PROJECT)
        assert type(result['exit_code']) is int and result['exit_code'] == 0, ('probe_command_not_passed', name)
        assert {k: result[k] for k in ('argv', 'cwd', 'started_utc')} == started
        assert result['finished_utc'] >= result['started_utc']
        assert result['elapsed_seconds'] >= 0
        logfile = lane / (name + '.log')
        assert result['log'] == str(logfile)
        bind(logfile, result['log_sha256'])
        assert logfile.stat().st_size == result['log_bytes']
        if expected_log_sha is not None:
            assert result['log_sha256'] == expected_log_sha, ('reported_probe_log_changed', name)
        return result

    ready = command('higher-new-probes-directdeps', h.guard(0,
        ['lake', '--no-build', 'build'] + ['+' + m + ':olean' for m in plan['direct_project_dependencies']]))
    results = [ready]
    for probe, frozen in zip(b['probes'], batch_plan['higher_probes_in_conditional_order'], strict=True):
        assert (frozen['name'], frozen['path'], frozen['sha256']) == (
            probe['name'], probe['published_path'], probe['source_sha256'])
        assert frozen['run_only_if_all_previous_probe_stages_exit_zero'] is True
        source = root / 'inputs' / 'probes' / Path(probe['published_path']).name
        bind(source, probe['source_sha256'])
        matching = [x for x in reads if x.get('path') == str(source)]
        assert len(matching) == 1
        row = matching[0]
        assert row['argv'] == ['git', 'show', b['commit'] + ':' + probe['published_path']]
        assert row['exit_code'] == 0 and row['sha256'] == probe['source_sha256']
        assert row['bytes'] == source.stat().st_size
        results.append(command(probe['name'], h.guard(0, [
            'lake', 'env', 'lean', '-DmaxRecDepth=100000', '-DmaxHeartbeats=4000000',
            '--root=' + str(source.parent), str(source)]), probe['expected_log_sha256']))
    assert outcome['stages'] == results
    assert results[1]['finished_utc'] <= results[2]['started_utc'], 'middle_did_not_follow_low'

    worker_argv = ['python3', str(root / 'executed-driver.py'), '--commit', b['commit'], '--worker', '--lane', '0']
    worker = command('worker', h.serialize(0, lane / 'VALIDATION_LANE.json', worker_argv), b['worker_log_sha256'])
    lock = record(lane / 'VALIDATION_LANE.json')
    assert lock['status'] == 'VALIDATION_LANE_FINISHED' and lock['exit_code'] == 0
    assert lock['argv'] == worker_argv and lock['state'] == str(h.STATES[0])
    assert lock['state_sha256'] == sha(h.STATES[0])
    assert lock['no_compiler_guard_runtime_or_memory_limit_changes'] is True
    assert lock['whole_chain_including_original_checker_serialized'] is True
    # Batch8's coordinator has finished both lanes and checked source stability.
    # Lane1 may have unrelated proof failures; only the probe lane must exit 0.
    final = record(root / 'BATCH8_RESULT.json')
    assert final['commit'] == b['commit'] and final['lane_commands'][0] == worker
    for key in ('all_context_sources_unchanged_during_execution', 'original_dirty_git_worktree_unchanged',
                'higher_canonical_source_unchanged'):
        assert final[key] is True, key
    assert final['higher_full_module_candidate_installed'] is False
    assert final['protected_roots'] == h.FOUR_ROOTS
    return {'status': 'ACTUAL_BATCH8_PROBES_AND_LANE0_VERIFIED', 'batch8_commit': b['commit'],
            'commands': results, 'worker_command': worker, 'runtime_state_sha256': sha(h.STATES[0]),
            'evidence_files': evidence, 'degree6_repeated': False, 'full_module_proved': False}


def git_unchanged(root, config):
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=GIT) == (root / 'git-head-before.bin').read_bytes()
    assert subprocess.check_output(['git', 'status', '--porcelain=v1', '-z'], cwd=GIT) == (root / 'git-status-before.bin').read_bytes()


def prepare(package_commit: str, receipt_root=None) -> dict:
    """Stage frozen published inputs and gate evidence. No source install or Lean."""
    assert re.fullmatch(r'[0-9a-f]{40}', package_commit), 'full published package commit required'
    # The external coordinator may stage this module under another filename.
    # Read the frozen plan from its published Git path, not a sibling filename.
    plan_bytes = subprocess.check_output(['git', 'show', package_commit + ':' + PLAN_PATH], cwd=GIT)
    assert hashlib.sha256(plan_bytes).hexdigest() == PLAN_SHA
    plan = json.loads(plan_bytes)
    assert plan['schema'] == 'p1_higher_full_after_batch8_normal_plan_v1'
    assert plan['project'] == str(PROJECT) and plan['git_repository'] == str(GIT)
    root = Path(receipt_root or plan['default_receipt_root']).resolve()
    assert root.is_relative_to('/workspace/p1-complete-proof/20261124-resume')
    root.mkdir(exist_ok=False)
    executed = root / 'executed-driver.py'
    put(executed, Path(__file__).read_bytes())
    put(root / 'inputs' / 'EXECUTION_PLAN.json', plan_bytes)
    put(root / 'git-head-before.bin', subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=GIT))
    put(root / 'git-status-before.bin', subprocess.check_output(['git', 'status', '--porcelain=v1', '-z'], cwd=GIT))
    reads = []

    def extract(commit, rel, destination, expected):
        argv = ['git', 'show', commit + ':' + rel]
        data = subprocess.check_output(argv, cwd=GIT)
        assert hashlib.sha256(data).hexdigest() == expected, ('published_input', rel)
        put(destination, data)
        reads.append({'argv': argv, 'cwd': str(GIT), 'exit_code': 0, 'path': str(destination),
                      'sha256': expected, 'bytes': len(data)})
        return data

    for row in plan['reused_python_sources']:
        extract(plan['source_commit'], row['path'], root / 'inputs' / row['input_name'], row['sha256'])
    h, ops = helpers(root, plan)
    fetch = ops.run(root, 'fetch-published-branch', ['git', 'fetch', 'origin', plan['publication_branch']], GIT)
    assert fetch['exit_code'] == 0
    for label, commit in [('package', package_commit), ('source', plan['source_commit'])]:
        check = ops.run(root, label + '-on-fetched-branch', ['git', 'merge-base', '--is-ancestor', commit, 'FETCH_HEAD'], GIT)
        assert check['exit_code'] == 0
    extract(package_commit, DRIVER_PATH, root / 'inputs' / 'published-driver.py', sha(executed))
    extract(package_commit, PLAN_PATH, root / 'inputs' / 'published-plan.json', PLAN_SHA)
    candidate = extract(plan['source_commit'], plan['candidate_published_path'], root / 'inputs' / 'candidate.lean', plan['candidate_sha256'])
    extract(plan['source_commit'], plan['canonical_path'], root / 'inputs' / 'published-preimage.lean', plan['source_preimage_sha256'])
    reference = plan['snapshot_layout_reference']
    extract(plan['source_commit'], reference['path'], root / 'inputs' / 'existing-audit-runner-reference.py', reference['sha256'])
    h.check_roots()
    gate = probe_gate(plan, h)
    assert sha(PROJECT / plan['canonical_path']) == plan['source_preimage_sha256'], 'source_not_3bc_preimage_review_existing_work_no_rebuild'
    assert h.imports(candidate) == h.imports((PROJECT / plan['canonical_path']).read_bytes())
    dependencies = dependency_binding(plan, h)
    for path, binding in gate['evidence_files'].items():
        source = Path(path)
        assert sha(source) == binding['sha256']
        destination = root / 'reused-batch8-evidence' / source.relative_to(plan['batch8']['root'])
        put(destination, source.read_bytes())
        assert sha(destination) == binding['sha256']
    h.save(root / 'PROBE_GATE.json', gate)
    h.save(root / 'GIT_SHOW_READS.json', reads)
    config = {'package_commit': package_commit, 'receipt_root': str(root), 'executed_driver': str(executed),
              'driver_sha256': sha(executed), 'plan_sha256': PLAN_SHA, 'normal_target': h.HIGHER,
              'expected_project_dependencies': dependencies, 'probe_gate_sha256': sha(root / 'PROBE_GATE.json'),
              'runtime_binding': runtime_binding(plan), 'sources_installed_by_prepare': False,
              'worker_argv': ['python3', str(executed), '--commit', package_commit,
                              '--receipt-root', str(root), '--worker']}
    h.save(root / 'RUN_CONFIG.json', config)
    git_unchanged(root, config)
    return config


def lane0_worker(config: dict) -> int:
    """Call only inside the existing lane0 serializer. No nested serializer."""
    root = Path(config['receipt_root'])
    assert config == read_json(root / 'RUN_CONFIG.json')
    assert sha(Path(__file__)) == config['driver_sha256']
    assert sha(root / 'inputs' / 'EXECUTION_PLAN.json') == config['plan_sha256'] == PLAN_SHA
    plan = read_json(root / 'inputs' / 'EXECUTION_PLAN.json')
    h, ops = helpers(root, plan)
    directory = root / 'execution' / 'lane-0'
    directory.mkdir(parents=True, exist_ok=True)
    assert sha(root / 'PROBE_GATE.json') == config['probe_gate_sha256']
    assert probe_gate(plan, h) == read_json(root / 'PROBE_GATE.json')
    h.save(directory / 'PROBE_GATE_RECHECK.json', {'actual_cloud_receipts_rechecked': True,
        'gate_sha256': config['probe_gate_sha256'], 'rechecked_utc': h.now()})
    assert runtime_binding(plan) == config['runtime_binding']
    assert dependency_binding(plan, h) == config['expected_project_dependencies']
    h.check_roots()
    current = PROJECT / plan['canonical_path']
    assert sha(current) == plan['source_preimage_sha256'], 'source_not_3bc_preimage_review_existing_work_no_rebuild'
    candidate = (root / 'inputs' / 'candidate.lean').read_bytes()
    assert h.digest(candidate) == plan['candidate_sha256']
    # Record missing ancillary outputs truthfully; do not rebuild a valid old
    # dependency merely to create an unused .c/.ilean. The original no-build
    # guard below remains the authority on import readiness.
    deps_before = {m: source_plus_five(m, False) for m in plan['expected_project_dependencies']}
    roots_before = {m: source_plus_five(m, False) for m in h.FOUR_ROOTS}
    h.save(directory / 'DEPENDENCIES_BEFORE.json', deps_before)
    h.save(directory / 'FOUR_ROOTS_BEFORE.json', roots_before)
    h.save(directory / 'SOURCE_FIVE_BEFORE.json', source_plus_five(h.HIGHER, False))
    ready = ops.run(directory, 'higher-directdeps', h.guard(0,
        ['lake', '--no-build', 'build'] + ['+' + m + ':olean' for m in plan['direct_project_dependencies']]))
    if ready['exit_code']:
        h.save(directory / 'NORMAL_RESULT.json', {'status': 'BLOCKED_DEPENDENCIES_NO_INSTALL_OR_NORMAL',
            'readiness': ready, 'source_installed': False, 'normal_executed': False, 'whole_P1_complete': False})
        return 1
    assert sha(current) == plan['source_preimage_sha256']
    row = {'module': h.HIGHER, 'path': plan['canonical_path'],
           'before_sha256': plan['source_preimage_sha256'], 'after_sha256': plan['candidate_sha256'],
           'cloud_source_mutation_required': True}
    installed = h.install_sources(PROJECT, [row], {plan['canonical_path']: candidate}, root / 'source-backups')
    h.save(root / 'SOURCE_INSTALL.json', {'sources': installed, 'probe_gate_sha256': config['probe_gate_sha256'],
        'protected_roots_after': h.check_roots(), 'original_dirty_git_worktree_not_checked_out': True})
    assert sha(root / 'source-backups' / plan['canonical_path']) == plan['source_preimage_sha256']
    normal = ops.run(directory, 'higher-full-module-normal', h.guard(0, ['lake', 'build', '+' + h.HIGHER + ':olean']))
    after = source_plus_five(h.HIGHER, False)
    h.save(directory / 'SOURCE_FIVE_AFTER.json', after)
    assert sha(current) == plan['candidate_sha256']
    assert dependency_binding(plan, h) == config['expected_project_dependencies']
    assert {m: source_plus_five(m, False) for m in deps_before} == deps_before, 'dependency_artifact_changed'
    assert {m: source_plus_five(m, False) for m in h.FOUR_ROOTS} == roots_before, 'protected_root_artifact_changed'
    assert runtime_binding(plan) == config['runtime_binding'], 'runtime_changed'
    h.check_roots()
    git_unchanged(root, config)
    passed = (normal['exit_code'] == 0 and normal['actual_built_modules'] == [h.HIGHER]
              and not normal['actual_failed_modules'] and all(value is not None for value in after.values()))
    result = {'status': 'PASS_NORMAL_ONLY_PENDING_KERNEL_AND_FULL_OWNED' if passed else 'NORMAL_NOT_ACCEPTED',
              'normal_command': normal, 'direct_dependency_readiness': ready,
              'module': h.HIGHER, 'source_sha256': plan['candidate_sha256'],
              'source_preimage_sha256': plan['source_preimage_sha256'], 'source_plus_five_outputs': after,
              'project_dependency_sources': config['expected_project_dependencies'],
              'project_dependency_artifacts_unchanged': True, 'protected_four_roots_unchanged': True,
              'runtime_guard_serializer_and_state_unchanged': True, 'original_dirty_git_worktree_unchanged': True,
              'all_raw_logs_preserved': True, 'probe_gate_sha256': config['probe_gate_sha256'],
              'low_middle_or_degree6_probe_repeated': False, 'independent_kernel_verified': False,
              'full_owned_audit_verified': False, 'whole_P1_complete': False}
    h.save(directory / 'NORMAL_RESULT.json', result)
    return 0 if passed else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--commit', required=True)
    parser.add_argument('--receipt-root', type=Path)
    parser.add_argument('--worker', action='store_true')
    args = parser.parse_args()
    assert re.fullmatch(r'[0-9a-f]{40}', args.commit)
    if args.worker:
        assert args.receipt_root is not None
        config = read_json(args.receipt_root / 'RUN_CONFIG.json')
        assert config['package_commit'] == args.commit
        return lane0_worker(config)
    config = prepare(args.commit, args.receipt_root)
    root = Path(config['receipt_root'])
    plan = read_json(root / 'inputs' / 'EXECUTION_PLAN.json')
    h, ops = helpers(root, plan)
    directory = root / 'execution' / 'lane-0'
    result = ops.run(directory, 'worker', h.serialize(0, directory / 'VALIDATION_LANE.json',
                     config['worker_argv']), relay=True)
    h.save(root / 'SERIALIZED_WORKER_RESULT.json', result)
    return result['exit_code']


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except Exception as error:
        print(json.dumps({'higher_full': 'STOPPED_WITH_EXCEPTION', 'error_type': type(error).__name__,
                          'error': str(error), 'whole_P1_complete': False}), flush=True)
        traceback.print_exc()
        raise SystemExit(1)
