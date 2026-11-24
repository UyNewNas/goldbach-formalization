#!/usr/bin/env python3
"""Run the gated complete Higher proof beside existing-build audits and new leaves."""
from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import traceback

PROJECT = Path('/workspace/blue-member-build')
GIT = Path('/workspace/goldbach-formalization')
ROOT = Path('/workspace/p1-complete-proof/20261124-resume/batch9-higher-full-and-frontier')
PREFIX = 'docs/p1/20261124/'
PLAN_PATH = PREFIX + 'batch9-parallel/EXECUTION_PLAN.json'
HELPER_PATH = PREFIX + 'batch5-parallel/run_batch5_parallel.py'
HELPER_SHA = '1d166b6a36362e185559ea08a82100a49ba9edbeefcb98b1a904b9ff9330cbd5'
OPS_PATH = PREFIX + 'batch6-parallel/run_batch6_parallel.py'
OPS_SHA = 'e1338ef756fba98b126bb089413f2c489ed4de8682a61c11dfb8e61c8e518d11'
RUNNER_PATH = PREFIX + 'normal-supplement-audit/run_parallel_acceptance_multibatch.py'
RUNNER_SHA = 'e9dadb4ee5cd0a9ad50e298a77c6133fe5e0d012f8b194ae02bd5118460fc9e1'
HIGHER_BEFORE = '3bc124a836f6637bdb8fd8448a3c76d1ed313756022329221ffa1268838b010d'
HIGHER_AFTER = 'a9a4e532991af5ba3b397b7381fd4a1fdf3302ee25ef27a16ebba04e68a68334'


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def emit(stage, **fields):
    print(json.dumps({'batch9': stage, **fields}, ensure_ascii=False), flush=True)


def module(name, path, expected):
    assert sha(path) == expected, ('helper_hash', str(path))
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def helpers():
    h = module('batch9_exact_helper', ROOT / 'inputs/batch5_helpers.py', HELPER_SHA)
    ops = module('batch9_exact_ops', ROOT / 'inputs/batch6_operations.py', OPS_SHA)
    assert h.PROJECT == ops.PROJECT == PROJECT
    return h, ops


def normal_worker(config):
    h, ops = helpers()
    assert sha(Path(__file__)) == config['driver_sha256']
    plan_file = ROOT / 'inputs/EXECUTION_PLAN.json'
    assert sha(plan_file) == config['plan_sha256']
    plan = json.loads(plan_file.read_bytes())
    directory = ROOT / 'execution/lane-1'
    results = []
    if config['audit_preparation_exit_code'] == 0:
        audit = Path(config['audit_receipt_root'])
        results.append(ops.run(directory, 'existing-normal-full-audit', [
            'python3', config['audit_runner'], '--plan', str(audit / 'AUDIT_PLAN.json'),
            '--receipt-root', str(audit), '--lane', '1']))
    else:
        results.append({'stage': 'AUDIT_PREPARATION_FAILED',
                        'exit_code': config['audit_preparation_exit_code']})
    for group in plan['normal_groups']:
        name = group['name']
        targets = [m for m in group['targets'] if m in config['normal_sources']]
        if not targets:
            h.save(directory / (name + '-SKIPPED.json'), {
                'reason': 'NO_EXACT_SOURCE_MATCH', 'requested': group['targets']})
            continue
        dependencies = sorted({d for m in targets for d in config['graph'][m]})
        assert dependencies, ('empty_direct_dependency_gate', name)
        ready = ops.run(directory, name + '-directdeps', h.guard(1, [
            'lake', '--no-build', 'build'] + ['+' + m + ':olean' for m in dependencies]))
        results.append(ready)
        if ready['exit_code'] == 3:
            # A stale dependency in one leaf must not suppress independent
            # siblings. Only this observed failure triggers finer read-only gates.
            eligible = []
            for m in targets:
                deps = config['graph'][m]
                assert deps, ('empty_individual_dependency_gate', m)
                check = ops.run(directory, name + '-directdeps-' + m.rsplit('.', 1)[-1],
                    h.guard(1, ['lake', '--no-build', 'build'] +
                            ['+' + d + ':olean' for d in sorted(set(deps))]))
                results.append(check)
                if check['exit_code'] == 0:
                    eligible.append(m)
            targets = eligible
        elif ready['exit_code']:
            continue
        if not targets:
            continue
        for name_ in config['normal_dependency_closure']:
            assert sha(PROJECT / h.module_path(name_)) == config['sources'][name_]['sha256']
        for m in targets:
            assert sha(PROJECT / h.module_path(m)) == config['normal_sources'][m]
        result = ops.run(directory, name, h.guard(1,
            ['lake', 'build'] + ['+' + m + ':olean' for m in targets]))
        unexpected = sorted(set(result['actual_built_modules']) - set(targets))
        result['unexpected_built_modules'] = unexpected
        results.append(result)
        h.save(directory / (name + '-BUILD_SCOPE.json'), {
            'group_requested': group['targets'], 'requested': targets,
            'built': result['actual_built_modules'],
            'failed': result['actual_failed_modules'], 'unexpected': unexpected,
            'normal_requires_separate_kernel_and_owned_audit': True})
    h.save(directory / 'LANE_RESULT.json', {
        'stages': results, 'audit_failure_does_not_suppress_independent_normal': True,
        'skipped_source_mismatch_modules': config['source_mismatch_modules'],
        'whole_P1_complete': False})
    return 0 if not config['source_mismatch_modules'] and all(
        r['exit_code'] == 0 and not r.get('unexpected_built_modules') for r in results) else 1


def coordinator(commit):
    ROOT.mkdir(exist_ok=False)
    inputs = ROOT / 'inputs'
    inputs.mkdir()
    executed = ROOT / 'executed-driver.py'
    executed.write_bytes(Path(__file__).read_bytes())
    original_head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=GIT)
    original_status = subprocess.check_output(['git', 'status', '--porcelain=v1', '-z'], cwd=GIT)
    (ROOT / 'original-git-status-before.bin').write_bytes(original_status)
    subprocess.run(['git', 'fetch', 'origin', 'codex/p1-final-acceptance-20261124'], cwd=GIT, check=True)
    subprocess.run(['git', 'merge-base', '--is-ancestor', commit, 'FETCH_HEAD'], cwd=GIT, check=True)
    reads = []

    def extract(rel, destination, expected=None):
        argv = ['git', 'show', commit + ':' + rel]
        data = subprocess.check_output(argv, cwd=GIT)
        digest = hashlib.sha256(data).hexdigest()
        if expected is not None:
            assert digest == expected, ('published_file', rel)
        destination.parent.mkdir(parents=True, exist_ok=True)
        with destination.open('xb') as output:
            output.write(data)
        reads.append({'argv': argv, 'exit_code': 0, 'path': str(destination),
                      'sha256': digest, 'bytes': len(data)})
        return data

    extract(HELPER_PATH, inputs / 'batch5_helpers.py', HELPER_SHA)
    extract(OPS_PATH, inputs / 'batch6_operations.py', OPS_SHA)
    h, ops = helpers()
    plan = json.loads(extract(PLAN_PATH, inputs / 'EXECUTION_PLAN.json'))
    assert plan['higher_after_sha256'] == HIGHER_AFTER
    for key in ('audit_plan_sha256', 'source_update_sha256', 'higher_driver_sha256'):
        assert re.fullmatch(r'[0-9a-f]{64}', plan[key]), ('unfrozen_input', key)
    audit = json.loads(extract(plan['audit_plan_path'], inputs / 'AUDIT_PLAN.json',
                               plan['audit_plan_sha256']))
    runner = inputs / 'run_parallel_acceptance_multibatch.py'
    extract(RUNNER_PATH, runner, RUNNER_SHA)
    assert audit['project'] == str(PROJECT)
    assert audit['runtime_states'] == [str(s) for s in h.STATES]
    assert [v['id'] for v in audit['lanes']] == [0, 1]
    assert audit['lanes'][0]['modules'] == []
    audit_targets = audit['lanes'][1]['modules']
    assert set(audit_targets) == set(audit['modules'])
    assert len(audit_targets) == plan['audit_module_count']
    normal = [m for group in plan['normal_groups'] for m in group['targets']]
    assert len(normal) == len(set(normal)) == plan['normal_module_count']
    assert not set(normal) & (set(audit_targets) | set(audit['reused_complete_modules']))
    assert h.HIGHER not in normal + audit_targets
    update = json.loads(extract(plan['source_update_path'], inputs / 'SOURCE_UPDATE.json',
                                plan['source_update_sha256']))
    assert {row['module'] for row in update['updates']} <= set(normal)
    payloads = {row['path']: extract(row['path'], inputs / 'sources' / row['path'],
                                    row['after_sha256']) for row in update['updates']}
    # Check all source-write intersections before installing any ordinary donor.
    graph_before, before = h.project_graph(PROJECT, normal + audit_targets + [h.HIGHER])
    for row in update['updates']:
        imports = [m for m in h.imports(payloads[row['path']]) if m.startswith('ImbalancedChen.')]
        assert imports == graph_before[row['module']], ('donor_imports_changed', row['module'])
    normal_set = set(normal)
    assert not normal_set & h.closure(graph_before, audit_targets)
    assert not normal_set & h.closure(graph_before, [h.HIGHER])
    assert h.HIGHER not in h.closure(graph_before, normal + audit_targets)
    for m in normal:
        assert not (normal_set - {m}) & h.closure(graph_before, [m]), ('normal_target_has_normal_ancestor', m)
    h.check_roots()
    assert before[h.HIGHER]['sha256'] == HIGHER_BEFORE
    installed = h.install_sources(PROJECT, update['updates'], payloads, ROOT / 'source-backups')
    h.save(ROOT / 'SOURCE_INSTALL.json', {'commit': commit, 'sources': installed,
                                         'protected_roots': h.check_roots()})
    graph, sources = h.project_graph(PROJECT, normal + audit_targets + [h.HIGHER])
    expected_audit = audit['expected_project_sources']
    assert set(expected_audit) == h.closure(graph, audit_targets)
    assert {m: sources[m]['sha256'] for m in expected_audit} == expected_audit
    matched, mismatches = {}, []
    for m in normal:
        expected = plan['normal_sources'][m]['sha256']
        if sources[m]['sha256'] == expected:
            matched[m] = expected
        else:
            p = ROOT / 'source-mismatches' / h.module_path(m)
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes((PROJECT / h.module_path(m)).read_bytes())
            mismatches.append(m)
            emit('SOURCE_MISMATCH', module=m, actual_sha256=sources[m]['sha256'],
                 expected_sha256=expected, action='SKIP_NO_SOURCE_OVERWRITE')
    h.save(ROOT / 'PROJECT_SOURCE_CONTEXT.json', sources)
    higher_driver = inputs / 'run_higher_full_after_batch8.py'
    extract(plan['higher_driver_path'], higher_driver, plan['higher_driver_sha256'])
    higher = module('batch9_gated_higher_driver', higher_driver, plan['higher_driver_sha256'])
    higher_config = higher.prepare(commit, ROOT / 'higher')
    assert higher_config['normal_target'] == h.HIGHER
    preparation = ops.run(ROOT, 'existing-normal-audit-prepare-only', [
        'python3', str(runner), '--plan', str(inputs / 'AUDIT_PLAN.json'), '--prepare-only'])
    config = {'commit': commit, 'driver_sha256': sha(executed),
        'plan_sha256': sha(inputs / 'EXECUTION_PLAN.json'), 'graph': graph, 'sources': sources,
        'normal_sources': matched, 'source_mismatch_modules': mismatches,
        'normal_dependency_closure': sorted(h.closure(graph, normal)),
        'audit_preparation_exit_code': preparation['exit_code'],
        'audit_runner': str(runner), 'audit_receipt_root': audit['receipt_root'],
        'higher_config': higher_config}
    h.save(ROOT / 'RUN_CONFIG.json', config)
    h.save(ROOT / 'GIT_SHOW_READS.json', reads)

    def launch(lane):
        directory = ROOT / 'execution' / ('lane-' + str(lane))
        directory.mkdir(parents=True, exist_ok=True)
        argv = higher_config['worker_argv'] if lane == 0 else [
            'python3', str(executed), '--commit', commit, '--normal-worker']
        return ops.run(directory, 'worker', h.serialize(lane, directory / 'VALIDATION_LANE.json', argv), relay=True)

    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        lanes = list(pool.map(launch, [0, 1]))
    for m in sources:
        if m != h.HIGHER:
            assert sha(PROJECT / h.module_path(m)) == sources[m]['sha256']
    actual_higher = sha(PROJECT / h.module_path(h.HIGHER))
    assert actual_higher in {HIGHER_BEFORE, HIGHER_AFTER}
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=GIT) == original_head
    assert subprocess.check_output(['git', 'status', '--porcelain=v1', '-z'], cwd=GIT) == original_status
    h.save(ROOT / 'BATCH9_RESULT.json', {
        'commit': commit, 'lane_commands': lanes, 'protected_roots': h.check_roots(),
        'all_other_context_sources_unchanged_during_execution': True,
        'higher_actual_source_sha256': actual_higher,
        'original_dirty_git_worktree_unchanged': True,
        'normal_requires_separate_kernel_and_owned_audit': True,
        'probe_and_previous_complete_audits_repeated': False, 'whole_P1_complete': False})
    emit('RESULT', lane_exit_codes=[r['exit_code'] for r in lanes], receipt=str(ROOT / 'BATCH9_RESULT.json'))
    return 0 if all(r['exit_code'] == 0 for r in lanes) else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--commit', required=True)
    parser.add_argument('--normal-worker', action='store_true')
    args = parser.parse_args()
    assert re.fullmatch(r'[0-9a-f]{40}', args.commit)
    sys.setrecursionlimit(10000)
    if args.normal_worker:
        config = json.loads((ROOT / 'RUN_CONFIG.json').read_bytes())
        assert config['commit'] == args.commit
        return normal_worker(config)
    return coordinator(args.commit)


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except Exception as error:
        emit('EXCEPTION', error_type=type(error).__name__, error=str(error), whole_P1_complete=False)
        traceback.print_exc()
        raise SystemExit(1)
