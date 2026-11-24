#!/usr/bin/env python3
"""Compile only new repair candidates and new probes; audit eight existing builds.

The exact previous helper and acceptance runner remain authoritative. Installation
is source-hash guarded and happens before both established lanes start. The
already accepted 90 + 24 modules and degree-six probe are never scheduled.
"""
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
import time
import traceback

PROJECT = Path('/workspace/blue-member-build')
GIT = Path('/workspace/goldbach-formalization')
ROOT = Path('/workspace/p1-complete-proof/20261124-resume/batch7-repairs-probes-next8')
PREFIX = 'docs/p1/20261124/'
HELPER_PATH = PREFIX + 'batch5-parallel/run_batch5_parallel.py'
HELPER_SHA = '1d166b6a36362e185559ea08a82100a49ba9edbeefcb98b1a904b9ff9330cbd5'
OPS_PATH = PREFIX + 'batch6-parallel/run_batch6_parallel.py'
OPS_SHA = 'e1338ef756fba98b126bb089413f2c489ed4de8682a61c11dfb8e61c8e518d11'
RUNNER_PATH = PREFIX + 'normal-supplement-audit/run_parallel_acceptance_multibatch.py'
RUNNER_SHA = 'e9dadb4ee5cd0a9ad50e298a77c6133fe5e0d012f8b194ae02bd5118460fc9e1'
AUDIT_PATH = PREFIX + 'next8-rowmodulus-rebound/AUDIT_PLAN.json'
AUDIT_SHA = 'eadf25801c129e3b055e472cca0d372666f97140097031c12c1986ad682db920'
PLAN_PATH = PREFIX + 'batch7-parallel/EXECUTION_PLAN.json'


def sha(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def emit(stage, **fields):
    print(json.dumps({'batch7': stage, **fields}, ensure_ascii=False), flush=True)


def load_module(name, path, expected):
    assert sha(path) == expected, ('helper_hash', str(path))
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def helpers():
    h = load_module('batch5_exact_helpers', ROOT / 'inputs' / 'batch5_helpers.py', HELPER_SHA)
    ops = load_module('batch6_exact_operations', ROOT / 'inputs' / 'batch6_operations.py', OPS_SHA)
    # Preserve the inherited batch6 progress label as well as run(),
    # diagnostics() and relay matching; the receipt directory identifies batch7.
    assert h.PROJECT == ops.PROJECT == PROJECT
    return h, ops


def worker(config, lane):
    h, ops = helpers()
    assert sha(Path(__file__)) == config['driver_sha256']
    plan = json.loads((ROOT / 'inputs' / 'EXECUTION_PLAN.json').read_bytes())
    assert sha(ROOT / 'inputs' / 'EXECUTION_PLAN.json') == config['plan_sha256']
    directory = ROOT / 'execution' / ('lane-' + str(lane))
    results = []
    if lane == 0:
        deps = config['probe_direct_project_dependencies']
        ready = ops.run(directory, 'higher-new-probes-directdeps', h.guard(0,
            ['lake', '--no-build', 'build'] + ['+' + m + ':olean' for m in deps]))
        results.append(ready)
        if ready['exit_code'] == 0:
            for probe in plan['higher_probes_in_conditional_order']:
                path = ROOT / 'inputs' / 'probes' / Path(probe['path']).name
                assert sha(path) == probe['sha256']
                result = ops.run(directory, probe['name'], h.guard(0, [
                    'lake', 'env', 'lean', '-DmaxRecDepth=100000',
                    '-DmaxHeartbeats=4000000', '--root=' + str(path.parent), str(path)]))
                results.append(result)
                if result['exit_code']:
                    break
        h.save(directory / 'PROBE_RESULTS.json', {
            'stages': results, 'old_passed_degree6_probe_repeated': False,
            'higher_full_module_candidate_installed': False,
            'higher_full_module_complete': False, 'whole_P1_complete': False})
    else:
        if config['audit_preparation_exit_code'] == 0:
            audit_root = Path(config['audit_receipt_root'])
            results.append(ops.run(directory, 'next8-rowmodulus-rebound-full-audit', [
                'python3', config['audit_runner'], '--plan', str(audit_root / 'AUDIT_PLAN.json'),
                '--receipt-root', str(audit_root), '--lane', '1']))
        else:
            results.append({'stage': 'AUDIT_PREPARATION_FAILED',
                            'exit_code': config['audit_preparation_exit_code']})
        for group in plan['normal_groups']:
            name, targets = group['name'], group['targets']
            deps = sorted({d for m in targets for d in config['graph'][m]})
            ready = ops.run(directory, name + '-directdeps', h.guard(1,
                ['lake', '--no-build', 'build'] + ['+' + m + ':olean' for m in deps]))
            results.append(ready)
            if ready['exit_code']:
                continue
            for m in targets:
                assert sha(PROJECT / h.module_path(m)) == config['normal_sources'][m]
            result = ops.run(directory, name, h.guard(1,
                ['lake', 'build'] + ['+' + m + ':olean' for m in targets]))
            result['unexpected_built_modules'] = sorted(set(result['actual_built_modules']) - set(targets))
            results.append(result)
            h.save(directory / (name + '-BUILD_SCOPE.json'), {
                'requested': targets, 'built': result['actual_built_modules'],
                'failed': result['actual_failed_modules'],
                'unexpected': result['unexpected_built_modules'],
                'normal_requires_separate_kernel_and_owned_audit': True})
        h.save(directory / 'LANE_RESULT.json', {
            'stages': results, 'audit_failure_does_not_suppress_independent_normal': True,
            'already_accepted90_and24_repeated': False, 'whole_P1_complete': False})
    return 0 if all(x['exit_code'] == 0 and not x.get('unexpected_built_modules')
                    for x in results) else 1


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
        with destination.open('xb') as stream:
            stream.write(data)
        reads.append({'argv': argv, 'exit_code': 0, 'path': str(destination),
                      'sha256': digest, 'bytes': len(data)})
        return data

    extract(HELPER_PATH, inputs / 'batch5_helpers.py', HELPER_SHA)
    extract(OPS_PATH, inputs / 'batch6_operations.py', OPS_SHA)
    h, ops = helpers()
    plan = json.loads(extract(PLAN_PATH, inputs / 'EXECUTION_PLAN.json'))
    assert plan['baseline_commit'] == '01f5bcc251cadb8d8548eef9b65c63b4b923723b'
    audit = json.loads(extract(AUDIT_PATH, inputs / 'AUDIT_PLAN.json', AUDIT_SHA))
    runner = inputs / 'run_parallel_acceptance_multibatch.py'
    extract(RUNNER_PATH, runner, RUNNER_SHA)
    assert audit['project'] == str(PROJECT)
    assert audit['runtime_states'] == [str(x) for x in h.STATES]
    assert audit['lanes'][0]['modules'] == [] and len(audit['lanes'][1]['modules']) == 8
    audit_targets = audit['lanes'][1]['modules']
    assert set(audit_targets) == set(audit['modules'])
    normal = [m for g in plan['normal_groups'] for m in g['targets']]
    assert len(normal) == len(set(normal)) == 10
    assert h.HIGHER not in normal
    update = json.loads(extract(PREFIX + 'batch7-repairs/SOURCE_UPDATE.json', inputs / 'SOURCE_UPDATE.json'))
    assert len(update['updates']) == 11
    assert {x['module'] for x in update['updates'] if x['cloud_source_mutation_required']} == set(normal)
    payloads = {x['path']: extract(x['path'], inputs / 'sources' / x['path'], x['after_sha256'])
                for x in update['updates']}
    probe_deps = set()
    for probe in plan['higher_probes_in_conditional_order']:
        data = extract(probe['path'], inputs / 'probes' / Path(probe['path']).name, probe['sha256'])
        probe_deps.update(m for m in h.imports(data) if m.startswith('ImbalancedChen.'))
    h.check_roots()
    installed = h.install_sources(PROJECT, update['updates'], payloads, ROOT / 'source-backups')
    h.save(ROOT / 'SOURCE_INSTALL.json', {'commit': commit, 'sources': installed,
        'protected_roots': h.check_roots(), 'higher_full_candidate_not_installed': True})
    graph, sources = h.project_graph(PROJECT, normal + audit_targets + sorted(probe_deps))
    assert not set(normal) & h.closure(graph, audit_targets)
    assert not set(normal) & h.closure(graph, sorted(probe_deps))
    for m in normal:
        assert not (set(normal) - {m}) & h.closure(graph, [m]), ('normal_target_has_other_normal_ancestor', m)
    h.save(ROOT / 'PROJECT_SOURCE_CONTEXT.json', sources)
    h.save(ROOT / 'GIT_SHOW_READS.json', reads)
    preparation = ops.run(ROOT, 'next8-prepare-only', [
        'python3', str(runner), '--plan', str(inputs / 'AUDIT_PLAN.json'), '--prepare-only'])
    config = {'commit': commit, 'driver_sha256': sha(executed),
        'plan_sha256': sha(inputs / 'EXECUTION_PLAN.json'), 'graph': graph,
        'normal_sources': {m: sources[m]['sha256'] for m in normal},
        'probe_direct_project_dependencies': sorted(probe_deps),
        'audit_preparation_exit_code': preparation['exit_code'],
        'audit_runner': str(runner), 'audit_receipt_root': audit['receipt_root']}
    h.save(ROOT / 'RUN_CONFIG.json', config)

    def launch(lane):
        directory = ROOT / 'execution' / ('lane-' + str(lane))
        directory.mkdir(parents=True, exist_ok=True)
        return ops.run(directory, 'worker', h.serialize(lane, directory / 'VALIDATION_LANE.json', [
            'python3', str(executed), '--commit', commit, '--worker', '--lane', str(lane)]), relay=True)

    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
        lanes = list(pool.map(launch, [0, 1]))
    assert {m: sha(PROJECT / h.module_path(m)) for m in sources} == {m: x['sha256'] for m, x in sources.items()}
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=GIT) == original_head
    assert subprocess.check_output(['git', 'status', '--porcelain=v1', '-z'], cwd=GIT) == original_status
    h.save(ROOT / 'BATCH7_RESULT.json', {
        'commit': commit, 'lane_commands': lanes, 'protected_roots': h.check_roots(),
        'all_context_sources_unchanged_during_execution': True,
        'original_dirty_git_worktree_unchanged': True,
        'higher_full_module_candidate_installed': False,
        'normal_requires_separate_kernel_and_owned_audit': True,
        'already_accepted90_and24_repeated': False,
        'old_degree6_probe_repeated': False, 'whole_P1_complete': False})
    emit('RESULT', lane_exit_codes=[x['exit_code'] for x in lanes], receipt=str(ROOT / 'BATCH7_RESULT.json'))
    return 0 if all(x['exit_code'] == 0 for x in lanes) else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--commit', required=True)
    parser.add_argument('--worker', action='store_true')
    parser.add_argument('--lane', type=int, choices=[0, 1])
    args = parser.parse_args()
    assert re.fullmatch(r'[0-9a-f]{40}', args.commit)
    sys.setrecursionlimit(10000)
    if args.worker:
        config = json.loads((ROOT / 'RUN_CONFIG.json').read_bytes())
        assert config['commit'] == args.commit and args.lane is not None
        return worker(config, args.lane)
    assert args.lane is None
    return coordinator(args.commit)


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except Exception as error:
        emit('EXCEPTION', error_type=type(error).__name__, error=str(error), whole_P1_complete=False)
        traceback.print_exc()
        raise SystemExit(1)
