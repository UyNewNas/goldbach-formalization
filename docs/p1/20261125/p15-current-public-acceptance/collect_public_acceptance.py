#!/usr/bin/env python3
"""Read four fixed P1 acceptance groups; never run Lean, a driver, or a kernel.

Only --group and, for pure2/p3-20, an explicit nonempty --targets subset are accepted.
Missing, unfinished, failed requested owners or stale evidence produce HOLD,
without publishing accepted counts. Successful output contains hashes/counts,
never owned declaration names, private types, or raw command logs.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from types import ModuleType

sys.dont_write_bytecode = True
os.environ['GIT_OPTIONAL_LOCKS'] = '0'
os.environ['GIT_NO_LAZY_FETCH'] = '1'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
OUTPUT = Path('/workspace/p1-complete-proof/20261125-p15-current-public-acceptance-v1')
PROTOTYPE = 'docs/p1/20261125/p15-singleton-proper-power/evidence-initial-four/collect_public_acceptance.py'
PROTOTYPE_COMMIT = 'bbcf75642ec19ebd976820c89011e83351856756'
PROTOTYPE_SHA = 'cd70c392b10cc1a57b7759c4fa16b49be5cc6780a43e814be666f0ee52dec123'
API_COMMIT = '4cea0407c1258eaddd7d4952cffa4aea67310422'
API_SHA = '95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea'
TOOLS = '220c14630ffd266f824bdbf0977147ecb740c0dd'
INTEGRATION_DRIVER = 'docs/p1/20261125/p15-atlas-current-context-integration/run_selected.py'
INTEGRATION_SHA = '81b9e49db7b5c9585f6d5bef12f383898c8a8f8f4ff65786d2cb22e4b3316af0'
INTEGRATION_COMMIT = '418ad4b9a5f2d992871062258a2eefd7fdf4b9ee'
INTEGRATION_ROOT = Path('/workspace/p1-complete-proof/20261125-p15-current-context-integration-v1')
PURE_ROOT = Path('/workspace/p1-complete-proof/20261125-p15-original-atlas-proper-power-v1')
CORE = 'ImbalancedChen.Part3FiniteLambdaOverLogCore'
MELLIN = 'ImbalancedChen.PrimeProductsMellinExactMeanInsertion'
GROUPS = {
    'atlas10': {
        'commit': INTEGRATION_COMMIT, 'driver': INTEGRATION_DRIVER, 'driver_sha256': INTEGRATION_SHA,
        'job': 'job_5f42ad18fde84377987c244daf0b5bfc', 'source_count': 68,
        'manifest': 'docs/p1/20261125/p15-atlas-current-context-integration/ATLAS10_MANIFEST.json',
        'manifest_sha256': '4d8c2a41316590f1cd3103c79faeb412b54923a91bb9537d232252fb5c9a5f3a',
        'targets': ['ImbalancedChen.' + n for n in '''P5OriginalHBMediumChartReserves
P5SmoothChartHBDyadicPartition P5SmoothChartPhysicalHBBranch P5ActualMultiGroupHBChartScale
P5ActualHBChartEventualClosure P5OriginalChartRoughCutoff P5ExactOriginalSmoothDyadicPartition
P5ActualLabelledPrimeSmoothCharts Part3OriginalProperPowerChartCount
Part3ActualOriginalProperPowerChartBridge'''.split()]},
    'p3-20': {
        'commit': INTEGRATION_COMMIT, 'driver': INTEGRATION_DRIVER, 'driver_sha256': INTEGRATION_SHA,
        'job': 'job_41c06d666c6642889cc27d82ee281eb7', 'source_count': 77,
        'manifest': 'docs/p1/20261125/p15-atlas-current-context-integration/P3_20_MANIFEST.json',
        'manifest_sha256': 'f36b834f1e34a8ba98e18f8bab6c149a1de9660c6567d5447339f3c25fbb8b23',
        'targets': ['ImbalancedChen.' + n for n in '''Part3BrunWeights Part3CompletedReciprocalWeil
Part3LongSlotDistribution Part3OffDiagonalModuli Part3OriginalDyadicChartPartition
Part3LongSlotDivisorExpansion Part3SignedModulusPayment Part3SmoothReciprocalWeil
Part3TwoLongCompletion Part3LongSlotBrunTransfer Part3TwoLongBrunComparison Part3TwoLongSmooth
Part3PrimeProductChartTransfer Part3PrimeProductVonMangoldt Part3ProperPrimePowerCount
Part3ProperPowerResidualPayment Part3ProperPowerDyadicBudget Part3ProperPowerOriginalChart
Part3ProperPowerLogSaving Part3ProperPowerChartSum'''.split()]},
    'pure2': {
        'commit': 'ef450be0a89b6a3f88b3bca19d06e04e7967fa18',
        'driver': 'docs/p1/20261125/p15-original-atlas-proper-power/run_selected.py',
        'driver_sha256': '8f18e7d7b00db15ca071e28f6bffdae263fc098df4ccb0156d17fdaa64374fe5',
        'job': 'job_0c98f60f3fbe4aaa8d3e23fcf53dbcb8', 'source_count': 168,
        'manifest': 'docs/p1/20261125/p15-original-atlas-proper-power/SOURCE_CLOSURE.json',
        'manifest_sha256': 'daedcda557fcb12a15da836fd40cdc6d4c1858cb94ef515955725d6313c99701',
        'targets': [CORE, MELLIN]},
    'mellin-current': {
        'commit': '21789da92213323d645122cfcc7dff9c10dc82d6',
        'driver': 'docs/p1/20261125/p15-original-atlas-proper-power/run_selected.py',
        'driver_sha256': '8f18e7d7b00db15ca071e28f6bffdae263fc098df4ccb0156d17fdaa64374fe5',
        'job': 'job_8d58f7741c56448980ca0984ae5c0239', 'source_count': 168,
        'manifest': 'docs/p1/20261125/p15-original-atlas-proper-power/SOURCE_CLOSURE.json',
        'manifest_sha256': 'c1dfff16bd8a758d47f14f5dfbed1ca3c836f657b525ed2afbefbf2605e182ad',
        'targets': [MELLIN]},
}
ALLOWED_AXIOMS = {'Classical.choice', 'Quot.sound', 'propext'}
STAGE = 'arguments'
CURRENT_OWNER = None


def need(ok, code):
    if not ok:
        raise ValueError(code)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def raw(path):
    need(path.is_file() and path.resolve() == path, 'missing_or_nonregular_retained_file')
    return path.read_bytes()


def git_file(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO,
                                   stderr=subprocess.DEVNULL)


def selected(group, requested):
    need(group in GROUPS, 'unknown_fixed_group')
    allowed = GROUPS[group]['targets']
    need(group != 'atlas10' or requested is None, 'atlas_group_requires_its_full_fixed_scope')
    need(group != 'mellin-current' or requested is None, 'mellin_current_requires_its_full_fixed_scope')
    if requested is None:
        return allowed[:]
    need(requested and len(requested) == len(set(requested)) and set(requested) <= set(allowed),
         'invalid_or_empty_fixed_owner_subset')
    return [owner for owner in allowed if owner in requested]


def pure_snapshot(runner, s, commit, graph, sources, owners):
    active = s.h.closure(graph, owners)
    live_graph, live = s.h.project_graph(PROJECT, owners)
    need(active == set(owners) and live_graph == {m: graph[m] for m in active} and
         {m: row['sha256'] for m, row in live.items()} == {m: sources[m] for m in active},
         'selected_pure_live_source_graph_differs')
    protected = {m: runner.file_binding(PROJECT / s.h.module_path(m)) for m in s.h.FOUR_ROOTS}
    need(protected == s.h.FOUR_ROOTS, 'protected_original_roots_changed')
    return {'selected_live_sources': {m: sources[m] for m in sorted(active)},
            'owner_contexts': {m: s.api.context(commit, PROJECT, m, graph, sources, s.h, s.d) for m in owners},
            'owner_outputs': {m: s.d.snapshot(PROJECT, m) for m in owners},
            'protected_roots': protected}


def collect(group, owners):
    global STAGE, CURRENT_OWNER
    fixed = GROUPS[group]
    commit, integration = fixed['commit'], group in ('atlas10', 'p3-20')
    STAGE = 'fixed_published_source_pins'
    need(sha(git_file(PROTOTYPE_COMMIT, PROTOTYPE)) == PROTOTYPE_SHA, 'published_collector_origin_differs')
    code = git_file(commit, fixed['driver'])
    need(sha(code) == fixed['driver_sha256'], 'fixed_driver_source_differs')
    need(sha(git_file(commit, fixed['manifest'])) == fixed['manifest_sha256'], 'fixed_source_manifest_differs')
    runner = ModuleType('fixed_public_acceptance_driver')
    retained_root = INTEGRATION_ROOT / group if integration else PURE_ROOT
    executed_driver = retained_root / commit / 'runs/attempt-00000/executed-driver.py'
    need(raw(executed_driver) == code, 'retained_executed_driver_differs')
    # The P1 checkout may intentionally stay dirty or lack this new path. The
    # job executed this retained published file, not a mutable checkout driver.
    runner.__file__ = str(executed_driver)
    exec(compile(code, runner.__file__, 'exec'), runner.__dict__)
    need((runner.REPO, runner.PROJECT, runner.API_COMMIT, runner.API_SHA, runner.TOOLS) ==
         (REPO, PROJECT, API_COMMIT, API_SHA, TOOLS), 'unchanged_api_or_environment_pin_differs')
    if integration:
        need(runner.ROOT_BASE == INTEGRATION_ROOT and runner.GROUPS[group]['targets'] == fixed['targets'],
             'fixed_integration_target_or_evidence_root_differs')
        runner.ROOT = runner.ROOT_BASE / group  # Exactly the published driver's main setup.
    else:
        need(runner.ROOT == PURE_ROOT and set(owners) <= set(runner.TARGETS), 'fixed_pure_evidence_scope_differs')
    base, bindings = runner.ROOT / commit, {}
    run = base / 'runs/attempt-00000'

    def bind(path):
        data = raw(path)
        value = {'bytes': len(data), 'sha256': sha(data)}
        need(str(path) not in bindings or bindings[str(path)] == value, 'retained_file_changed_during_collection')
        bindings[str(path)] = value
        return value

    STAGE = 'completed_requested_owner_run'
    run_result_binding = bind(run / 'RESULT.json')
    original = json.loads(raw(run / 'RESULT.json'))
    need(original['source_commit'] == commit and original['targets'] and
         len(original['targets']) == len(set(original['targets'])) and
         set(original['targets']) == set(fixed['targets']) and original['whole_P1_complete'] is False,
         'retained_run_source_or_full_scope_differs')
    reported_accepted = original['accepted_owners']
    need(len(reported_accepted) == len(set(reported_accepted)) and
         set(reported_accepted) <= set(fixed['targets']) and set(original['failures']) <= set(fixed['targets']) and
         set(owners) <= set(reported_accepted) and not set(owners).intersection(original['failures']),
         'requested_owner_missing_unfinished_or_failed')
    need(not any(k in original for k in ('context_error', 'final_context_error', 'git_error')),
         'retained_run_context_failure')
    if integration:
        need(original['group'] == group and
             original['acceptance_class'] == 'CURRENT_P1_ENVIRONMENT_INTEGRATION_OF_EXISTING_PROOF_SOURCES' and
             original['new_mathematical_proofs'] == 0 and not original['historical_acceptance_invalidated'],
             'integration_acceptance_class_differs')
    success_key = 'all_selected_integration_owners_accepted' if integration else 'all_selected_owners_accepted'
    if owners == fixed['targets']:
        need(original[success_key] is True and set(reported_accepted) == set(owners) and
             original['failures'] == {} and original['worker_exit_code'] == 0 and
             'dispatch_error' not in original, 'requested_full_group_not_completely_accepted')
    else:
        need(group in ('pure2', 'p3-20'), 'unsupported_partial_group')
        exit_code = original['worker_exit_code']
        need(exit_code in (0, 1) and
             ((exit_code == 0 and 'dispatch_error' not in original and original['failures'] == {} and
               original[success_key] is True and set(reported_accepted) == set(fixed['targets'])) or
              (exit_code == 1 and original.get('dispatch_error') == 'serialized worker exited 1' and
               original[success_key] is False and bool(original['failures']))),
             'partial_run_failure_scope_not_the_recorded_unselected_owner_failure')
    for stem in ('CONTEXT', 'GIT'):
        need(raw(run / (stem + '_BEFORE.json')) == raw(run / (stem + '_AFTER.json')),
             'retained_compile_context_or_git_changed')
        bind(run / (stem + '_BEFORE.json')); bind(run / (stem + '_AFTER.json'))
    need(raw(run / 'executed-driver.py') == code, 'retained_executed_driver_differs')
    bind(run / 'executed-driver.py')
    STAGE = 'historical_source_and_selected_live_context'
    s = runner.helpers()
    git_before = s.d.original_git_state(REPO)
    if integration:
        spec = runner.preflight(s, commit, group, owners)
        graph, sources = spec.graph, spec.sources
        current = lambda: {'source_context': runner.snapshot(s, spec),
                           'selected_target_artifacts': {m: runner.module_artifacts(s, m) for m in owners}}
        baseline = current()
        need(baseline['source_context'] == spec.baseline, 'integration_preflight_context_changed')
    else:
        # Verify all168 Git sources at this pure group's fixed commit, then only
        # its selected live closure. Core keeps its original pure2 identity.
        manifest, graph, sources, manifest_binding = runner.source_manifest(s, commit, owners)
        need(manifest_binding['sha256'] == fixed['manifest_sha256'] and
             all(graph[m] == [] and s.h.imports(git_file(commit, s.h.module_path(m))) == ['Mathlib']
                 for m in owners), 'published_pure_owner_graph_differs')
        current = lambda: pure_snapshot(runner, s, commit, graph, sources, owners)
        baseline = current()
    need(len(graph) == fixed['source_count'], 'published_source_graph_count_differs')

    def command_summary(command, receipt, log, operation, modules):
        need(sha(raw(log)) == command['log_sha256'], 'retained_command_log_hash_differs')
        return {'operation': operation, 'guard_lane': 0, 'modules': modules,
                'exit_code': command['exit_code'],
                'argv_sha256': sha(json.dumps(command['argv'], separators=(',', ':')).encode()),
                'command_receipt': bind(receipt), 'log': bind(log)}

    worker_path = run / 'serialized-worker-command.json'
    worker = json.loads(raw(worker_path))
    child = ['python3', '-B', str(run / 'executed-driver.py'), '--source-commit', commit]
    if integration:
        child += ['--group', group]
    child += ['--targets', *fixed['targets'], '--run', '--inside-lane', str(run)]
    need(worker['exit_code'] == original['worker_exit_code'] and
         worker['argv'] == s.h.serialize(0, run / 'VALIDATION_LANE.json', child),
         'retained_serialized_worker_command_scope_differs')
    worker_summary = command_summary(worker, worker_path, Path(worker['log']),
                                      'original_serialized_group_worker_not_reexecuted', fixed['targets'])

    observed_axioms, results = set(), {}
    for owner in owners:
        CURRENT_OWNER, STAGE = owner, 'original_full_audit_valid'
        folder = base / owner
        normal_path = folder / 'normal' / owner / 'NORMAL_PASS.json'
        paths = list((folder / 'audits').glob('*/lane-0/VALIDATION_RESULTS.json'))
        need(len(paths) == 1, 'ambiguous_or_missing_retained_owner_audit')
        result_path = paths[0]
        audit = result_path.parent.parent
        need(re.fullmatch('[0-9a-f]{20}', audit.name), 'unexpected_retained_audit_path')
        lane, plan_path = audit / 'lane-0', audit / 'AUDIT_PLAN.json'
        normal, plan = json.loads(raw(normal_path)), json.loads(raw(plan_path))
        accepted = s.api.audit_valid(commit, runner.PROJECT, audit, plan, {owner: normal},
                                     graph, sources, s.h, s.d)
        need(accepted == {owner}, 'retained_full_audit_owner_scope_differs')
        result = json.loads(raw(result_path))
        exports = json.loads(raw(lane / 'OWNED_EXPORTS.json'))
        axioms = {a for entry in exports for a in entry['axioms']}
        need(axioms <= ALLOWED_AXIOMS and all(entry['kind'] != 'axiom' for entry in exports),
             'unexpected_owned_axiom')
        observed_axioms |= axioms
        refs = {'normal': normal_path, 'audit_plan': plan_path, 'audit_result': result_path,
                'reused_normal_evidence': lane / 'REUSED_NORMAL_EVIDENCE.json',
                'owned_exports': lane / 'OWNED_EXPORTS.json', 'owned_log': lane / 'all-owned-types-axioms.log'}
        commands = {'normal': command_summary(normal['normal_command'],
                    Path(normal['normal_command']['command_receipt']), Path(normal['normal_command']['log']),
                    'normal_build_exactly_one_owner', [owner])}
        for key, command in [('stock_before', result['stock_readiness_before']),
                             ('named_kernel', result['kernel_commands'][owner]),
                             ('full_owned', result['audit_command']),
                             ('stock_after', result['stock_readiness_after'])]:
            log = lane / command['log']
            need(log.is_relative_to(lane), 'audit_log_outside_fixed_lane')
            commands[key] = command_summary(command, log.with_name(log.stem + '-command.json'), log,
                                            {'named_kernel': 'named_owner_kernel_replay',
                                             'full_owned': 'complete_environment_owned_types_and_axioms'}.get(
                                                key, 'stock_readiness_no_build'), [owner])
        results[owner] = {'source_commit': commit, 'source_sha256': sources[owner],
            'status': result['status'], 'receipt_bindings': {k: bind(p) for k, p in refs.items()},
            'owned_count': result['total_owned_exports'], 'public_count': result['total_public_exports'],
            'commands': commands, 'observed_axioms': sorted(axioms)}
    CURRENT_OWNER, STAGE = None, 'final_read_only_context_and_receipt_checks'
    need(current() == baseline, 'selected_live_context_changed_during_collection')
    need(s.d.original_git_state(REPO) == git_before, 'current_git_metadata_changed')
    for path, expected in list(bindings.items()):
        need(bind(Path(path)) == expected, 'retained_receipt_changed')
    summary = {
        'schema': 'p15_fixed_current_acceptance_public_summary_v1', 'status': 'REQUESTED_OWNERS_FULLY_REVALIDATED',
        'repository': 'UyNewNas/goldbach-formalization', 'group': group, 'source_commit': commit,
        'compiler_job': fixed['job'], 'compiler_job_binding': 'Fixed parent-observed task identity; retained run binds source and scope.',
        'acceptance_class': ('CURRENT_P1_ENVIRONMENT_INTEGRATION_OF_EXISTING_PROOF_SOURCES' if integration
                             else 'NEW_PHASE2_MATHEMATICAL_OWNER_ACCEPTANCE'),
        'collector_sha256': sha(Path(__file__).read_bytes()), 'prototype_sha256': PROTOTYPE_SHA,
        'unchanged_driver_sha256': fixed['driver_sha256'], 'unchanged_api_sha256': API_SHA,
        'original_result': run_result_binding, 'requested_owners': owners,
        'original_worker_command': worker_summary,
        'original_run_scope': {'targets': original['targets'], 'reported_accepted_owners': reported_accepted,
            'reported_failed_owners': sorted(original['failures']), 'worker_exit_code': original['worker_exit_code'],
            'reported_not_accepted_owners': sorted(set(fixed['targets']) - set(reported_accepted)),
            'all_original_targets_accepted': original['all_selected_integration_owners_accepted'] if integration
                                           else original['all_selected_owners_accepted']},
        'owners': results, 'accepted_requested_owner_count': len(results),
        'owned_count': sum(r['owned_count'] for r in results.values()),
        'public_count': sum(r['public_count'] for r in results.values()), 'observed_axioms': sorted(observed_axioms),
        'full_published_source_graph_count': len(graph),
        'selected_live_source_closure_count': len(s.h.closure(graph, owners)),
        'full_published_graph_verified_from_fixed_Git_commit': True,
        'full_published_graph_claimed_equal_to_current_live_graph': integration,
        'normal_kernel_full_owned_receipts_revalidated_without_execution': True,
        'retained_compile_context_and_git_unchanged': True,
        'selected_live_source_runtime_outputs_and_dependency_context_unchanged': True,
        'current_git_metadata_unchanged': True, 'historical_acceptance_invalidated': False,
        'new_mathematical_proofs_developed_by_collector': 0, 'Lean_or_kernel_commands_executed': 0,
        'dependency_rebuilds_requested': False, 'raw_logs_or_private_declarations_exported': False,
        'whole_P1_complete': False, 'whole_P1_5_complete': False}
    encoded = (json.dumps(summary, sort_keys=True, separators=(',', ':')) + '\n').encode()
    subset = ('all' if owners == fixed['targets'] else 'core' if owners == [CORE] else
              'mellin' if owners == [MELLIN] else 'selected-' + sha(json.dumps(owners).encode())[:12])
    output = OUTPUT / (group + '-' + commit + '-' + subset + '.json')
    output.parent.mkdir(parents=True, exist_ok=True)
    if output.exists():
        need(raw(output) == encoded, 'existing_public_summary_differs')
    else:
        with output.open('xb') as stream:
            stream.write(encoded)
    print('PUBLIC_ACCEPTANCE_SUMMARY ' + encoded.decode().strip())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--group', required=True, choices=tuple(GROUPS))
    parser.add_argument('--targets', nargs='+', help='pure2/p3-20 only; an explicit nonempty subset of that fixed whitelist')
    args = parser.parse_args()
    try:
        collect(args.group, selected(args.group, args.targets))
    except Exception as error:
        # No exception text or traceback: validators can read private audit data.
        print('PUBLIC_ACCEPTANCE_HOLD ' + json.dumps({'status': 'HOLD', 'group': args.group,
              'source_commit': GROUPS[args.group]['commit'], 'stage': STAGE,
              'requested_owner_at_failure': CURRENT_OWNER, 'error_type': type(error).__name__,
              'accepted_counts_emitted': False, 'new_Lean_acceptance_claimed': False,
              'whole_P1_5_complete': False}, sort_keys=True, separators=(',', ':')))
        return 2
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
