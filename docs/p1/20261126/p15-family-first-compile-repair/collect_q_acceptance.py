#!/usr/bin/env python3
"""Read the two frozen Q runs and revalidate their two accepted owners, without execution."""
from pathlib import Path
from types import ModuleType
import hashlib
import json
import os
import subprocess
import sys

sys.dont_write_bytecode = True
Q = '445201674271f9d9d6b846ecc634a10c4a0c6043'
P = 'b45d33fc0f8e2b2ac97a5919d5c7af120f11fa9f'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
DRIVER_FP = {'bytes': 101219, 'sha256': 'c168664e6350f79a77c7b07d22db09167ac9a3906b18a251c4c308b773cfbce5'}
MANIFEST_FP = {'bytes': 342103, 'sha256': 'b37216a0928fbd7ebb0c14ff4cb51dfbfda568cd1d606db61966417dbb5077a6'}
RUN_PINS = [
    {'RESULT.json': {'bytes': 33421, 'sha256': '1d53e27318da9580b417ae8bc3925d31b23a043f82d3c52e611b3bb3ad824362'},
     'WORKER_RESULT.json': {'bytes': 33356, 'sha256': '007d6ed0cfc78c08669dd616ac9b428b88e43efbd7e137bdda1e83bdc247c625'}},
    {'RESULT.json': {'bytes': 47299, 'sha256': '4edbb82b0d72d025a415a7d9f532112c80b7bae7d4f7279c5514900ea56450ec'},
     'WORKER_RESULT.json': {'bytes': 47183, 'sha256': '1cfc84b483e31ed1f500b2e56ac4fb9dbbd60187f40ac5603f7c0892dcccf2db'}},
]
ALLK = 'ImbalancedChen.Part3AllKLambdaChartCorrection'
ADMISSIBLE = 'ImbalancedChen.P5AdmissibleAllRankIntegerGeometricFamily'
FAMILY = 'ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound'
ACCEPTED = [ALLK, ADMISSIBLE]
REMAINING = [ALLK, ADMISSIBLE, FAMILY,
    'ImbalancedChen.P5IndependentPrimeSourceWordDictionary',
    'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy',
    'ImbalancedChen.P1OriginalSingletonSmoothLicence',
    'ImbalancedChen.P5OriginalPrimeEndpointLogPayment',
    'ImbalancedChen.P5PrimeDivisorMeanCorrection',
    'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
    'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
    'ImbalancedChen.P1OriginalSingletonAtlasTrim',
    'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
    'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime']
JOBS = ['job_f7f42e3d3b7249cd8b60d383ce69a869', 'job_7b6961dd4ada4d1e82ed170a66eee311']
AUDITS = {ALLK: '14d74f4877522c8c50f1', ADMISSIBLE: 'ee6394de268ce05592c6'}
SOURCE_PINS = {
    ALLK: {'bytes': 11416, 'sha256': '9d739aab99a7873daaf25f649cca910d11f02a08ae22a32a70f517734df67962'},
    ADMISSIBLE: {'bytes': 6653, 'sha256': '9f8d0ad201037d39ddff34f0a7619456a29eb8cc61ccd0e45011769247d3c01e'},
}
stage = 'load_published_Q_reader'


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def raw_fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def value_fp(value):
    return raw_fp((json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode())


def file_fp(path):
    path = Path(path)
    need(path.is_file() and not path.is_symlink(), 'required regular evidence file missing: ' + str(path))
    with path.open('rb') as stream:
        return {'bytes': os.fstat(stream.fileno()).st_size, 'sha256': hashlib.file_digest(stream, 'sha256').hexdigest()}


def bind(path):
    return {'path': str(path), **file_fp(path)}


def pin(binding):
    return {key: binding[key] for key in ('bytes', 'sha256')}


def tree_inventory(base):
    need(base.is_dir() and base.resolve() == base, 'Q evidence root differs')
    result = {}
    for path in sorted(base.rglob('*')):
        need(not path.is_symlink(), 'symlink in Q evidence tree')
        result[str(path.relative_to(base))] = 'directory' if path.is_dir() else file_fp(path)
    return result


def validate_scope(result, worker, index):
    targets, accepted, failures, reused = ([ALLK], [ALLK], {}, []) if index == 0 else (
        REMAINING, ACCEPTED, {FAMILY: 'normal failed/scope differs: ' + FAMILY}, [ALLK])
    for record in (result, worker):
        need(record['source_commit'] == Q and record['targets'] == targets and
             record['accepted_owners'] == accepted and record['failures'] == failures and
             set(record['acceptance_bindings']) == set(accepted) and
             record['reused_complete_selected_owners'] == reused and
             set(record['direct_import_readiness']) == ({ALLK} if index == 0 else {ADMISSIBLE, FAMILY}) and
             record['published_source_count'] == 360 and record['selected_live_source_count'] == (73 if index == 0 else 157) and
             all(record[key] is False for key in ('whole_P1_complete', 'whole_P1_5_complete',
                 'accepted_supplier_recompile_requested', 'dependency_rebuild_requested',
                 'old_receipts_rebound', 'old_P3_REUSE_changed')) and
             not any(key in record for key in ('context_error', 'final_context_error', 'git_error')),
             'original Q run scope differs: attempt-%05d' % index)
    need(all(result.get(key) == value for key, value in worker.items()) and
         result['worker_exit_code'] == index and result['all_selected_owners_accepted'] is (index == 0),
         'Q RESULT/WORKER terminal status differs')
    if index == 0:
        need('dispatch_error' not in result and 'final_stock_readiness' in worker, 'AllK single success is incomplete')
    else:
        need(result['dispatch_error'] == 'serialized worker exited 1' and
             'final_stock_readiness' not in worker and 'final_stock_readiness' not in result,
             'original thirteen-target partial failure was relabelled')
    return targets, accepted


def read_run(driver, s, graph, index):
    run = ROOT / Q / 'runs' / ('attempt-%05d' % index)
    names = ['RESULT.json', 'WORKER_RESULT.json', 'CONTEXT_BEFORE.json', 'CONTEXT_AFTER.json',
             'GIT_BEFORE.json', 'GIT_AFTER.json', 'executed-driver.py']
    bindings = {name: bind(run / name) for name in names}
    need(all(pin(bindings[name]) == expected for name, expected in RUN_PINS[index].items()),
         'original Q RESULT/WORKER pin differs')
    need(file_fp(run / 'executed-driver.py') == DRIVER_FP, 'actual Q executed driver differs')
    result, worker = [s.api.read_json(run / name) for name in names[:2]]
    targets, accepted = validate_scope(result, worker, index)
    for stem in ('CONTEXT', 'GIT'):
        before, after = run / (stem + '_BEFORE.json'), run / (stem + '_AFTER.json')
        need(file_fp(before) == file_fp(after), 'original Q context pair changed: ' + stem)
    context = s.api.read_json(run / 'CONTEXT_BEFORE.json')
    requested = context['committed_inputs']['selected_targets']
    need(context['committed_inputs']['source_commit'] == Q and
         context['committed_inputs']['source_anchor_commit'] == P and
         driver.selection(requested) == requested and set(requested) == set(targets) and
         s.d.compile_order([], requested, graph) == targets, 'original Q requested/executed target scope differs')
    stock = {'recorded': False, 'reason': 'original_attempt_stopped_after_owner_failure', 'executed_again_by_collector': False}
    if index == 0:
        rec = result['final_stock_readiness']
        need(rec == s.api.read_json(run / 'final-stock-readiness-command.json') and
             rec['exit_code'] == 0 and rec['actual_built_modules'] == [] and rec['actual_failed_modules'] == [] and
             rec['cwd'] == str(PROJECT) and
             rec['argv'] == s.h.guard(0, ['lake', '--no-build', 'build', '+' + ALLK + ':olean']) and
             rec['log'] == str(run / 'final-stock-readiness.log') and
             file_fp(Path(rec['log'])) == {'bytes': rec['log_bytes'], 'sha256': rec['log_sha256']},
             'original AllK final stock readiness differs')
        stock = {'recorded': True, 'exit_code': 0, 'actual_built_modules': [], 'actual_failed_modules': [],
                 'command': bind(run / 'final-stock-readiness-command.json'), 'log': bind(Path(rec['log'])),
                 'executed_again_by_collector': False}
    public = {'source_commit': Q, 'compiler_job': JOBS[index], 'original_run': str(run),
        'status': 'ALL_SELECTED_OWNERS_ACCEPTED' if index == 0 else 'PARTIAL_FAILURE_AFTER_ACCEPTED_PREFIX',
        'original_requested_targets': requested, 'targets': targets,
        'accepted_owners': accepted, 'failed_modules': list(result['failures']),
        'failure_messages': result['failures'], 'not_accepted_modules': targets[len(accepted):],
        'not_started_modules': [] if index == 0 else targets[len(accepted) + 1:],
        'reused_complete_selected_owners': result['reused_complete_selected_owners'],
        'worker_exit_code': index, 'all_selected_owners_accepted': index == 0,
        'original_live_source_count': result['selected_live_source_count'],
        'evidence_bindings': bindings, 'original_context_pairs_equal': True, 'original_final_stock_readiness': stock}
    return result, context, public


def flat_summary(module, index, runs, owners):
    result, context, run = runs[index]
    files = run['evidence_bindings']
    return {'schema': 'p15_Q_original_accepted_owner_public_acceptance_v1',
        'status': 'ORIGINAL_Q_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION',
        'source_commit': Q, 'source_anchor_commit': P, 'compiler_job': JOBS[index],
        'driver': {'commit': Q, 'path': DRIVER, **DRIVER_FP},
        'source_manifest': {'commit': Q, 'path': MANIFEST, **MANIFEST_FP},
        'original_run': 'runs/attempt-%05d' % index,
        'original_result': pin(files['RESULT.json']), 'original_worker_result': pin(files['WORKER_RESULT.json']),
        'original_requested_targets': run['original_requested_targets'], 'original_targets': run['targets'],
        'original_group_accepted_owners': run['accepted_owners'],
        'original_group_reused_complete_selected_owners': run['reused_complete_selected_owners'],
        'original_group_failed_modules': run['failed_modules'],
        'original_group_not_accepted_modules': run['not_accepted_modules'],
        'original_group_not_started_modules': run['not_started_modules'],
        'original_group_worker_exit_code': run['worker_exit_code'],
        'original_group_all_selected_owners_accepted': run['all_selected_owners_accepted'],
        'original_group_dispatch_error': result.get('dispatch_error'),
        'original_group_live_closure_count': run['original_live_source_count'],
        'original_context_pairs': {stem: {side: pin(files[stem + '_' + side.upper() + '.json'])
            for side in ('before', 'after')} for stem in ('CONTEXT', 'GIT')},
        'original_final_stock_readiness': run['original_final_stock_readiness'],
        'owners': {module: owners[module]}, 'published_source_count': 360,
        'selected_owners_revalidated': ACCEPTED, 'current_read_live_source_count': 74,
        'current_read_preserved_dependency_count': 72,
        'owner_live_source_closure_count': owners[module]['owner_live_source_closure_count'],
        'source_runtime_and_original_receipts_unchanged': True,
        'normal_or_kernel_commands_executed': 0, 'types_or_archives_exported': False,
        'axiom_union_exported': False, 'new_lean_acceptance': False, 'whole_P1_5_complete': False}


def collect():
    global stage
    need(__debug__, 'optimized Python is refused')
    raw = subprocess.check_output(['git', 'show', Q + ':' + DRIVER], cwd=REPO)
    manifest_raw = subprocess.check_output(['git', 'show', Q + ':' + MANIFEST], cwd=REPO)
    need(raw_fp(raw) == DRIVER_FP and raw_fp(manifest_raw) == MANIFEST_FP, 'published Q reader/manifest differs')
    executed = ROOT / Q / 'runs/attempt-00000/executed-driver.py'
    need(file_fp(executed) == DRIVER_FP and executed.read_bytes() == raw, 'first original Q driver differs')
    driver = ModuleType('unchanged_Q_acceptance_reader')
    driver.__file__ = str(executed)
    exec(compile(raw, str(executed), 'exec'), driver.__dict__)
    need((driver.REPO, driver.PROJECT, driver.ROOT, driver.RUNNER, driver.SOURCE_ANCHOR) ==
         (REPO, PROJECT, ROOT, DRIVER, P), 'Q reader environment differs')
    s = driver.helpers()
    git_before = s.d.original_git_state(REPO)
    tree_before = tree_inventory(ROOT / Q)
    graph = {m: row['imports'] for m, row in json.loads(manifest_raw)['project_sources'].items()}
    stage = 'read_two_original_Q_runs'
    runs = [read_run(driver, s, graph, index) for index in (0, 1)]
    need(runs[0][0]['acceptance_bindings'][ALLK] == runs[1][0]['acceptance_bindings'][ALLK],
         'AllK reuse differs from its first Q acceptance')
    stage = 'original_Q_preflight_for_accepted_prefix_only'
    spec = driver.preflight(s, Q, ACCEPTED)
    need(len(spec.graph) == 360 and len(spec.active) == 74 and len(spec.dependency_pins) == 72 and
         spec.order == ACCEPTED and set(spec.initial_owners) == set(ACCEPTED) and FAMILY not in spec.active,
         'accepted-prefix read scope differs')
    for result, context, public in runs:
        active = s.h.closure(spec.graph, result['targets'])
        need(context['selected_live_sources'] == {m: spec.sources[m] for m in active} and
             set(context['preserved_dependency_artifacts']) == active - set(result['targets']),
             'original run source/dependency inventory differs from Q')
    artifacts_before = {m: driver.module_artifacts(s, m) for m in driver.TARGETS}
    owners = {}
    for index, module in enumerate(ACCEPTED):
        stage = 'revalidate_original_Q_owner:' + module
        driver.require_completed_existing_owner(s, Q, spec, module, spec.initial_owners[module])
        binding = driver.acceptance_binding(s, Q, module)
        need(binding == runs[index][0]['acceptance_bindings'][module] and len(binding['audits']) == 1,
             'current owner binding differs from its original accepting run')
        normal = ROOT / Q / module / 'normal' / module / 'NORMAL_PASS.json'
        audit = ROOT / Q / module / 'audits' / AUDITS[module]
        paths = {'normal': normal, 'audit_plan': audit / 'AUDIT_PLAN.json',
                 'audit_result': audit / 'lane-0/VALIDATION_RESULTS.json',
                 'owned_exports': audit / 'lane-0/OWNED_EXPORTS.json',
                 'owned_log': audit / 'lane-0/all-owned-types-axioms.log',
                 'reused_normal_evidence': audit / 'lane-0/REUSED_NORMAL_EVIDENCE.json'}
        receipts = {key: bind(path) for key, path in paths.items()}
        need(binding['normal_receipt'] == receipts['normal'] and binding['audits'] == [
             {'plan': receipts['audit_plan'], 'result': receipts['audit_result']}], 'original audit ID/path differs')
        counted = s.api.read_json(paths['audit_result'])
        counts = (counted['total_owned_exports'], counted['total_public_exports'])
        need(counts == ((34, 31) if module == ALLK else (42, 42)), 'original Q owned/public counts differ')
        source = PROJECT / s.h.module_path(module)
        need(file_fp(source) == SOURCE_PINS[module] and spec.sources[module] == SOURCE_PINS[module]['sha256'],
             'accepted original Q source differs')
        owners[module] = {'source_commit': Q, 'source_sha256': spec.sources[module],
            'source': bind(source), 'compiler_job': JOBS[index],
            'original_accepting_run': runs[index][2]['original_run'], 'audit_id': AUDITS[module],
            'owned_count': counts[0], 'public_count': counts[1],
            'owner_live_source_closure_count': len(s.h.closure(spec.graph, [module])),
            'receipt_bindings': {key: pin(value) for key, value in receipts.items()},
            'receipt_paths': {key: value['path'] for key, value in receipts.items()},
            'normal_kernel_full_owned_revalidated_without_execution': True,
            'source_plus_five_and_all_21_artifacts_bound_to_original_result': True,
            'receipt_rebound_to_current_commit': False,
            'later_same_Q_reuse_run': runs[1][2]['original_run'] if module == ALLK else None}
    stage = 'verify_read_only_context_preservation'
    need(driver.snapshot(s, spec) == spec.baseline and
         {m: driver.module_artifacts(s, m) for m in driver.TARGETS} == artifacts_before and
         tree_inventory(ROOT / Q) == tree_before and s.d.original_git_state(REPO) == git_before,
         'source/runtime/artifact/original-evidence/Git context changed during collection')
    prior = {m: {key: row[key] for key in ('source_commit', 'source_sha256', 'owned_count', 'public_count')}
             for m, row in spec.supplier_evidence.items()}
    return {'schema': 'p15_Q_two_original_runs_accepted_prefix_public_acceptance_v1',
        'status': 'ORIGINAL_Q_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION',
        'source_commit': Q, 'source_anchor_commit': P,
        'collector': {'filename': Path(__file__).name, **file_fp(Path(__file__))},
        'driver': {'commit': Q, 'path': DRIVER, **DRIVER_FP},
        'source_manifest': {'commit': Q, 'path': MANIFEST, **MANIFEST_FP},
        'public_summaries': {name: flat_summary(module, index, runs, owners)
            for index, (name, module) in enumerate((('ALLK_Q_PUBLIC_ACCEPTANCE', ALLK),
                                                   ('ADMISSIBLE_Q_PUBLIC_ACCEPTANCE', ADMISSIBLE)))},
        'selected_owners_revalidated': ACCEPTED,
        'published_source_count': len(spec.graph), 'current_read_live_source_count': len(spec.active),
        'current_read_preserved_dependency_count': len(spec.dependency_pins),
        'historical_owners_revalidated_in_current_read_scope': prior,
        'all_current_target_artifact_slots_watched': len(driver.TARGETS) * 21,
        'complete_original_Q_evidence_inventory': {'entry_count': len(tree_before), **value_fp(tree_before)},
        'current_read_snapshot': value_fp(spec.baseline), 'current_dirty_Git_state': value_fp(git_before),
        'remaining_failed_modules': [FAMILY], 'remaining_not_started_modules': REMAINING[3:],
        'source_runtime_artifacts_and_original_receipts_unchanged': True,
        'current_dirty_Git_state_unchanged': True, 'normal_or_kernel_commands_executed': 0,
        'stock_readiness_executed_by_collector': False, 'types_or_archives_exported': False,
        'axiom_union_exported': False, 'new_lean_acceptance': False, 'whole_P1_5_complete': False}


if __name__ == '__main__':
    for key, value in {'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'}.items():
        os.environ[key] = value
    try:
        result = collect()
        code = 0
    except Exception as error:
        result = {'status': 'HOLD', 'stage': stage, 'error_type': type(error).__name__,
                  'reason': str(error)[:1000], 'new_lean_acceptance': False, 'whole_P1_5_complete': False}
        code = 3
    print(json.dumps(result, ensure_ascii=False, sort_keys=True), flush=True)
    raise SystemExit(code)
