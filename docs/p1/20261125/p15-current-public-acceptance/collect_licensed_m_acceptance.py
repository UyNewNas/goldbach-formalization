#!/usr/bin/env python3
"""Read bounded acceptance evidence for M's fixed first original-15 attempt.

The actual terminal RESULT/WORKER fingerprints below bind the fixed M attempt.
Only its nonempty accepted prefix is checked through M's unchanged normal/full-owned
readers. A partial original run stays partial; no owner, Lean, kernel, installer,
stock command, or worker is executed here. Full types and logs remain private.
"""
from contextlib import contextmanager, redirect_stderr, redirect_stdout
from pathlib import Path
from types import ModuleType
import hashlib
import io
import json
import os
import re
import subprocess
import sys

sys.dont_write_bytecode = True
COMMIT = '54c6e72732ce3a6d209960c396956f9cb2fe3f59'
COMPILER_JOB = 'job_11072d40ef774d1abb6afb1c38b215b1'
SOURCE_ANCHOR = '972c2220d87669869a65c03fa64dc04562e37f0d'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PREFIX = 'docs/p1/20261126/p15-current-corrections/'
TARGETS = [
    'ImbalancedChen.P5IndependentPrimeSourceWordDictionary',
    'ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy',
    'ImbalancedChen.P1OriginalSingletonSmoothLicence',
    'ImbalancedChen.P5OriginalSingletonLowerTrimPaid',
    'ImbalancedChen.P1OriginalSingletonAtlasTrim',
    'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches',
    'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime',
    'ImbalancedChen.P5LicensedOriginalIntegerProfile',
    'ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward',
    'ImbalancedChen.P5AdmissibleAllRankIntegerGeometricFamily',
    'ImbalancedChen.Part3AllKLambdaChartCorrection',
    'ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound',
    'ImbalancedChen.P5OriginalPrimeEndpointLogPayment',
    'ImbalancedChen.P5OriginalSharpPrimeSynthesis',
    'ImbalancedChen.P5PrimeDivisorMeanCorrection',
]
DRIVER = {'bytes': 72984, 'sha256': 'a956f87fa00e360156c6e10dba3de857e038486b7e6a97aefebfe80e9a05ccfa'}
MANIFEST = {'bytes': 335974, 'sha256': '0ce2649ad047edaba54c63c62f369d3df1046c5b2bd4cf4a916cac9584348a8d'}
# Actual fixed M attempt fingerprints from bounded metadata job_69a6cac7c8504cc68a05633c4e353cf0.
EXPECTED_RESULT = {'bytes': 37943, 'sha256': 'a1173904f25955de383622f4641d1bd5de6ff04b4b077357cf5623c6b21211f5'}
EXPECTED_WORKER = {'bytes': 37827, 'sha256': '24de7742786b14f0841e40aa242538512c8f5f1f7d2536d4d9cd09f9b1d4c60a'}
MAX_PUBLIC_BYTES = 32768
MAX_RETAINED_FILE_BYTES = 128 * 1024 * 1024
stage = 'unbound_M_terminal_fingerprints'


def fingerprint(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def encode(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode('utf-8')


def git_file(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO,
                                   stderr=subprocess.PIPE)


@contextmanager
def quiet_readers():
    """Suppress incidental Python and child output; only bounded JSON is public."""
    capture = io.StringIO()
    sys.stdout.flush()
    sys.stderr.flush()
    saved = [os.dup(1), os.dup(2)]
    null_fd = os.open(os.devnull, os.O_WRONLY)
    try:
        os.dup2(null_fd, 1)
        os.dup2(null_fd, 2)
        with redirect_stdout(capture), redirect_stderr(capture):
            yield
    finally:
        for fd, original in zip((1, 2), saved):
            os.dup2(original, fd)
            os.close(original)
        os.close(null_fd)


def collect():
    global stage
    assert __debug__, 'PYTHON_OPTIMIZATION_NOT_ALLOWED'
    assert re.fullmatch('[0-9a-f]{40}', COMMIT)
    assert re.fullmatch('job_[0-9a-f]{32}', COMPILER_JOB)
    for expected in (EXPECTED_RESULT, EXPECTED_WORKER):
        assert isinstance(expected, dict) and set(expected) == {'bytes', 'sha256'}
        assert type(expected['bytes']) is int and expected['bytes'] > 0
        assert re.fullmatch('[0-9a-f]{64}', expected['sha256'])
    root = ROOT / COMMIT
    run = root / 'runs/attempt-00000'
    retained = {}

    def read(path):
        assert path.is_file() and not path.is_symlink() and path.resolve() == path
        assert path.stat().st_size <= MAX_RETAINED_FILE_BYTES
        raw = path.read_bytes()
        assert len(raw) <= MAX_RETAINED_FILE_BYTES
        pin = fingerprint(raw)
        assert path not in retained or retained[path] == pin
        retained[path] = pin
        return raw

    stage = 'fixed_M_published_inputs'
    # The run's immutable executed copy is authoritative; no dirty Git worktree
    # copy or new deployment of the historical runner is required.
    entrypoint = run / 'executed-driver.py'
    code = read(entrypoint)
    assert fingerprint(code) == DRIVER
    assert code == git_file(COMMIT, PREFIX + 'run_selected.py')
    manifest_raw = git_file(COMMIT, PREFIX + 'SOURCE_MANIFEST.json')
    assert fingerprint(manifest_raw) == MANIFEST
    manifest = json.loads(manifest_raw)
    assert manifest['source_anchor_commit'] == SOURCE_ANCHOR
    assert manifest['project_module_count'] == 360 and manifest['target_count'] == 21
    assert manifest['selection_guidance']['subsequent_15_targets'] == TARGETS
    assert manifest['selection_guidance']['subsequent_15_source_count'] == 157

    stage = 'actual_M_original_attempt_and_accepted_prefix'
    original_raw, worker_raw = read(run / 'RESULT.json'), read(run / 'WORKER_RESULT.json')
    assert fingerprint(original_raw) == EXPECTED_RESULT
    assert fingerprint(worker_raw) == EXPECTED_WORKER
    original, worker = json.loads(original_raw), json.loads(worker_raw)
    accepted = original['accepted_owners']
    assert type(accepted) is list and accepted, 'NO_ORIGINAL_ACCEPTED_OWNERS'
    assert len(accepted) == len(set(accepted)) and set(accepted) <= set(TARGETS)
    for record in (original, worker):
        assert record['source_commit'] == COMMIT
        assert type(record['targets']) is list and len(record['targets']) == 15
        assert set(record['targets']) == set(TARGETS)
        assert record['accepted_owners'] == accepted
        assert record['targets'][:len(accepted)] == accepted
        assert set(record['acceptance_bindings']) == set(accepted)
        assert not any(key in record for key in ('context_error', 'final_context_error', 'git_error'))
        assert record['published_source_count'] == 360 and record['selected_live_source_count'] == 157
        assert record['whole_P1_complete'] is False and record['whole_P1_5_complete'] is False
        assert record['accepted_supplier_recompile_requested'] is False
        assert record['dependency_rebuild_requested'] is False and record['old_receipts_rebound'] is False
        assert record['old_P3_REUSE_changed'] is False and record['reused_complete_selected_owners'] == []
    assert 'dispatch_error' not in worker
    for key in ('targets', 'failures', 'acceptance_bindings', 'direct_import_readiness',
                'original_supplier_acceptance_bindings'):
        assert original[key] == worker[key]
    full_success = len(accepted) == 15
    if full_success:
        assert original['failures'] == {}
        assert original['worker_exit_code'] == 0 and original['all_selected_owners_accepted'] is True
        assert 'dispatch_error' not in original
        assert original['final_stock_readiness'] == worker['final_stock_readiness']
    else:
        assert set(original['failures']) == {original['targets'][len(accepted)]}
        assert original['worker_exit_code'] == 1 and original['all_selected_owners_accepted'] is False
        assert original.get('dispatch_error') == 'serialized worker exited 1'
        assert 'final_stock_readiness' not in original and 'final_stock_readiness' not in worker
    for module in accepted:
        ready = original['direct_import_readiness'][module]
        assert ready['exit_code'] == 0 and ready['actual_built_modules'] == [] and ready['actual_failed_modules'] == []
    context_pairs = {}
    for stem in ('CONTEXT', 'GIT'):
        before, after = run / (stem + '_BEFORE.json'), run / (stem + '_AFTER.json')
        assert read(before) == read(after)
        context_pairs[stem] = {'before': retained[before], 'after': retained[after]}

    stage = 'unchanged_M_normal_and_complete_owned_readers'
    driver = ModuleType('fixed_M_readonly_accepted_prefix_reader')
    driver.__file__ = str(entrypoint)
    exec(compile(code, str(entrypoint), 'exec'), driver.__dict__)
    assert (driver.REPO, driver.PROJECT, driver.ROOT) == (REPO, PROJECT, ROOT)
    assert driver.SOURCE_ANCHOR == SOURCE_ANCHOR and driver.MANIFEST_SHA == MANIFEST['sha256']
    s = driver.helpers()
    graph = {module: row['imports'] for module, row in manifest['project_sources'].items()}
    assert original['targets'] == s.d.compile_order([], TARGETS, graph)
    assert len(s.h.closure(graph, TARGETS)) == 157
    # A failed next owner may retain failed setup. It is never selected here.
    # Only accepted owners' live import closures enter the unchanged preflight.
    spec = driver.preflight(s, COMMIT, accepted)
    assert spec.manifest == manifest and spec.graph == graph and len(spec.graph) == 360
    assert spec.selected == set(accepted) and spec.order == accepted
    assert set(spec.initial_owners) == set(accepted)
    assert set(spec.dependency_pins) == spec.active - set(accepted)
    assert not (set(original['failures']) & spec.active)
    expected_historical = spec.active & (set(manifest['accepted_suppliers']) |
                                          set(manifest['previously_accepted_targets']))
    assert set(spec.supplier_evidence) == expected_historical
    for module, evidence in spec.supplier_evidence.items():
        assert evidence == original['original_supplier_acceptance_bindings'][module]
        assert evidence['receipt_rebound_to_current_commit'] is False
        assert evidence['Lean_or_kernel_executed_for_supplier'] is False

    owners = {}
    for module in accepted:
        stage = 'unique_original_M_owner_receipts:' + module
        base = root / module
        audits = list((base / 'audits').iterdir())
        assert len(audits) == 1
        audit = audits[0]
        assert audit.is_dir() and not audit.is_symlink() and audit.resolve() == audit
        paths = {'normal': base / 'normal' / module / 'NORMAL_PASS.json',
            'audit_plan': audit / 'AUDIT_PLAN.json',
            'audit_result': audit / 'lane-0/VALIDATION_RESULTS.json',
            'owned_exports': audit / 'lane-0/OWNED_EXPORTS.json',
            'owned_log': audit / 'lane-0/all-owned-types-axioms.log',
            'reused_normal_evidence': audit / 'lane-0/REUSED_NORMAL_EVIDENCE.json'}
        for path in paths.values():
            read(path)
        validation = json.loads(read(paths['audit_result']))
        receipts = {key: retained[path] for key, path in paths.items()}
        binding = original['acceptance_bindings'][module]
        assert binding['module'] == module
        assert binding['normal_receipt'] == {'path': str(paths['normal']), **receipts['normal']}
        assert binding['audits'] == [{
            'plan': {'path': str(paths['audit_plan']), **receipts['audit_plan']},
            'result': {'path': str(paths['audit_result']), **receipts['audit_result']}}]
        assert len(spec.initial_owners[module]['artifacts']) == 21
        assert spec.initial_owners[module]['artifacts'] == binding['all_observed_target_artifacts']
        assert driver.acceptance_binding(s, COMMIT, module) == binding
        driver.require_completed_existing_owner(s, COMMIT, spec, module, spec.initial_owners[module])
        assert driver.acceptance_binding(s, COMMIT, module) == binding
        owned, public = validation['total_owned_exports'], validation['total_public_exports']
        assert type(owned) is int and type(public) is int and 0 <= public <= owned
        owners[module] = {'source_commit': COMMIT, 'source_sha256': spec.sources[module],
            'audit_id': audit.name, 'owned_count': owned, 'public_count': public,
            'receipt_bindings': receipts, 'normal_kernel_full_owned_revalidated_without_execution': True,
            'source_plus_five_and_all_21_artifacts_bound_to_original_result': True,
            'receipt_rebound_to_current_commit': False}

    stage = 'original_M_final_stock_scope'
    if full_success:
        stock = original['final_stock_readiness']
        assert stock['argv'] == s.h.guard(0, ['lake', '--no-build', 'build'] +
                                         ['+' + module + ':olean' for module in original['targets']])
        assert stock['cwd'] == str(PROJECT) and stock['exit_code'] == 0
        assert stock['actual_built_modules'] == [] and stock['actual_failed_modules'] == []
        stock_log = run / 'final-stock-readiness.log'
        assert stock['log'] == str(stock_log)
        read(stock_log)
        assert retained[stock_log] == {'bytes': stock['log_bytes'], 'sha256': stock['log_sha256']}
        final_stock = {'recorded': True, 'exit_code': 0, 'built': [], 'failed': [],
                       'log_fingerprint': retained[stock_log], 'executed_again_by_collector': False}
    else:
        final_stock = {'recorded': False, 'reason': 'original_attempt_stopped_after_owner_failure',
                       'executed_again_by_collector': False}

    stage = 'final_preservation'
    assert driver.snapshot(s, spec) == spec.baseline
    for module in accepted:
        assert driver.acceptance_binding(s, COMMIT, module) == original['acceptance_bindings'][module]
        assert driver.module_artifacts(s, module) == spec.initial_owners[module]['artifacts']
    for path, expected in retained.items():
        assert path.is_file() and not path.is_symlink() and path.resolve() == path
        assert fingerprint(path.read_bytes()) == expected
    result = {'schema': 'p15_M_original_accepted_prefix_public_acceptance_v1',
        'status': 'ORIGINAL_M_ACCEPTED_OWNERS_REVALIDATED_WITHOUT_EXECUTION',
        'source_commit': COMMIT, 'compiler_job': COMPILER_JOB, 'original_run': 'runs/attempt-00000',
        'driver': {'commit': COMMIT, 'path': PREFIX + 'run_selected.py', **DRIVER},
        'source_manifest': {'commit': COMMIT, 'path': PREFIX + 'SOURCE_MANIFEST.json', **MANIFEST},
        'source_anchor_commit': SOURCE_ANCHOR, 'original_result': retained[run / 'RESULT.json'],
        'original_worker_result': retained[run / 'WORKER_RESULT.json'],
        'original_group_worker_exit_code': original['worker_exit_code'],
        'original_group_all_selected_owners_accepted': original['all_selected_owners_accepted'],
        'original_group_accepted_owners': accepted,
        'original_group_failed_modules': sorted(original['failures']),
        'original_group_not_accepted_modules': [module for module in original['targets'] if module not in owners],
        'selected_owners_revalidated': accepted, 'original_context_pairs': context_pairs,
        'owners': owners, 'published_source_count': 360, 'original_group_live_closure_count': 157,
        'selected_owner_live_closure_count': len(spec.active),
        'preserved_dependency_count': len(spec.dependency_pins),
        'historical_original_acceptance_identities': {
            module: {'source_commit': evidence['source_commit'],
                     'original_full_audit_revalidated_without_execution': True,
                     'receipt_rebound_to_current_commit': False}
            for module, evidence in sorted(spec.supplier_evidence.items())},
        'original_final_stock_readiness': final_stock,
        'source_runtime_and_original_receipts_unchanged': True,
        'normal_or_kernel_commands_executed': 0, 'axiom_union_exported': False,
        'types_or_archives_exported': False, 'whole_P1_5_complete': False}
    payload = encode(result) + b'\n'
    assert len(payload) <= MAX_PUBLIC_BYTES, 'PUBLIC_OUTPUT_BUDGET_EXCEEDED'
    return payload


def main():
    global stage
    for key, value in {'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'}.items():
        os.environ[key] = value
    try:
        with quiet_readers():
            payload = collect()
    except Exception as error:
        # Never relay original audit exceptions, private declarations or raw logs.
        payload = encode({'schema': 'p15_M_original_accepted_prefix_public_acceptance_v1',
            'status': 'HOLD', 'source_commit': COMMIT, 'compiler_job': COMPILER_JOB,
            'stage': stage, 'failure_class': type(error).__name__,
            'normal_or_kernel_commands_executed': 0, 'new_acceptance_claimed': False}) + b'\n'
        sys.stdout.buffer.write(payload)
        sys.stdout.buffer.flush()
        return 3
    sys.stdout.buffer.write(payload)
    sys.stdout.buffer.flush()
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
