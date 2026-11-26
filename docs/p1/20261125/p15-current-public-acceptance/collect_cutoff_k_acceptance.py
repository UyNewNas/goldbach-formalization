#!/usr/bin/env python3
"""Collect the fixed K Cutoff acceptance only after its original run succeeds.

Use K's unchanged normal/full-owned readers, never a build, kernel invocation,
installer, or driver worker. Keep full types, logs and source inventories private.
HB is validated through its original F adapter inside Cutoff's closure68. Support
is outside that closure: only its original B mapping and C public identity are
bound here; its live closure109 is deliberately not re-audited.
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
COMMIT = '237b5c5c6b9fa721ea2d069fb5fafc0940a27e4e'
COMPILER_JOB = 'job_fce62dd5906d4d26ac8cb17790fbec32'
SOURCE_ANCHOR = '7c59a3d125d99010a501c14f1ecc60710483f918'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PREFIX = 'docs/p1/20261126/p15-current-corrections/'
CUTOFF = 'ImbalancedChen.P1OriginalSingletonCutoffData'
HB = 'ImbalancedChen.P5OriginalPrimeChartHBWitnesses'
SUPPORT = 'ImbalancedChen.P1OriginalSingletonSupportData'
TARGETS = [CUTOFF]
DRIVER = {'bytes': 59950, 'sha256': '575fcc9737d0b239cb0d994ad286ad8cae5dbf4406ca898157d7c2e87782c293'}
MANIFEST = {'bytes': 333254, 'sha256': 'f683cfc328b7323d4e1840e10dc1eca0b24c4b55b644756ef2e5d910152a27e5'}
SOURCE = {'bytes': 12744, 'sha256': 'ceb0d90a99b41455124802c5446d16499e11207f1042b790f0646d4c19272b22'}
HB_COMMIT = '080d4178711ae042235104f7f4768649f51da2ab'
HB_PUBLIC = {'commit': 'f6fdd7fffe17803c60914bf28b39b55715d34464',
    'path': 'docs/p1/20261125/p15-current-public-acceptance/HB_F_PUBLIC_ACCEPTANCE.json',
    'bytes': 3109, 'sha256': 'b1c9bbf219d3d1fea2294683f71dce391c91b9abe7d6bb80ceb0238b40081598'}
SUPPORT_COMMIT = '3d292e4cd193ab422ca990e80a25165d5aca33a1'
SUPPORT_PUBLIC = {'commit': '545566753bae9464560a871bea87ea663f90aa53',
    'path': 'docs/p1/20261125/p15-current-public-acceptance/SUPPORT_CURRENT_PUBLIC_ACCEPTANCE.json',
    'bytes': 1894, 'sha256': '25a6333e4b89b03ca541d72a26b5d7f9273849bb7cc8aed6cc351db99bbc3c1a'}
MAX_PUBLIC_BYTES = 6144
MAX_RETAINED_FILE_BYTES = 128 * 1024 * 1024
stage = 'unbound_K_identity'


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

    stage = 'fixed_K_published_inputs'
    entrypoint = root / 'published-entrypoints/run_selected.py'
    code = read(entrypoint)
    assert fingerprint(code) == DRIVER
    assert code == git_file(COMMIT, PREFIX + 'run_selected.py')
    manifest_raw = git_file(COMMIT, PREFIX + 'SOURCE_MANIFEST.json')
    assert fingerprint(manifest_raw) == MANIFEST
    manifest = json.loads(manifest_raw)
    assert manifest['source_anchor_commit'] == SOURCE_ANCHOR
    source_path = CUTOFF.replace('.', '/') + '.lean'
    assert fingerprint(git_file(COMMIT, source_path)) == SOURCE
    assert git_file(COMMIT, source_path) == git_file(SOURCE_ANCHOR, source_path)
    assert {key: manifest['project_sources'][CUTOFF][key] for key in ('bytes', 'sha256')} == SOURCE
    assert read(run / 'executed-driver.py') == code

    stage = 'original_K_single_owner_success_required'
    original = json.loads(read(run / 'RESULT.json'))
    worker = json.loads(read(run / 'WORKER_RESULT.json'))
    for record in (original, worker):
        assert record['source_commit'] == COMMIT
        assert record['targets'] == TARGETS and record['accepted_owners'] == TARGETS
        assert record['failures'] == {} and set(record['acceptance_bindings']) == {CUTOFF}
        assert not any(key in record for key in ('context_error', 'final_context_error', 'git_error', 'dispatch_error'))
        assert record['published_source_count'] == 360 and record['selected_live_source_count'] == 68
        assert record['accepted_supplier_recompile_requested'] is False
        assert record['dependency_rebuild_requested'] is False and record['old_receipts_rebound'] is False
        assert record['old_P3_REUSE_changed'] is False and record['reused_complete_selected_owners'] == []
    assert original['worker_exit_code'] == 0 and original['all_selected_owners_accepted'] is True
    for key in ('failures', 'acceptance_bindings', 'direct_import_readiness', 'final_stock_readiness',
                'original_supplier_acceptance_bindings'):
        assert original[key] == worker[key]
    ready = original['direct_import_readiness'][CUTOFF]
    assert ready['exit_code'] == 0 and ready['actual_built_modules'] == [] and ready['actual_failed_modules'] == []
    context_pairs = {}
    for stem in ('CONTEXT', 'GIT'):
        before, after = run / (stem + '_BEFORE.json'), run / (stem + '_AFTER.json')
        assert read(before) == read(after)
        context_pairs[stem] = {'before': retained[before], 'after': retained[after]}

    stage = 'unique_original_K_owner_receipts'
    base = root / CUTOFF
    audits = list((base / 'audits').iterdir())
    assert len(audits) == 1
    audit = audits[0]
    assert audit.is_dir() and not audit.is_symlink() and audit.resolve() == audit
    paths = {'normal': base / 'normal' / CUTOFF / 'NORMAL_PASS.json',
        'audit_plan': audit / 'AUDIT_PLAN.json',
        'audit_result': audit / 'lane-0/VALIDATION_RESULTS.json',
        'owned_exports': audit / 'lane-0/OWNED_EXPORTS.json',
        'owned_log': audit / 'lane-0/all-owned-types-axioms.log',
        'reused_normal_evidence': audit / 'lane-0/REUSED_NORMAL_EVIDENCE.json'}
    for path in paths.values():
        read(path)
    validation = json.loads(read(paths['audit_result']))
    receipts = {key: retained[path] for key, path in paths.items()}
    binding = original['acceptance_bindings'][CUTOFF]
    assert binding['module'] == CUTOFF
    assert binding['normal_receipt'] == {'path': str(paths['normal']), **receipts['normal']}
    assert binding['audits'] == [{
        'plan': {'path': str(paths['audit_plan']), **receipts['audit_plan']},
        'result': {'path': str(paths['audit_result']), **receipts['audit_result']}}]

    stage = 'unchanged_K_normal_and_complete_owned_readers'
    driver = ModuleType('fixed_K_readonly_Cutoff_reader')
    driver.__file__ = str(entrypoint)
    exec(compile(code, str(entrypoint), 'exec'), driver.__dict__)
    assert (driver.REPO, driver.PROJECT, driver.ROOT) == (REPO, PROJECT, ROOT)
    assert driver.SOURCE_ANCHOR == SOURCE_ANCHOR and driver.MANIFEST_SHA == MANIFEST['sha256']
    s = driver.helpers()
    spec = driver.preflight(s, COMMIT, TARGETS)
    assert len(spec.graph) == 360 and len(spec.active) == 68 and spec.selected == {CUTOFF}
    assert set(spec.initial_owners) == {CUTOFF}
    assert len(spec.dependency_pins) == 67 and set(spec.dependency_pins) == spec.active - {CUTOFF}
    assert HB in spec.active and SUPPORT not in spec.active
    assert spec.sources[CUTOFF] == SOURCE['sha256']
    assert len(spec.initial_owners[CUTOFF]['artifacts']) == 21
    assert spec.initial_owners[CUTOFF]['artifacts'] == binding['all_observed_target_artifacts']
    driver.require_completed_existing_owner(s, COMMIT, spec, CUTOFF, spec.initial_owners[CUTOFF])
    assert driver.acceptance_binding(s, COMMIT, CUTOFF) == binding
    assert driver.snapshot(s, spec) == spec.baseline
    stock = original['final_stock_readiness']
    assert stock['argv'] == s.h.guard(0, ['lake', '--no-build', 'build', '+' + CUTOFF + ':olean'])
    assert stock['cwd'] == str(PROJECT) and stock['exit_code'] == 0
    assert stock['actual_built_modules'] == [] and stock['actual_failed_modules'] == []
    stock_log = run / 'final-stock-readiness.log'
    assert stock['log'] == str(stock_log)
    read(stock_log)
    assert retained[stock_log] == {'bytes': stock['log_bytes'], 'sha256': stock['log_sha256']}

    stage = 'original_F_HB_and_B_Support_identities'
    hb_prior = spec.manifest['previously_accepted_targets'][HB]
    support_prior = spec.manifest['previously_accepted_targets'][SUPPORT]
    assert hb_prior['source_commit'] == HB_COMMIT
    assert hb_prior['historical_group']['public_evidence'] == HB_PUBLIC
    assert support_prior['source_commit'] == SUPPORT_COMMIT
    assert support_prior['historical_group']['public_evidence'] == SUPPORT_PUBLIC
    hb_raw = git_file(HB_PUBLIC['commit'], HB_PUBLIC['path'])
    support_raw = git_file(SUPPORT_PUBLIC['commit'], SUPPORT_PUBLIC['path'])
    assert fingerprint(hb_raw) == {key: HB_PUBLIC[key] for key in ('bytes', 'sha256')}
    assert fingerprint(support_raw) == {key: SUPPORT_PUBLIC[key] for key in ('bytes', 'sha256')}
    hb_public, support_public = json.loads(hb_raw), json.loads(support_raw)
    driver.require_hb_f_public_scope(hb_prior, hb_public)
    assert spec.supplier_evidence[HB]['source_commit'] == HB_COMMIT
    assert spec.supplier_evidence[HB] == original['original_supplier_acceptance_bindings'][HB]
    assert support_public['schema'] == 'p15_support_B_original_public_acceptance_v1'
    assert support_public['source_commit'] == SUPPORT_COMMIT
    assert support_public['owners'][SUPPORT]['source_commit'] == SUPPORT_COMMIT
    assert support_public['owners'][SUPPORT]['source_sha256'] == support_prior['source_sha256']
    assert support_public['owners'][SUPPORT]['receipt_rebound_to_current_commit'] is False
    assert SUPPORT not in spec.supplier_evidence

    owned, public = validation['total_owned_exports'], validation['total_public_exports']
    assert type(owned) is int and type(public) is int and 0 <= public <= owned
    owner = {'source_commit': COMMIT, 'source_sha256': spec.sources[CUTOFF],
        'audit_id': audit.name, 'owned_count': owned, 'public_count': public,
        'receipt_bindings': receipts, 'normal_kernel_full_owned_revalidated_without_execution': True,
        'all_21_artifacts_bound_to_original_result': True, 'receipt_rebound_to_current_commit': False}

    stage = 'final_preservation'
    assert driver.snapshot(s, spec) == spec.baseline
    assert driver.acceptance_binding(s, COMMIT, CUTOFF) == binding
    for path, expected in retained.items():
        assert path.is_file() and not path.is_symlink() and path.resolve() == path
        assert fingerprint(path.read_bytes()) == expected
    assert driver.module_artifacts(s, CUTOFF) == spec.initial_owners[CUTOFF]['artifacts']
    result = {'schema': 'p15_cutoff_K_original_public_acceptance_v1',
        'status': 'ORIGINAL_CUTOFF_ACCEPTANCE_REVALIDATED_WITHOUT_EXECUTION',
        'source_commit': COMMIT, 'compiler_job': COMPILER_JOB,
        'driver': {'commit': COMMIT, 'path': PREFIX + 'run_selected.py', **DRIVER},
        'source_manifest': {'commit': COMMIT, 'path': PREFIX + 'SOURCE_MANIFEST.json', **MANIFEST},
        'source_anchor_commit': SOURCE_ANCHOR, 'original_result': retained[run / 'RESULT.json'],
        'original_worker_result': retained[run / 'WORKER_RESULT.json'],
        'original_group_worker_exit_code': original['worker_exit_code'],
        'original_group_all_selected_owners_accepted': original['all_selected_owners_accepted'],
        'original_group_accepted_owners': original['accepted_owners'],
        'original_group_failed_modules': sorted(original['failures']),
        'selected_owners_revalidated': TARGETS, 'original_context_pairs': context_pairs,
        'owners': {CUTOFF: owner}, 'published_source_count': 360,
        'selected_owner_live_closure_count': len(spec.active),
        'historical_dependencies': {
            HB: {'source_commit': HB_COMMIT, 'public_summary': HB_PUBLIC,
                'active_in_selected_closure': True, 'original_F_full_owned_reader_revalidated': True,
                'receipt_rebound_to_K': False},
            SUPPORT: {'source_commit': SUPPORT_COMMIT, 'public_summary': SUPPORT_PUBLIC,
                'active_in_selected_closure': False, 'mapping_and_public_identity_bound': True,
                'live_B_closure_revalidated_by_this_collector': False, 'receipt_rebound_to_K': False}},
        'original_final_stock_readiness': {'exit_code': 0, 'built': [], 'failed': [],
            'log_fingerprint': retained[stock_log], 'executed_again_by_collector': False},
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
        payload = encode({'schema': 'p15_cutoff_K_original_public_acceptance_v1',
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
