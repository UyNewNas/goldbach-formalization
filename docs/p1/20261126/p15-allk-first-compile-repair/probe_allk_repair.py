#!/usr/bin/env python3
"""Read original PerGroup@O acceptance, then typecheck the exact AllK repair without outputs."""
import argparse
from contextlib import contextmanager, redirect_stdout, redirect_stderr
from pathlib import Path
from types import ModuleType
import hashlib
import io
import json
import os
import subprocess
import sys

sys.dont_write_bytecode = True
COMMIT = 'dc1e74ee5c15471d6dd22e4e2c609d5e79b0169d'
ANCHOR = 'c47ea640bf40c22423aec7066c13e5b05956d349'
JOB = 'job_cda017c5183c4b5ba80a8a2182f446ba'
TARGET = 'ImbalancedChen.Part3AllKLambdaChartCorrection'
PRIOR = 'ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PROBE_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-allk-api-probe-v1')
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
DRIVER_FP = {'bytes': 87907, 'sha256': '9e673a755108d8cf58f02db2165654a1df97e701b0137275078e33da2136f5d9'}
MANIFEST_FP = {'bytes': 339019, 'sha256': '0801ba4e04eacfa8c8d9f99ec657898035d1af3153bcc4023de54bb20833ed2f'}
SOURCE_FP = {'bytes': 11458, 'sha256': '124094d9fbc7358bfbc5e841cc2c5f853330f54f1f432fa17728e1ce1a5f64b8'}
CANDIDATE_FP = {'bytes': 11416, 'sha256': '9d739aab99a7873daaf25f649cca910d11f02a08ae22a32a70f517734df67962'}
RESULT_FP = {'bytes': 39901, 'sha256': '48934d443e7598fb71c8c20eead738e63af03b4fa7ad11f5c00943b723db2bee'}
WORKER_FP = {'bytes': 39785, 'sha256': 'd0886d01d8b06fc23db731d730fdd05bcb2445faa9fc45799cab766df9bd6cfd'}
SETUP_FP = {'bytes': 6329098, 'sha256': '14330c5ee87da605a861559cdd3adb035302ef8e4aa90d3f20cf467b751e0b87'}
stage = 'pinned_inputs'


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def raw_fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def fp(path):
    path = Path(path)
    if not os.path.lexists(path):
        return None
    need(path.is_file() and not path.is_symlink(), 'NONREGULAR_INPUT: ' + str(path))
    return raw_fp(path.read_bytes())


@contextmanager
def quiet():
    saved = [os.dup(1), os.dup(2)]
    null = os.open(os.devnull, os.O_WRONLY)
    try:
        sys.stdout.flush()
        sys.stderr.flush()
        os.dup2(null, 1)
        os.dup2(null, 2)
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            yield
    finally:
        for fd, original in zip((1, 2), saved):
            os.dup2(original, fd)
            os.close(original)
        os.close(null)


def run(candidate_path):
    global stage
    need(__debug__, 'OPTIMIZED_PYTHON_REFUSED')
    need(fp(candidate_path) == CANDIDATE_FP, 'CANDIDATE_FINGERPRINT_DIFFERS')
    candidate = candidate_path.read_bytes()
    raw = subprocess.check_output(['git', 'show', COMMIT + ':' + DRIVER], cwd=REPO)
    need(raw_fp(raw) == DRIVER_FP, 'ORIGINAL_O_DRIVER_DIFFERS')
    entrypoint = ROOT / COMMIT / 'published-entrypoints/run_selected.py'
    need(fp(entrypoint) == DRIVER_FP, 'RETAINED_O_ENTRYPOINT_DIFFERS')
    driver = ModuleType('original_O_read_only_acceptance')
    driver.__file__ = str(entrypoint)
    exec(compile(raw, str(entrypoint), 'exec'), driver.__dict__)
    need((driver.REPO, driver.PROJECT, driver.ROOT) == (REPO, PROJECT, ROOT), 'ENVIRONMENT_DIFFERS')
    s = driver.helpers()
    manifest_raw = driver.git_file(COMMIT, MANIFEST)
    need(raw_fp(manifest_raw) == MANIFEST_FP, 'ORIGINAL_O_MANIFEST_DIFFERS')
    manifest = json.loads(manifest_raw)
    original = driver.git_file(COMMIT, TARGET.replace('.', '/') + '.lean')
    need(raw_fp(original) == SOURCE_FP and
         (PROJECT / (TARGET.replace('.', '/') + '.lean')).read_bytes() == original,
         'ALLK_SOURCE_PREIMAGE_DIFFERS')
    repairs = [
        (b'    \xc2\xb7 exact fun hp => hbad (Or.inl hp)\n    \xc2\xb7 exact fun hpp => hbad (Or.inr \xe2\x9f\xa8hpp, fun hp => hbad (Or.inl hp)\xe2\x9f\xa9)\n',
         '    · exact hbad.1\n    · exact fun hpp => hbad.1 (hbad.2 hpp)\n'.encode()),
        ('  · simpa [List.getD_eq_getElem _ _ hi, hget] using hnpe\n  · simpa [List.getD_eq_getElem _ _ hi, hget] using hcoeff\n'.encode(),
         '  · simpa only [List.getD_eq_getElem _ _ hi, hget] using hnpe\n  · simpa only [List.getD_eq_getElem _ _ hi, hget] using hcoeff\n'.encode())]
    patched = original
    for old, new in repairs:
        need(patched.count(old) == 1, 'EXACT_SPLICE_NOT_UNIQUE')
        patched = patched.replace(old, new, 1)
    need(patched == candidate, 'CANDIDATE_NOT_EXACT_TWO_SPLICES')
    base = ROOT / COMMIT
    old_run = base / 'runs/attempt-00000'
    need(fp(old_run / 'RESULT.json') == RESULT_FP and fp(old_run / 'WORKER_RESULT.json') == WORKER_FP,
         'ORIGINAL_O_RESULT_BINDING_DIFFERS')
    result = json.loads((old_run / 'RESULT.json').read_bytes())
    worker = json.loads((old_run / 'WORKER_RESULT.json').read_bytes())
    targets = result['targets']
    for record in (result, worker):
        need(record['source_commit'] == COMMIT and len(record['targets']) == 14 and
             record['targets'] == targets and targets[:2] == [PRIOR, TARGET] and
             set(targets) == set(manifest['selection_guidance']['subsequent_14_targets']) and
             record['accepted_owners'] == [PRIOR] and set(record['failures']) == {TARGET} and
             set(record['acceptance_bindings']) == {PRIOR} and
             not any(k in record for k in ['context_error', 'final_context_error', 'git_error', 'final_stock_readiness']),
             'ORIGINAL_O_PARTIAL_SCOPE_DIFFERS')
    need(result['worker_exit_code'] == 1 and result['all_selected_owners_accepted'] is False,
         'ORIGINAL_O_FAILURE_STATUS_DIFFERS')
    context_pairs = {}
    for stem in ('CONTEXT', 'GIT'):
        before, after = fp(old_run / (stem + '_BEFORE.json')), fp(old_run / (stem + '_AFTER.json'))
        need(before is not None and before == after, 'ORIGINAL_O_CONTEXT_CHANGED')
        context_pairs[stem] = {'before': before, 'after': after}

    stage = 'original_PerGroup_O_full_acceptance_read'
    spec = driver.preflight(s, COMMIT, [PRIOR])
    need(len(spec.active) == 69 and TARGET not in spec.active and set(spec.initial_owners) == {PRIOR},
         'PERGROUP_ORIGINAL_SCOPE_DIFFERS')
    driver.require_completed_existing_owner(s, COMMIT, spec, PRIOR, spec.initial_owners[PRIOR])
    accepted = driver.acceptance_binding(s, COMMIT, PRIOR)
    need(accepted == result['acceptance_bindings'][PRIOR], 'PERGROUP_ORIGINAL_ACCEPTANCE_CHANGED')
    audit_id = '370ebae525106ac7bd2e'
    audit = base / PRIOR / 'audits' / audit_id
    audit_result = json.loads((audit / 'lane-0/VALIDATION_RESULTS.json').read_bytes())
    need((audit_result['total_owned_exports'], audit_result['total_public_exports']) == (68, 58),
         'PERGROUP_ACTUAL_COUNTS_DIFFER')
    receipts = {
        'normal': base / PRIOR / 'normal' / PRIOR / 'NORMAL_PASS.json',
        'audit_plan': audit / 'AUDIT_PLAN.json',
        'audit_result': audit / 'lane-0/VALIDATION_RESULTS.json',
        'owned_exports': audit / 'lane-0/OWNED_EXPORTS.json',
        'owned_log': audit / 'lane-0/all-owned-types-axioms.log',
        'reused_normal_evidence': audit / 'lane-0/REUSED_NORMAL_EVIDENCE.json'}
    receipt_bindings = {k: fp(v) for k, v in receipts.items()}
    need(all(receipt_bindings.values()), 'PERGROUP_SIX_RECEIPTS_MISSING')
    watch = sorted(driver.TARGETS)
    sources = {m: fp(PROJECT / (m.replace('.', '/') + '.lean')) for m in watch}
    artifacts = {m: driver.module_artifacts(s, m) for m in watch}
    setup = '.lake/build/ir/' + TARGET.replace('.', '/') + '.setup.json'
    need({p: v for p, v in artifacts[TARGET].items() if v is not None} == {setup: SETUP_FP},
         'ALLK_FAILED_ARTIFACTS_NOT_EXACT_SETUP_ONLY')
    normal_pass = base / TARGET / 'normal' / TARGET / 'NORMAL_PASS.json'
    need(fp(normal_pass) is None, 'ALLK_NORMAL_PASS_ALREADY_PRESENT')
    retained = {p: fp(p) for p in base.rglob('*') if p.is_file()}
    need(all(retained.values()), 'ORIGINAL_EVIDENCE_MISSING')
    environment = driver.environment(s, spec.review)
    git = s.d.original_git_state(REPO)

    def unchanged():
        need(driver.snapshot(s, spec) == spec.baseline, 'ORIGINAL_DEPENDENCY_CONTEXT_CHANGED')
        need({m: fp(PROJECT / (m.replace('.', '/') + '.lean')) for m in watch} == sources,
             'WATCH_SOURCE_CHANGED')
        need({m: driver.module_artifacts(s, m) for m in watch} == artifacts, 'WATCH_ARTIFACT_CHANGED')
        need(driver.acceptance_binding(s, COMMIT, PRIOR) == accepted, 'PERGROUP_ACCEPTANCE_CHANGED')
        need(all(fp(p) == pin for p, pin in retained.items()), 'ORIGINAL_EVIDENCE_CHANGED')
        need(fp(normal_pass) is None, 'ALLK_NORMAL_PASS_APPEARED')
        need(driver.environment(s, spec.review) == environment, 'RUNTIME_CONFIGURATION_CHANGED')
        need(s.d.original_git_state(REPO) == git, 'GIT_STATE_CHANGED')

    unchanged()
    public = {
        'schema': 'p15_O_original_accepted_prefix_public_acceptance_v1',
        'status': 'ORIGINAL_O_ACCEPTED_OWNERS_REVALIDATED_WITHOUT_EXECUTION',
        'source_commit': COMMIT, 'source_anchor_commit': ANCHOR, 'compiler_job': JOB,
        'original_run': 'runs/attempt-00000', 'published_source_count': 360,
        'driver': {'commit': COMMIT, 'path': DRIVER, **DRIVER_FP},
        'source_manifest': {'commit': COMMIT, 'path': MANIFEST, **MANIFEST_FP},
        'original_result': RESULT_FP, 'original_worker_result': WORKER_FP,
        'original_targets': targets, 'original_group_live_closure_count': 157,
        'selected_owner_live_closure_count': 69, 'preserved_dependency_count': 68,
        'selected_owners_revalidated': [PRIOR], 'original_group_accepted_owners': [PRIOR],
        'original_group_failed_modules': [TARGET], 'original_group_not_started_modules': targets[2:],
        'original_group_not_accepted_modules': targets[1:], 'original_group_worker_exit_code': 1,
        'original_group_all_selected_owners_accepted': False,
        'original_context_pairs': context_pairs,
        'original_final_stock_readiness': {'recorded': False,
            'reason': 'original_attempt_stopped_after_owner_failure', 'executed_again_by_collector': False},
        'owners': {PRIOR: {'source_commit': COMMIT, 'source_sha256': spec.sources[PRIOR],
            'owned_count': 68, 'public_count': 58, 'audit_id': audit_id, 'receipt_bindings': receipt_bindings,
            'normal_kernel_full_owned_revalidated_without_execution': True,
            'source_plus_five_and_all_21_artifacts_bound_to_original_result': True,
            'receipt_rebound_to_current_commit': False}},
        'source_runtime_and_original_receipts_unchanged': True, 'normal_or_kernel_commands_executed': 0,
        'types_or_archives_exported': False, 'axiom_union_exported': False, 'whole_P1_5_complete': False}
    attempt = s.d.attempt(PROBE_ROOT / COMMIT / 'runs')
    s.d.save(attempt / 'PERGROUP_O_PUBLIC_ACCEPTANCE.json', public)
    stage = 'one_serialized_guarded_AllK_whole_module_probe'
    probe = attempt / 'AllKLambdaChartCorrectionProbe.lean'
    s.d.write_frozen(probe, candidate)
    suffixes = ['.olean', '.olean.private', '.olean.server', '.ilean', '.ir', '.ir.sig', '.c', '.bc', '.o']
    need(all(not os.path.lexists(probe.with_suffix(ext)) for ext in suffixes), 'PROBE_OUTPUT_ALREADY_EXISTS')
    command = s.h.serialize(0, attempt / 'PROBE_LANE.json',
        s.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(probe)]))
    outcome = s.ops.run(attempt, 'serialized-whole-allk-probe', command, cwd=PROJECT, relay=False)
    unchanged()
    need(fp(probe) == CANDIDATE_FP and all(not os.path.lexists(probe.with_suffix(ext)) for ext in suffixes),
         'PROBE_SOURCE_OR_OUTPUT_CHANGED')
    need(outcome['actual_built_modules'] == [] and outcome['actual_failed_modules'] == [],
         'PROBE_ATTEMPTED_PROJECT_BUILD')
    log = Path(outcome['log'])
    result = {'schema': 'p15_AllK_actual_whole_module_api_probe_v1',
        'source_base_commit': COMMIT, 'exit_code': outcome['exit_code'],
        'candidate': {'path': str(probe), **CANDIDATE_FP}, 'original_source': SOURCE_FP,
        'whole_original_module_submitted': True, 'exact_two_proof_splices_only': True,
        'Lean_typecheck_commands': 1, 'original_serializer_and_guard_used': True,
        'lake_no_build_env_lean': True, 'output_object_requested': False,
        'existing_project_modules_rebuilt': [], 'log': {'path': str(log), **fp(log)},
        'compiler_output': log.read_text(), 'original_PerGroup_full_acceptance_preserved': True,
        'watched_source_count': len(watch), 'watched_artifact_slot_count': len(watch) * 21,
        'all_original_O_evidence_unchanged': True, 'runtime_configuration_and_Git_state_unchanged': True,
        'normal_or_kernel_acceptance_claimed': False, 'whole_P1_5_complete': False}
    s.d.save(attempt / 'ACTUAL_ALLK_PROBE_RESULT.json', result)
    return {'status': 'ALLK_WHOLE_MODULE_PROBE_SUCCEEDED' if outcome['exit_code'] == 0 else 'ALLK_PROBE_FAILED',
        'public_acceptance_path': str(attempt / 'PERGROUP_O_PUBLIC_ACCEPTANCE.json'),
        'public_acceptance': public, 'probe': result, 'new_owner_acceptance': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--candidate', type=Path, required=True)
    args = parser.parse_args()
    for key, value in {'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'}.items():
        os.environ[key] = value
    try:
        with quiet():
            result = run(args.candidate)
    except Exception as error:
        result = {'status': 'HOLD', 'stage': stage, 'failure_class': type(error).__name__,
                  'reason': str(error), 'new_owner_acceptance': False}
    print(json.dumps(result, ensure_ascii=False, sort_keys=True), flush=True)
    return 0 if result['status'] == 'ALLK_WHOLE_MODULE_PROBE_SUCCEEDED' else 3


if __name__ == '__main__':
    raise SystemExit(main())
