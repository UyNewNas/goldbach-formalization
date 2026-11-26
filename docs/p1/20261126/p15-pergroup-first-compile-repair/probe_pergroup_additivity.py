#!/usr/bin/env python3
"""One original guarded, serialized no-output typecheck of the whole PerGroup candidate."""
import argparse
from contextlib import contextmanager, redirect_stderr, redirect_stdout
from pathlib import Path
from types import ModuleType
import hashlib
import io
import json
import os
import subprocess
import sys

sys.dont_write_bytecode = True
COMMIT = '54c6e72732ce3a6d209960c396956f9cb2fe3f59'
TARGET = 'ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward'
LICENSED = 'ImbalancedChen.P5LicensedOriginalIntegerProfile'
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PROBE_ROOT = Path('/workspace/p1-complete-proof/20261126-p15-pergroup-additivity-probe-v1')
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
DRIVER_FP = {'bytes': 72984, 'sha256': 'a956f87fa00e360156c6e10dba3de857e038486b7e6a97aefebfe80e9a05ccfa'}
SOURCE_FP = {'bytes': 9091, 'sha256': '090fc6f2140dcb74a01865d25f7c8158364cf31d2b6300884cd6d35f870730d9'}
CANDIDATE_FP = {'bytes': 9093, 'sha256': '83ac50b41f5927c3e408611cb01cdc5d3712d730b49a507923179eba951606d6'}
METADATA_FP = {'bytes': 16785, 'sha256': 'b856e08909252321dec83fb415f7d62359a12bb7f1d14a67d9a7606961c7f74b'}
PUBLIC_FP = {'bytes': 6083, 'sha256': '6707a719bc053d687a6ad0a170990a43757b9945d80d124c7cf6f014fad5a543'}
WATCH = [TARGET, LICENSED, 'ImbalancedChen.P5OriginalPrimeChartHBWitnesses',
         'ImbalancedChen.P1OriginalSingletonCutoffData', 'ImbalancedChen.P1OriginalSingletonSupportData']
stage = 'public_inputs'


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def fp_bytes(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def fp(path):
    path = Path(path)
    if not os.path.lexists(path):
        return None
    need(path.is_file() and not path.is_symlink(), 'EXPECTED_REGULAR_FILE')
    return fp_bytes(path.read_bytes())


@contextmanager
def quiet_helpers():
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


def run(args):
    global stage
    need(__debug__, 'OPTIMIZED_PYTHON_REFUSED')
    for path, pin in [(args.candidate, CANDIDATE_FP), (args.metadata, METADATA_FP),
                      (args.licensed_public, PUBLIC_FP)]:
        need(fp(path) == pin, 'PUBLIC_INPUT_FINGERPRINT_DIFFERS')
    candidate = args.candidate.read_bytes()
    metadata = json.loads(args.metadata.read_bytes())
    public = json.loads(args.licensed_public.read_bytes())
    need(metadata['source_commit'] == COMMIT and metadata['normal_exit_code'] == 1 and
         metadata['accepted_owners_from_original_result'] == [LICENSED], 'M_FAILURE_SCOPE_DIFFERS')
    need(public['source_commit'] == COMMIT and public['selected_owners_revalidated'] == [LICENSED] and
         public['original_group_worker_exit_code'] == 1 and
         public['original_group_failed_modules'] == [TARGET] and
         public['original_group_all_selected_owners_accepted'] is False, 'M_PARTIAL_IDENTITY_DIFFERS')
    raw = subprocess.check_output(['git', 'show', COMMIT + ':' + DRIVER], cwd=REPO, stderr=subprocess.PIPE)
    need(fp_bytes(raw) == DRIVER_FP, 'PUBLISHED_M_DRIVER_DIFFERS')
    entrypoint = ROOT / COMMIT / 'published-entrypoints/run_selected.py'
    need(fp(entrypoint) == DRIVER_FP, 'ORIGINAL_ENTRYPOINT_DIFFERS')
    driver = ModuleType('M_PerGroup_no_output_probe_reader')
    driver.__file__ = str(entrypoint)
    exec(compile(raw, str(entrypoint), 'exec'), driver.__dict__)
    need((driver.REPO, driver.PROJECT, driver.ROOT) == (REPO, PROJECT, ROOT), 'ENVIRONMENT_PATH_DIFFERS')
    s = driver.helpers()
    source_path = PROJECT / (TARGET.replace('.', '/') + '.lean')
    old = driver.git_file(COMMIT, TARGET.replace('.', '/') + '.lean')
    need(fp_bytes(old) == SOURCE_FP and source_path.read_bytes() == old, 'LIVE_SOURCE_PREIMAGE_DIFFERS')
    old_line = b'      simp_rw [ih,mul_add,Finset.sum_add_distrib]\n'
    new_line = b'      simp only [ih,mul_add,Finset.sum_add_distrib]\n'
    need(old[7125:7175] == old_line and old[:7125] + new_line + old[7175:] == candidate,
         'CANDIDATE_IS_NOT_THE_SINGLE_EXACT_SPLICE')
    need(candidate.splitlines()[0] == b'import ImbalancedChen.P5LicensedOriginalIntegerProfile',
         'CANDIDATE_IMPORT_DIFFERS')
    preserved = {Path(row['path']): {'bytes': row['bytes'], 'sha256': row['sha256']}
                 for row in metadata['failed_evidence']}
    need(len(preserved) == 18 and all(fp(p) == pin for p, pin in preserved.items()), 'M_FAILURE_EVIDENCE_DIFFERS')

    stage = 'original_Licensed_normal_and_full_owned_acceptance'
    # PerGroup has retained failed setup; it is NOT passed to a fresh-owner gate.
    # The unchanged original preflight is actually called only for the accepted supplier.
    spec = driver.preflight(s, COMMIT, [LICENSED])
    need(len(spec.active) == 68 and TARGET not in spec.active and
         set(spec.initial_owners) == {LICENSED}, 'LICENSED_SELECTED_SCOPE_DIFFERS')
    driver.require_completed_existing_owner(s, COMMIT, spec, LICENSED, spec.initial_owners[LICENSED])
    accepted = driver.acceptance_binding(s, COMMIT, LICENSED)
    need(accepted == metadata['accepted_owner_bindings'][LICENSED], 'LICENSED_ORIGINAL_M_BINDING_DIFFERS')
    owner = public['owners'][LICENSED]
    need((owner['owned_count'], owner['public_count'], owner['audit_id']) ==
         (33, 33, '43cb6e04e72ce50bfc8e'), 'LICENSED_PUBLIC_COUNTS_OR_AUDIT_DIFFER')
    base = ROOT / COMMIT / LICENSED
    audit = base / 'audits' / owner['audit_id']
    receipt_paths = {'normal': base / 'normal' / LICENSED / 'NORMAL_PASS.json',
        'audit_plan': audit / 'AUDIT_PLAN.json', 'audit_result': audit / 'lane-0/VALIDATION_RESULTS.json',
        'owned_exports': audit / 'lane-0/OWNED_EXPORTS.json',
        'owned_log': audit / 'lane-0/all-owned-types-axioms.log',
        'reused_normal_evidence': audit / 'lane-0/REUSED_NORMAL_EVIDENCE.json'}
    for name, path in receipt_paths.items():
        need(fp(path) == owner['receipt_bindings'][name], 'LICENSED_PRIVATE_RECEIPT_PIN_DIFFERS')
        preserved[path] = owner['receipt_bindings'][name]
    sources = {m: fp(PROJECT / (m.replace('.', '/') + '.lean')) for m in WATCH}
    need(all(sources[m]['sha256'] == spec.sources[m] for m in WATCH), 'WATCH_SOURCE_DIFFERS_FROM_M')
    artifacts = {m: driver.module_artifacts(s, m) for m in WATCH}
    need(artifacts[TARGET] == metadata['artifacts'] and
         artifacts[LICENSED] == accepted['all_observed_target_artifacts'], 'OBSERVED_TARGET_ARTIFACTS_DIFFER')
    setup = '.lake/build/ir/' + TARGET.replace('.', '/') + '.setup.json'
    need({p: v for p, v in artifacts[TARGET].items() if v is not None} ==
         {setup: {'bytes': 6328419, 'sha256': 'c6fb3ebc059387bb4cbb2f009b23ed377a01a9f0e575767c1bda8ae3efe5d63a'}},
         'FAILED_SETUP_SHAPE_DIFFERS')
    normal_pass = ROOT / COMMIT / TARGET / 'normal' / TARGET / 'NORMAL_PASS.json'
    need(fp(normal_pass) is None, 'FAILED_OWNER_NORMAL_PASS_PRESENT')
    source_five = {m: s.d.snapshot(PROJECT, m) for m in WATCH[1:]}
    git_before = s.d.original_git_state(REPO)
    environment_before = driver.environment(s, spec.review)

    def unchanged():
        need(driver.snapshot(s, spec) == spec.baseline, 'LICENSED_DEPENDENCY_CONTEXT_CHANGED')
        need({m: fp(PROJECT / (m.replace('.', '/') + '.lean')) for m in WATCH} == sources,
             'WATCH_SOURCE_CHANGED')
        need({m: driver.module_artifacts(s, m) for m in WATCH} == artifacts, 'WATCH_ARTIFACT_CHANGED')
        need({m: s.d.snapshot(PROJECT, m) for m in WATCH[1:]} == source_five, 'ACCEPTED_SOURCE_FIVE_CHANGED')
        need(all(fp(p) == pin for p, pin in preserved.items()), 'ORIGINAL_RECEIPT_CHANGED')
        need(fp(normal_pass) is None, 'FAILED_OWNER_NORMAL_PASS_APPEARED')
        need(driver.environment(s, spec.review) == environment_before, 'RUNTIME_CONFIGURATION_CHANGED')
        need(s.d.original_git_state(REPO) == git_before, 'GIT_STATE_CHANGED')

    unchanged()
    stage = 'one_original_serialized_guarded_whole_module_probe'
    attempt = s.d.attempt(PROBE_ROOT / COMMIT / 'runs')
    probe = attempt / 'PerGroupIntegerHBAtlasPushforwardProbe.lean'
    s.d.write_frozen(probe, candidate)
    s.d.save(attempt / 'RUNTIME_BEFORE.json', environment_before)
    s.d.save(attempt / 'GIT_BEFORE.json', git_before)
    suffixes = ['.olean', '.olean.private', '.olean.server', '.ilean', '.ir', '.ir.sig', '.c', '.bc', '.o']
    need(all(not os.path.lexists(probe.with_suffix(ext)) for ext in suffixes), 'PROBE_OUTPUT_ALREADY_EXISTS')
    command = s.h.serialize(0, attempt / 'PROBE_LANE.json',
        s.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(probe)]))
    outcome = s.ops.run(attempt, 'serialized-whole-pergroup-probe', command, cwd=PROJECT, relay=False)
    unchanged()
    need(fp(probe) == CANDIDATE_FP and
         all(not os.path.lexists(probe.with_suffix(ext)) for ext in suffixes), 'PROBE_SOURCE_OR_OUTPUT_CHANGED')
    need(outcome['actual_built_modules'] == [] and outcome['actual_failed_modules'] == [],
         'PROBE_ATTEMPTED_A_PROJECT_BUILD')
    log_path = Path(outcome['log'])
    log_pin = {'bytes': outcome['log_bytes'], 'sha256': outcome['log_sha256']}
    need(fp(log_path) == log_pin, 'PROBE_LOG_DIFFERS')
    log = log_path.read_bytes()
    result = {'schema': 'p15_PerGroup_actual_whole_module_additivity_probe_v1',
        'source_base_commit': COMMIT, 'exit_code': outcome['exit_code'],
        'probe_source': {'path': str(probe), **CANDIDATE_FP},
        'whole_original_PerGroup_module_submitted': True, 'exact_single_tactic_splice_only': True,
        'Lean_typecheck_commands': 1, 'original_serializer_and_guard_used': True,
        'lake_no_build_env_lean': True, 'output_object_requested': False,
        'existing_project_modules_rebuilt': [], 'log': {'path': str(log_path), **log_pin},
        'compiler_output_prefix': log[:6000].decode('utf-8', 'ignore'),
        'compiler_output_truncated_in_public_report': len(log) > 6000,
        'five_sources_and_105_artifacts_unchanged': True,
        'Licensed_original_M_33_owned_acceptance_preserved': True,
        'older_accepted_source_five_and_21_artifacts_unchanged': True,
        'eighteen_original_M_failure_records_and_six_Licensed_receipts_unchanged': True,
        'runtime_configuration_and_Git_state_unchanged': True,
        'normal_or_kernel_acceptance_claimed': False}
    s.d.save(attempt / 'ACTUAL_PROBE_RESULT.json', result)
    s.d.save(attempt / 'RUNTIME_AFTER.json', driver.environment(s, spec.review))
    s.d.save(attempt / 'GIT_AFTER.json', s.d.original_git_state(REPO))
    return {'status': 'WHOLE_PERGROUP_PROBE_SUCCEEDED_NO_OWNER_OUTPUT' if outcome['exit_code'] == 0 else 'HOLD_PROBE_FAILED',
            'probe': result, 'new_owner_acceptance': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--candidate', type=Path, required=True)
    parser.add_argument('--metadata', type=Path, required=True)
    parser.add_argument('--licensed-public', type=Path, required=True)
    args = parser.parse_args()
    for key, value in {'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'}.items():
        os.environ[key] = value
    try:
        with quiet_helpers():
            result = run(args)
    except Exception as error:
        result = {'status': 'HOLD', 'stage': stage, 'failure_class': type(error).__name__,
                  'new_owner_acceptance': False}
    raw = (json.dumps(result, sort_keys=True) + '\n').encode()
    need(len(raw) <= 10000, 'PUBLIC_OUTPUT_BUDGET_EXCEEDED')
    sys.stdout.buffer.write(raw)
    sys.stdout.buffer.flush()
    return 0 if result['status'] == 'WHOLE_PERGROUP_PROBE_SUCCEEDED_NO_OWNER_OUTPUT' else 3


if __name__ == '__main__':
    raise SystemExit(main())
