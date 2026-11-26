"""Read only the HB acceptance retained by the fixed F pair with failed Cutoff."""
from contextlib import redirect_stderr, redirect_stdout
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
os.environ['GIT_OPTIONAL_LOCKS'] = '0'
os.environ['GIT_NO_LAZY_FETCH'] = '1'
COMMIT = '080d4178711ae042235104f7f4768649f51da2ab'
COMPILER_JOB = 'job_f0761da7e6124e818d654afef54ff5c5'
REPO = Path('/workspace/goldbach-formalization')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PREFIX = 'docs/p1/20261126/p15-current-corrections/'
HB = 'ImbalancedChen.P5OriginalPrimeChartHBWitnesses'
CUTOFF = 'ImbalancedChen.P1OriginalSingletonCutoffData'
PAIR = [HB, CUTOFF]
TARGETS = [HB]
DRIVER = {'bytes': 48571, 'sha256': '9fffe0f6608eec153c5d58d8269f5ddb1b8f0552d8b862ae73b03451d4eda45c'}
MANIFEST = {'bytes': 330884, 'sha256': '12c8898624290d088a7f51065db87fefa0e7f6ee72954a7fb582a28e17f4f609'}
SOURCE_ANCHOR_E = '1103fd45507a5889d79ba1629cc36ae0e69a9672'
stage = 'unbound_F_identity'


def fingerprint(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def main():
    global stage
    if not __debug__:
        raise RuntimeError('PYTHON_OPTIMIZATION_NOT_ALLOWED')
    assert isinstance(COMMIT, str) and re.fullmatch('[0-9a-f]{40}', COMMIT)
    assert isinstance(COMPILER_JOB, str) and re.fullmatch('job_[0-9a-f]{32}', COMPILER_JOB)
    root = ROOT / COMMIT
    run = root / 'runs/attempt-00000'
    retained = {}

    def read(path):
        assert path.is_file() and path.resolve() == path
        raw = path.read_bytes()
        pin = fingerprint(raw)
        assert path not in retained or retained[path] == pin
        retained[path] = pin
        return raw

    stage = 'fixed_published_inputs'
    f = root / 'published-entrypoints/run_selected.py'
    code = read(f)
    assert fingerprint(code) == DRIVER
    assert code == subprocess.check_output(['git', 'show', COMMIT + ':' + PREFIX + 'run_selected.py'], cwd=REPO, stderr=subprocess.PIPE)
    manifest_raw = subprocess.check_output(['git', 'show', COMMIT + ':' + PREFIX + 'SOURCE_MANIFEST.json'], cwd=REPO, stderr=subprocess.PIPE)
    assert fingerprint(manifest_raw) == MANIFEST
    assert read(run / 'executed-driver.py') == code

    stage = 'original_HB_acceptance_with_only_known_Cutoff_failure'
    original = json.loads(read(run / 'RESULT.json'))
    worker = json.loads(read(run / 'WORKER_RESULT.json'))
    for record in (original, worker):
        assert record['source_commit'] == COMMIT
        assert record['accepted_owners'] == [HB]
        assert len(record['targets']) == 2 and set(record['targets']) == set(PAIR)
        assert set(record['failures']) == {CUTOFF}
        assert set(record['acceptance_bindings']) == {HB}
        assert not any(k in record for k in ['context_error', 'final_context_error', 'git_error'])
    assert original['worker_exit_code'] == 1 and original['all_selected_owners_accepted'] is False
    assert original.get('dispatch_error') == 'serialized worker exited 1'
    assert 'dispatch_error' not in worker
    assert original['failures'] == worker['failures']
    assert original['acceptance_bindings'] == worker['acceptance_bindings']
    context_pairs = {}
    for stem in ['CONTEXT', 'GIT']:
        before, after = run / (stem + '_BEFORE.json'), run / (stem + '_AFTER.json')
        assert read(before) == read(after)
        context_pairs[stem] = {'before': retained[before], 'after': retained[after]}

    stage = 'unique_original_owner_receipts'
    receipts, validations, audit_ids = {}, {}, {}
    for module in TARGETS:
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
        validations[module] = json.loads(read(paths['audit_result']))
        receipts[module] = {key: retained[path] for key, path in paths.items()}
        audit_ids[module] = audit.name
        binding = original['acceptance_bindings'][module]
        assert receipts[module]['normal'] == {key: binding['normal_receipt'][key] for key in ['bytes', 'sha256']}
        assert len(binding['audits']) == 1
        for key, name in [('audit_plan', 'plan'), ('audit_result', 'result')]:
            assert receipts[module][key] == {field: binding['audits'][0][name][field] for field in ['bytes', 'sha256']}

    stage = 'original_F_preflight_and_complete_owned_audit_readers'
    # These are the unchanged original readers. No normal, kernel, owner worker,
    # stock build, driver main or installer entrypoint is called by this script.
    # Any incidental internal reader output is kept private and discarded.
    with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
        driver = ModuleType('fixed_F_readonly_HB_reader')
        driver.__file__ = str(f)
        exec(compile(code, str(f), 'exec'), driver.__dict__)
        assert driver.SOURCE_ANCHOR == SOURCE_ANCHOR_E and driver.MANIFEST_SHA == MANIFEST['sha256']
        s = driver.helpers()
        spec = driver.preflight(s, COMMIT, TARGETS)
        assert len(spec.graph) == 360 and len(spec.active) == 67 and spec.selected == set(TARGETS)
        assert 'ImbalancedChen.P1OriginalSingletonSupportData' not in spec.active
        assert CUTOFF not in spec.active
        assert len(spec.initial_owners[HB]['artifacts']) == 21
        for module in TARGETS:
            assert spec.initial_owners[module]['artifacts'] == original['acceptance_bindings'][module]['all_observed_target_artifacts']
            driver.require_completed_existing_owner(s, COMMIT, spec, module, spec.initial_owners[module])
        assert driver.snapshot(s, spec) == spec.baseline

    owners = {}
    for module in TARGETS:
        validation = validations[module]
        owned, public = validation['total_owned_exports'], validation['total_public_exports']
        assert type(owned) is int and type(public) is int and 0 <= public <= owned
        owners[module] = {'source_commit': COMMIT, 'source_sha256': spec.sources[module],
            'audit_id': audit_ids[module], 'owned_count': owned, 'public_count': public,
            'receipt_bindings': receipts[module], 'normal_kernel_full_owned_revalidated_without_execution': True,
            'receipt_rebound_to_current_commit': False}

    stage = 'final_preservation'
    assert driver.snapshot(s, spec) == spec.baseline
    for path, expected in retained.items():
        assert path.is_file() and path.resolve() == path and fingerprint(path.read_bytes()) == expected
    for module in TARGETS:
        assert driver.module_artifacts(s, module) == spec.initial_owners[module]['artifacts']
    result = {'schema': 'p15_hb_F_original_public_acceptance_v1',
        'status': 'ORIGINAL_HB_ACCEPTANCE_REVALIDATED_WITHOUT_EXECUTION',
        'source_commit': COMMIT, 'compiler_job': COMPILER_JOB,
        'driver': {'commit': COMMIT, 'path': PREFIX + 'run_selected.py', **DRIVER},
        'source_manifest': {'commit': COMMIT, 'path': PREFIX + 'SOURCE_MANIFEST.json', **MANIFEST},
        'source_anchor_commit': SOURCE_ANCHOR_E, 'original_result': retained[run / 'RESULT.json'],
        'original_group_worker_exit_code': original['worker_exit_code'],
        'original_group_all_selected_owners_accepted': original['all_selected_owners_accepted'],
        'original_group_accepted_owners': original['accepted_owners'],
        'original_group_failed_modules': sorted(original['failures']),
        'original_group_dispatch_error': original['dispatch_error'],
        'selected_owners_revalidated': TARGETS,
        'original_worker_result': retained[run / 'WORKER_RESULT.json'],
        'original_context_pairs': context_pairs, 'owners': owners,
        'published_source_count': 360, 'selected_owner_live_closure_count': len(spec.active),
        'source_runtime_and_original_receipts_unchanged': True,
        'normal_or_kernel_commands_executed': 0, 'axiom_union_exported': False,
        'types_or_archives_exported': False, 'whole_P1_5_complete': False}
    payload = json.dumps(result, sort_keys=True, separators=(',', ':'))
    assert len(payload.encode()) + 1 <= 6144
    print(payload)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        # Never relay an original audit exception, private type, or raw log.
        print(json.dumps({'status': 'HOLD', 'stage': stage, 'failure_class': type(error).__name__,
            'normal_or_kernel_commands_executed': 0, 'new_acceptance_claimed': False}, sort_keys=True))
        raise SystemExit(3)
