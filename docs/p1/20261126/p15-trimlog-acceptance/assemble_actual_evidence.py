from pathlib import Path
import hashlib
import json

ACTUAL = Path('/tmp/p15-ai-actual')
OUT = Path('/tmp/p15-aj-publication')
AI = '6d9072f7b33332eaf5ecfff22876e0404cd6ab51'
AH = 'c8ef05d421f8ba388aadc6d7d24c626ff40c9c14'
MODULE = 'ImbalancedChen.P1OriginalSingletonAtlasTrimLogAccuracy'
PUBLIC_PATH = 'docs/p1/20261125/p15-current-public-acceptance/TRIMLOG_AI_PUBLIC_ACCEPTANCE.json'


def read(name):
    return json.loads((ACTUAL / name).read_bytes())


def fingerprint(path):
    raw = Path(path).read_bytes()
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def pure(row):
    return {key: row[key] for key in ('bytes', 'sha256')}


def save(name, value):
    raw = (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + '\n').encode()
    path = OUT / name
    assert not path.exists(), 'do not overwrite frozen evidence: ' + str(path)
    path.write_bytes(raw)
    return fingerprint(path)


meta = read('ACTUAL_TRIMLOG_METADATA.json')
result = read('TRIMLOG_AI_RESULT.json')
installation = read('TRIMLOG_AI_SOURCE_INSTALL_RESULT.json')
checked = read('ACTUAL_TRIMLOG_ACCEPTANCE_READ.json')
formal_task = read('TRIMLOG_FORMAL_TASK.json')
install_task = read('TRIMLOG_INSTALL_TASK.json')
read_task = read('TRIMLOG_ACCEPTANCE_READ_TASK.json')
assert formal_task['task_id'] == 'job_192899996b69462b8499f237d9a8699c'
assert install_task['task_id'] == 'job_13e87ccb66094c66971d082f8e964d37'
assert read_task['task_id'] == 'job_3dc611cacbd2473d96a12e83eb9eaca3'
assert all(task['status'] == 'succeeded' and task['exit_code'] == 0
           for task in (formal_task, install_task, read_task))
assert result['identity']['source_commit'] == checked['identity']['source_commit'] == meta['source_commit'] == AI
assert result['accepted_owners'] == [MODULE] and result['failures'] == {} and result['new_owner_accepted'] is True
assert result['worker_exit_code'] == 0 and result['whole_P1_5_complete'] is False
assert installation['source_install_complete'] is True and installation['worker_exit_code'] == 0
assert installation['normal_or_kernel_commands_executed'] == 0 and installation['new_owner_accepted'] is False
assert checked['status'] == 'ORIGINAL_TRIMLOG_ACCEPTANCE_REVALIDATED_WITHOUT_EXECUTION'
assert checked['new_owner_accepted'] is True and checked['normal_or_kernel_commands_executed'] == 0
assert checked['owner'] == result['owner'] == meta['owner']
assert checked['preservation'] == result['preservation'] == installation['preservation']
assert (checked['active_source_count'], checked['preserved_dependency_count']) == (154, 153)
assert meta['normal_source_closure_count'] == 154
assert meta['normal_command']['exit_code'] == 0 and meta['normal_command']['actual_built_modules'] == [MODULE]
assert result['final_stock_readiness']['exit_code'] == 0
assert result['final_stock_readiness']['actual_built_modules'] == result['final_stock_readiness']['actual_failed_modules'] == []
owner = checked['owner']
assert owner['owned_count'] == owner['public_count'] == 4
assert owner['audit_id'] == '3d934c02c7fcb8f3a335'
assert owner['full_owned_including_private_generated'] is True and owner['only_standard_axioms'] is True
assert all(row['exit_code'] == 0 for row in meta['audit_summary']['kernel_commands'].values())
assert meta['audit_summary']['status'] == 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS'
for stem in ('CONTEXT', 'GIT'):
    assert pure(meta['run'][stem + '_BEFORE.json']) == pure(meta['run'][stem + '_AFTER.json'])
for stem in ('OLD_CONTEXT', 'GIT'):
    assert pure(meta['installation'][stem + '_BEFORE.json']) == pure(meta['installation'][stem + '_AFTER.json'])
for name, item in checked['accepting_run']['original_run_receipts'].items():
    if name in meta['run']:
        assert item == meta['run'][name]
for name, key in [('TRIMLOG_AI_RESULT.json', 'RESULT.json'), ('TRIMLOG_AI_WORKER_RESULT.json', 'WORKER_RESULT.json')]:
    assert fingerprint(ACTUAL / name) == pure(meta['run'][key])
for name, key in [('TRIMLOG_AI_SOURCE_INSTALL_RESULT.json', 'SOURCE_INSTALL_RESULT.json'),
                  ('TRIMLOG_AI_INSTALL_WORKER_RESULT.json', 'WORKER_RESULT.json')]:
    assert fingerprint(ACTUAL / name) == pure(meta['installation'][key])

public = {
    'schema': 'p15_independent_trimlog_original_acceptance_public_v1',
    'status': 'NORMAL_KERNEL_ALL_OWNED_ACCEPTED_AND_READ_BACK',
    'module': MODULE,
    'source_commit': AI,
    'source_identity': checked['identity'],
    'compiler_job': formal_task['task_id'],
    'original_accepting_run': checked['accepting_run'],
    'owned_count': owner['owned_count'],
    'public_count': owner['public_count'],
    'audit_id': owner['audit_id'],
    'only_standard_axioms': True,
    'full_owned_including_private_generated': True,
    'owner_binding': owner['binding'],
    'normal_command': meta['normal_command'],
    'normal_exit_code': 0,
    'kernel_exit_codes': {module: row['exit_code'] for module, row in meta['audit_summary']['kernel_commands'].items()},
    'final_stock_exit_code': 0,
    'active_source_count': 154,
    'preserved_dependency_count': 153,
    'source_installation': {'compiler_job': install_task['task_id'],
        'original_receipt': meta['installation']['SOURCE_INSTALL_RESULT.json'],
        'binding': checked['independent_source_installation']},
    'read_only_revalidation': {'compiler_job': read_task['task_id'], 'normal_or_kernel_commands_executed': 0,
        'read': fingerprint(ACTUAL / 'ACTUAL_TRIMLOG_ACCEPTANCE_READ.json')},
    'original_21_registry': {'total': 21, 'accepted': 18, 'proper_power_HOLD': 3, 'modified': False},
    'additional_owner_outside_original_21': True,
    'whole_P1_complete': False,
    'whole_P1_5_complete': False,
}
public_fp = save('TRIMLOG_AI_PUBLIC_ACCEPTANCE.json', public)
prior_ledger = Path('/tmp/p15-ag-status/STATUS_LEDGER.json')
assert fingerprint(prior_ledger) == {'bytes': 79673,
    'sha256': 'acc2f14b465d659a5ed42a2632f5f0140051819e1630396640449cee7a467d33'}
status = {
    'schema': 'p15_after_independent_trimlog_actual_status_v1',
    'whole_P1_complete': False, 'whole_P1_5_complete': False,
    'original_21_registry': {'total': 21, 'accepted': 18,
        'held': ['ImbalancedChen.P1OriginalSingletonProperPower',
                 'ImbalancedChen.P1OriginalHistoricalProperPower',
                 'ImbalancedChen.P1OriginalSingletonAtlasProperPower'],
        'unchanged_original_ledger': {'commit': AH,
            'path': 'docs/p1/20261126/p15-ag-status/STATUS_LEDGER.json', **fingerprint(prior_ledger)}},
    'additional_accepted_owners': {MODULE: {'source_commit': AI, 'compiler_job': formal_task['task_id'],
        'owned_count': 4, 'public_count': 4, 'audit_id': owner['audit_id'],
        'public_acceptance': {'path': PUBLIC_PATH, **public_fp}}},
    'new_mathematical_conclusions': {
        'rough_prime_reserve': 'Original singleton rough-prime reserve is eventually exactly zero for fixed K >= 1 and profile kappa < 1; AG original acceptance is preserved.',
        'atlas_trim': 'For fixed 0 < kap0 < 1, A : Nat and eps > 0, the original trim signed discrepancy is eventually <= eps*N/log(N)^A, uniformly over profile kap, B, Q subset [1,N] and real rho with abs(rho q) <= 1.',
        'same_parameter_limit': 'If kap0 = kap, fix that common parameter before choosing the threshold; no uniformity over a varying common parameter is claimed.'},
    'remaining_boundaries': {
        'literal_historical_medium': 'OPEN: same-source physical/coefficient dictionary and full signed bound for the actual literal medium carrier remain missing.',
        'remaining_type_I': 'SOURCE ONLY: RemainingTypeIPaid still imports unaccepted RemainingRectangles, RetainedFourierInvoice and OneLongConsumer; original FixedM source boundary remains.',
        'proper_power': 'P1 acceptance HOLD: original three targets still require the 19 unaccepted P3 dependencies in the fixed registry; no new receiver acceptance or guard weakening was performed.',
        'hSmoothSignedPP': 'Still a hypothesis of the existing conditional synthesis; the new Atlas trim bound is not the full smooth signed PP estimate.',
        'exact_medium_residual': 'SOURCE ONLY: its TrimLog direct import is now accepted, but RemainingTypeIPaid and AtlasCorrectionReduction/proper-power imports are still not ready.'},
    'next_fully_unblocked_existing_successor': None,
    'bounded_successor_check': 'Only the existing ExactMediumResidual draft directly imports TrimLog in the checked P1 drafts/local project; its other two import branches remain blocked.',
    'old_snapshots_and_accepting_identities_rebound': False,
}
status_fp = save('STATUS_AFTER_TRIMLOG_AI.json', status)
verification = {
    'schema': 'p15_trimlog_actual_root_evidence_verification_v1',
    'source_commit': AI, 'normal_and_full_owned_kernel_and_final_stock_passed': True,
    'read_only_revalidation_passed': True, 'no_old_owner_recompiled': True,
    'raw_RESULT_and_WORKER_reconstructions_match_cloud_fingerprints': True,
    'original_accepting_commit_run_and_audit_preserved': True,
    'source_plus_five_outputs_and_full21_binding_match_original_formal_run': True,
    'normal_actual_built_modules': meta['normal_command']['actual_built_modules'],
    'source_count': 154, 'dependency_count': 153,
    'normal_seconds': meta['normal_command']['elapsed_seconds'],
    'formal_task_seconds': formal_task['runtime_seconds'],
    'read_task_seconds': read_task['runtime_seconds'],
    'public_acceptance': public_fp, 'status': status_fp,
    'inputs': {name: fingerprint(ACTUAL / name) for name in (
        'ACTUAL_TRIMLOG_METADATA.json', 'TRIMLOG_AI_RESULT.json', 'TRIMLOG_AI_WORKER_RESULT.json',
        'TRIMLOG_AI_SOURCE_INSTALL_RESULT.json', 'TRIMLOG_AI_INSTALL_WORKER_RESULT.json',
        'ACTUAL_TRIMLOG_ACCEPTANCE_READ.json', 'TRIMLOG_FORMAL_TASK.json',
        'TRIMLOG_INSTALL_TASK.json', 'TRIMLOG_ACCEPTANCE_READ_TASK.json')},
    'whole_P1_5_complete': False,
}
verification_fp = save('ROOT_ACTUAL_VERIFICATION.json', verification)
print(json.dumps({'public': public_fp, 'status': status_fp, 'verification': verification_fp}, sort_keys=True))
