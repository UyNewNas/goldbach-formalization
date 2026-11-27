from pathlib import Path
import hashlib
import json
import shutil
import zipfile

ROOT = Path('/workspace/scratch/c397bfd2830f')
STAGE = ROOT / 'p29-package-resume'
REL = Path('docs/verification/20261127-p2-9-standard-package-resume')
OUT = STAGE / REL
BUILDER = ROOT / 'p29-v5-builder'
PREVIOUS = ROOT / 'p29-observation-resume'


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def identity(path):
    data = path.read_bytes()
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
            'git_blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()}


for file in ['postimage.py', 'bootstrap.py', 'V4_TO_V5.patch', 'STATIC_BINDING.json']:
    dest = OUT / 'v5-controller' / file
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(BUILDER / 'generated-final' / file, dest)
for file in ['build_v5.py', 'main_delta.py', 'cache_inputs.py', 'test_build_v5.py',
             'test_cache_inputs.py', 'PLAN.md', 'PROGRESS.md', 'prepare_packet.py']:
    dest = OUT / 'builder' / file
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(BUILDER / file, dest)

old_rel = Path('docs/verification/20261127-p2-9-omitted-observation-resume')
for file in ['ACTUAL_OUTCOME.json', 'ACTUAL_TERMINAL_TASK.json', 'ACTUAL_STDOUT.log', 'GITHUB_RECEIPT.json']:
    dest = STAGE / old_rel / file
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(PREVIOUS / old_rel / file, dest)

binding = json.loads((OUT / 'v5-controller/STATIC_BINDING.json').read_text())
outcome = json.loads((PREVIOUS / old_rel / 'ACTUAL_OUTCOME.json').read_text())
continuation = {
    'schema': 'p29_standard_package_resume_v5_continuation_v1',
    'status': 'REVIEWED_LOCAL_CODE_PENDING_PINNED_PUBLICATION_AND_UNIQUE_SUBMISSION',
    'previous_job': outcome['job_id'],
    'previous_status': outcome['status'],
    'previous_failure': outcome['missing_object'],
    'target': 'ImbalancedChen.P2FiniteMarkedGamma5OmittedPrimeWall',
    'source_blob': 'ef40c77ee9b4c58a8e4761b21fafdfe867f85d8e',
    'source_sha256': '4bf64e2d4fdb45755716cd1614db4059afcefa2ca0e6d5e230252408264e1c9c',
    'source_bytes': 7887,
    'source_changed': False,
    'postimage': binding['postimage'],
    'bootstrap': binding['bootstrap'],
    'unchanged_contract_blob': '4706e5c9e9d5f93f165d50b47ad82b8588449870',
    'unchanged_contract_sha256': binding['unchanged_contract_sha256'],
    'complete_cache_probe': binding['cache_probe'],
    'compressed_cache_transport': json.loads((OUT / 'CACHE_TRANSPORT_PIN.json').read_text()),
    'new_owned_output': binding['generated_owned_output'],
    'new_Batteries_only_view': binding['generated_owned_Batteries_view'],
    'existing_package_view_unchanged': binding['unchanged_owned_package_view'],
    'Batteries_modules': 192,
    'Batteries_facets': 960,
    'Batteries_facets_freshly_hashed_by_readonly_probe': 5,
    'other_Batteries_probe_checks': 'current regular-file metadata only; full hashes of every actual used facet remain required',
    'existing_research_modules': 529,
    'excluded_AnalyticNumberTheory_probe_rows': 44,
    'Batteries_byte_authority': 'unchanged original accepted e9edf9226c45934541d576c76ca7f3041bf3c73c703e51b3162dd69dcbe68636 derived facet table',
    'restoration_receipt_role': 'auxiliary currently observed provenance, not qualification authority',
    'reused_successful_stages': binding['reused_successful_stages'],
    'original_successful_stage_reinvocations': 0,
    'supplier_source_kernel_owned_replays': 0,
    'new_formal_credit': 0,
    'accepted_increment_unchanged': {'modules': 23, 'owned_declarations': 501},
    'full_P2_9_complete': False,
    'signed_PP_estimate_complete': False,
    'planned_request_limits': {'cwd': '/workspace', 'memory_mb': 12800, 'cpu_threads': 2, 'timeout_seconds': 3600},
    'future_submission_requires_fresh_complete_service_observation': True,
    'remaining_acceptance': ['fresh actual imported module/header/facet identities', 'warning-as-error target normal',
                             'before/after identity stability', 'named-kernel', 'complete-owned inventory, types and axiom audit',
                             'final runtime audit', 'complete original archive reception and root review'],
}
save(OUT / 'CONTINUATION.json', continuation)
save(OUT / 'ROOT_REVIEW.json', {
    'schema': 'p29_standard_package_resume_v5_root_review_v1',
    'status': 'STATIC_REVIEW_PASS_NOT_RUNTIME_OR_PROOF_ACCEPTANCE',
    'reviewed_postimage': binding['postimage'],
    'reviewed_bootstrap': binding['bootstrap'],
    'root_read_complete_bounded_diff': True,
    'root_checked_original_guard_environment_contract': True,
    'root_checked_original_cache_selection_and_five_Lemma_facet_hashes': True,
    'accepted_table_and_current_cache_provenance_distinguished': True,
    'literal_inverse_and_helpers': binding['reviewed_helper_delta'],
    'builder_agent_validation': {'tests_passed': 31,
        'additional_final_target_sequence_regressions_passed': 2,
        'wholefile_inverse_exact': True,
        'source_and_bootstrap_syntax_passed': True,
        'scope': 'author-reported local validator tests; no controller main or Lean run'},
    'independent_bounded_review': {'reviewer': '/root/p29_controller_schema/v5_guard_review',
        'result': 'No deterministic path, guard, or known-facet failure found',
        'scope': 'read-only integration review; no Git, cloud, controller-main, or Lean execution'},
    'new_formal_credit': 0,
})

next_action = ('Publish the exact reviewed v5 bootstrap and compressed original cache probe, save the complete request, '
               'then submit one continuation with a fresh complete P2 observation. Reuse original successful gates; '
               'accept Omitted only after all target gates and complete archive review. Then bind the existing 71 old '
               'inputs plus the accepted Omitted object for Nonempty.')
for rel in [Path('docs/verification/20261126-p2-9-continuation/RESUME.json'),
            Path('docs/verification/20261125-p2-9-geometric-family/CURRENT_RUN_STATUS.json')]:
    d = json.loads((PREVIOUS / rel).read_text())
    if 'source_parent' in d:
        d['source_parent'] = 'dbea6b7c0cfc1057ee2be84c3bce1a5f30e1a243'
        d['observed_utc'] = '2026-11-27 04:40:35 UTC'
        d['observed_shanghai'] = '2026-11-27 12:40:35 Asia/Shanghai'
    if 'source_commit_before_this_packet' in d:
        d['source_commit_before_this_packet'] = 'dbea6b7c0cfc1057ee2be84c3bce1a5f30e1a243'
        d['status_sample_utc'] = '2026-11-27 04:40:35 UTC'
    p = d['P2']['omitted_input_preparation']
    ex = p['execution']
    ex['status'] = 'V4_MATHLIB_PATH_PASSED_BATTERIES_IMPORT_FAILED_V5_REVIEWED_PENDING_SUBMISSION'
    ex['latest_observed_status'] = 'failed'
    ex['resume_v4_observation_repair'].update({'current_status': 'failed', 'terminal_outcome': outcome,
        'terminal_evidence': str(old_rel / 'ACTUAL_TERMINAL_TASK.json'),
        'complete_stdout_evidence': str(old_rel / 'ACTUAL_STDOUT.log')})
    ex['resume_v5_standard_package'] = continuation
    ex['attempt_field_scope']['job_exit_code_and_original_result_fields'] = 'Preserved original 1dfcb781103d4426b860b7ffe3ebc8cd fields; use latest_job and latest_observed_status for latest submitted task.'
    ex['attempt_field_scope']['resume_v4_observation_repair'] = 'Actual a691a4c888044726ad49f92170e3c8f5 terminal failure after successful Mathlib path observation.'
    ex['attempt_field_scope']['resume_v5_standard_package'] = 'Reviewed static continuation, no submitted task or proof credit yet.'
    ex['next_action'] = p['next_action'] = next_action
    p['target_normal_start_observation'] = ('Actual a691a4c888044726ad49f92170e3c8f5 passed the Mathlib path stage '
        'and failed omitted-direct-imports at the stock Batteries/Tactic/Lemma.olean path; target normal was not started. '
        'V5 is a reviewed continuation and has not been submitted yet.')
    p['current_standard_package_view_repair'] = {'record': str(REL / 'CONTINUATION.json'),
        'status': continuation['status'], 'new_formal_credit': 0}
    d['latest_observation_repair']['latest_observed_status'] = 'failed'
    d['latest_standard_package_resume'] = {'record': str(REL / 'CONTINUATION.json'),
        'status': continuation['status'], 'new_formal_credit': 0, 'source_changed': False}
    assert d['accepted_increment']['modules'] == 23 and d['accepted_increment']['owned_declarations'] == 501
    save(STAGE / rel, d)

print(json.dumps({'staged': str(OUT), 'postimage': identity(OUT / 'v5-controller/postimage.py'),
                  'bootstrap': identity(OUT / 'v5-controller/bootstrap.py'),
                  'new_formal_credit': 0}))
