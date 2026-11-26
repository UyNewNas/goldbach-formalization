# Inserted verbatim into the draft02 publication builder before state creation.
# This is local evidence validation only: no Git, compiler, audit or remote call.
SHAPE = Path('/tmp/p24-canonical-A-shape-evidence-20261126')
RETENTION = Path('/tmp/p24-diagnostic-metadata-retention-20261126')
SERIALIZED = Path('/tmp/p24-current322-serialized-names-b55-20261126')
LOGPOINT = Path('/tmp/p24-receipt-duplicates-b55-20261126/logpoint-candidate-01')
RAW_B = Path('/tmp/p24-b-rfl-diagnostic-20261126')


def read_json(path):
    return json.loads(Path(path).read_bytes())


def complete_task_log(task, path):
    raw = Path(path).read_bytes()
    assert task['status'] == 'succeeded' and task['exit_code'] == 0
    assert not task['log_truncated'] and task['log_discarded_bytes'] == 0
    assert len(raw) == task['log_bytes']
    return raw


def add_verified_blob(target, source, blob_record, expected_sha256, expected_bytes, role):
    source = Path(source)
    raw = source.read_bytes()
    assert len(raw) == expected_bytes and sha(raw) == expected_sha256
    git_sha = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
    assert blob_record['sha'] == git_sha
    assert target not in seen
    seen.add(target)
    elements.append({'path': target, 'mode': '100644', 'type': 'blob', 'sha': git_sha})
    rows.append({'path': target, 'bytes': len(raw), 'sha256': sha(raw), 'git_blob_sha': git_sha,
                 'origin': str(source), 'role': role})
    return {'path': target, 'bytes': len(raw), 'sha256': sha(raw), 'git_blob_sha': git_sha}


shape_task = read_json(SHAPE / 'original-shape-task-status.json')
complete_task_log(shape_task, SHAPE / 'original-shape-task.log')
assert shape_task['task_id'] == 'af141e9e53ef4fd591f2e320debedb5e'
shape = read_json(SHAPE / 'shape-diagnostic.json')
assert shape['source_pin'] == SOURCE and shape['canonical_A_shape_checks_passed']
assert shape['wrapper_exit_code'] == 0 and shape['block_count'] == 2048 and shape['fact_count'] == 131072
assert all(shape['postchecks'].values()) and not shape['errors']
assert not shape['canonical_audit_credit'] and not shape['independent_replay_performed']
shape_raw = gzip.decompress((SHAPE / 'blocks.stdout.log.gz').read_bytes())
assert len(shape_raw) == shape['shape_capture']['stdout_bytes'] == 32377535
assert sha(shape_raw) == shape['shape_capture']['stdout_sha256'] == '17da353c642b87270d40ccaf19803c462a1afc3ed88702cbb21ae8e8b9c2a033'
shape_summary = json.loads(gzip.decompress((SHAPE / 'complete-block-summary.json.gz').read_bytes()))
assert sorted(shape_summary['indices']) == list(range(32769, 163841))
assert len(shape_summary['indices']) == len(set(shape_summary['indices'])) == 131072
assert shape_summary['owned_block_count'] == 2048 and shape_summary['shape_checks_passed']
shape_integrity = read_json(SHAPE / 'retrieval-verification.json')
assert shape_integrity['status'] == 'passed' and shape_integrity['all_five_artifacts_exact_bytes_and_sha256_verified']
shape_blob = add_verified_blob(EVIDENCE + '/shape/blocks.stdout.log.gz', SHAPE / 'blocks.stdout.log.gz',
    read_json(SHAPE / 'blocks-stdout-blob.json'),
    '709c2f0d26d4481f2845edd7d2726e677842eda447f455297178dab7259a25d0', 7577341,
    'complete canonical A shape stdout; original diagnostic only, not the full owned gate')

retention_stage1_task = read_json(RETENTION / 'draft02/stage1-task-status.json')
stage1_log = complete_task_log(retention_stage1_task, RETENTION / 'draft02/stage1-final.log')
retention_stage1 = json.loads(stage1_log.splitlines()[-1])
assert retention_stage1['status'] == 'passed' and retention_stage1['exit_code'] == 0
assert retention_stage1['actual_xz_bytes'] == 569276 and retention_stage1['original_files_deleted'] == 0
verification_task = read_json(RETENTION / 'draft02/verification-only-final-task.json')
verification_log = complete_task_log(verification_task, RETENTION / 'draft02/verification-only-final.log')
verification = json.loads(verification_log)
assert verification_task['task_id'] == '09da25ebebca4f20a9e2b83deb106ee2'
assert verification['status'] == 'passed' and verification['exit_code'] == 0
assert verification['all_thirteen_independently_reconstructed_and_compared']
assert all(verification['postchecks'].values()) and verification['persistent_reserve_passed_after_receipt']
assert verification['original_count'] == 13
assert verification['original_files_deleted'] == verification['original_files_written'] == verification['reconstruction_markers_created'] == 0
release_block = read_json(RETENTION / 'draft02/stage2-submission-blocked.json')
assert release_block['automatic_approval_block_observed'] and release_block['no_release_task_accepted']
assert release_block['job_id'] is None and not release_block['original_files_released']

raw_b_task = read_json(RAW_B / 'raw-defeq-b55-final-task.json')
complete_task_log(raw_b_task, RAW_B / 'raw-defeq-b55-final.log')
raw_b = read_json(RAW_B / 'raw-defeq-b55-final-summary.json')
assert raw_b['exit_code'] == 0 and raw_b['diagnostic_preservation_checks_passed'] and not raw_b['errors']
returned = [x for x in raw_b['observations'] if x['phase'] == 'returned']
assert len(returned) == 1 and returned[0]['isDefEq'] is False
assert not raw_b['original_B_compile_credit'] and not raw_b['kernel_replay_credit']

logpoint_task = read_json(LOGPOINT / 'logpoint-candidate-b55-final-task.json')
complete_task_log(logpoint_task, LOGPOINT / 'logpoint-candidate-b55-final.log')
logpoint = read_json(LOGPOINT / 'logpoint-candidate-b55-final-summary.json')
assert logpoint['isolated_group_passed'] and logpoint['protected_inputs_unchanged'] and not logpoint['postcheck_errors']
assert not logpoint['canonical_source_modified'] and not logpoint['canonical_compile_credit']
assert len(logpoint['candidates']) == 1
candidate = logpoint['candidates'][0]
assert candidate['owned_count'] == 125 and candidate['duplicate_name_absent_from_all_owned_records']
assert candidate['candidate_sha256'] == 'ec8550365f6f47c8354c9b31d9c156a7f82280335a72abc6c70b024414fded58'
assert all(row['exit_code'] == 0 and not row['timed_out'] for row in candidate['stages'].values())

serialized_task = read_json(SERIALIZED / 'serialized322-b55-final-task.json')
complete_task_log(serialized_task, SERIALIZED / 'serialized322-b55-final.log')
serialized_summaries = read_json(SERIALIZED / 'serialized322-b55-final-summaries.json')
serialized = next(row['value'] for row in serialized_summaries if row['tag'] == 'P24_SERIALIZED_322_RESULT')
duplicates = next(row['value'] for row in serialized_summaries if row['tag'] == 'P24_SERIALIZED_DUPLICATES')
assert serialized['diagnostic_completed'] and serialized['exit_code'] == 0 and not serialized['errors']
assert serialized['current_compiled_scope'] == 322 and all(serialized['postchecks'].values())
assert duplicates['modules'] == 322 and duplicates['serialized_occurrences'] == 12030 and duplicates['unique_names'] == 12016
assert len(duplicates['duplicate_names']) == serialized['duplicate_count'] == 14
assert not duplicates['within_module_duplicate_names'] and not serialized['canonical_credit']

three_descriptor = read_json(SERIALIZED / 'three-diagnostic-transport-descriptor.json')
three_verification = read_json(SERIALIZED / 'three-diagnostic-transport-local-verification.json')
assert three_verification['all_member_hashes_verified'] and three_verification['member_count'] == 26
three_raw = (SERIALIZED / 'three-diagnostics-complete-evidence.tar.xz').read_bytes()
three_tar = lzma.decompress(three_raw)
assert len(three_tar) == three_descriptor['tar_bytes'] == 4065280
assert sha(three_tar) == three_descriptor['tar_sha256'] == 'f405b8a3a65d7e5513873dd989ac02347258e3059ff92ca458d38511a5121722'
with tarfile.open(fileobj=io.BytesIO(three_tar), mode='r:') as archive_reader:
    three_members = {}
    for member in archive_reader:
        assert member.isfile() and not Path(member.name).is_absolute() and '..' not in Path(member.name).parts
        assert member.name not in three_members
        three_members[member.name] = archive_reader.extractfile(member).read()
    assert len(three_members) == 26 and sum(map(len, three_members.values())) == 4036102
    three_index = json.loads(three_members['FILES.json'])
    expected = {row['name']: row for row in three_index['members']}
    assert set(expected) == set(three_members) - {'FILES.json'}
    for name, row in expected.items():
        assert len(three_members[name]) == row['bytes'] and sha(three_members[name]) == row['sha256']
    assert len(three_index['excluded']) == 1 and three_index['excluded'][0]['name'].endswith('.olean')
three_blob = add_verified_blob(EVIDENCE + '/three-diagnostics-complete-evidence.tar.xz',
    SERIALIZED / 'three-diagnostics-complete-evidence.tar.xz', read_json(SERIALIZED / 'three-diagnostic-evidence-blob.json'),
    'ab805768c0e6e4ce426bd1cc81da2a9b84b61ffaa3838ac37f0c33a7fd6f0477', 338568,
    'complete isolated LogPoint/raw-B/serialized322 evidence; one receipt-bound isolated object excluded explicitly')

native_block = read_json(ROOT / 'native-environment-block-observation-draft02.json')
assert native_block['current_acceptance_readiness'] == 'blocked_native_physical_inputs_missing'
assert native_block['qualified_snapshot_bytes'] == 20904189
assert native_block['qualified_snapshot_sha256'] == 'ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27'
assert native_block['released_by_reviewed_metadata_workflow'] is False

native_task = read_json(RAW_B / 'native-input-missing-inventory-01-task.json')
complete_task_log(native_task, RAW_B / 'native-input-missing-inventory-01.log')
native_raw = gzip.decompress((RAW_B / 'native-missing-complete-inventory.json.gz').read_bytes())
assert len(native_raw) == 14064089 and sha(native_raw) == '297f3c77f8494ac78ba5694872bf214b464bea3c601404fa2a0bf61f3251f505'
native_inventory = json.loads(native_raw)
assert native_inventory['files_count'] == 70383
assert native_inventory['counts'] == {'missing': 41505, 'present_same_size': 28878}
assert len(native_inventory['mismatches']) == 41505
assert all(row['state'] == 'missing' and row['path'].startswith('/workspace/compile-deps/mathlib/')
           for row in native_inventory['mismatches'])
assert sum(row['expected']['bytes'] for row in native_inventory['mismatches']) == 5712781792
assert native_inventory['present_same_size_sha256_not_checked']
assert native_inventory['snapshot_sha256'] == native_block['qualified_snapshot_sha256']
assert native_inventory['registry_sha256'] == native_block['registry_sha256_at_inventory']
assert native_inventory['source_pin'] == SOURCE and not native_inventory['qualification_run']
native_blob = add_verified_blob(EVIDENCE + '/native-input-incident/complete-missing-input-inventory.json.gz',
    RAW_B / 'native-missing-complete-inventory.json.gz', read_json(RAW_B / 'native-missing-complete-inventory-blob.json'),
    '371180d13bcfc651df35e9712dba3b1ce6a1bc1aa5ad1020f33e18fd0b836a57', 2034654,
    'complete observed missing native inputs; existing-size files were not rehashed and no new qualification was performed')
official_task = read_json(RAW_B / 'native-official-cache-index-probe-01-task.json')
official_log = complete_task_log(official_task, RAW_B / 'native-official-cache-index-probe-01.log')
official_attempts = [json.loads(line.removeprefix('OFFICIAL_INDEX_PROBE '))
    for line in official_log.decode().splitlines() if line.startswith('OFFICIAL_INDEX_PROBE ')]
assert len(official_attempts) == 2
assert all(row['method'] == 'GET' and 'Tunnel connection failed: 403 Forbidden' in row['error']
           for row in official_attempts)

six_path = Path('/tmp/p24-global-duplicate-repairs-b55-20261126/candidates-01/six-proof-candidates-manifest.json')
six = read_json(six_path)
assert six['source_pin'] == SOURCE and len(six['candidates']) == 6
assert not six['executed'] and not six['canonical_source_modified'] and not six['canonical_credit']
assert sum(row['patch_count'] for row in six['candidates']) == 14
assert sum(row['theorem_head_count'] for row in six['candidates']) == 109
for row in six['candidates']:
    original = Path(row['original_path']).read_bytes()
    candidate_raw = Path(row['candidate_path']).read_bytes()
    assert len(original) == row['original_bytes'] and sha(original) == row['old_sha256']
    assert len(candidate_raw) == row['candidate_bytes'] and sha(candidate_raw) == row['candidate_sha256']
    assert sha(Path(row['patch_path']).read_bytes()) == row['patch_sha256']
    restored = candidate_raw
    for replacement in reversed(row['patches']):
        old, new = replacement['old'].encode(), replacement['new'].encode()
        assert restored.count(new) == 1
        restored = restored.replace(new, old, 1)
    assert restored == original

six_wrappers_path = six_path.parent.parent / 'isolated-wrappers-01/six-isolated-wrappers-manifest.json'
six_wrappers = read_json(six_wrappers_path)
assert six_wrappers['source_pin'] == SOURCE and len(six_wrappers['wrappers']) == 6
assert not six_wrappers['executed'] and not six_wrappers['canonical_credit']
candidate_hashes = {row['module']: row['candidate_sha256'] for row in six['candidates']}
for wrapper in six_wrappers['wrappers']:
    assert wrapper['candidate_sha256'] == candidate_hashes[wrapper['original_module']]
    for key in ['shell', 'python', 'patch']:
        item = wrapper[key]
        raw = Path(item['path']).read_bytes()
        assert len(raw) == item['bytes'] and sha(raw) == item['sha256']

recovery_path = Path('/tmp/p24-native-recovery-readonly-20261126/prepared-only-verification.json')
recovery = read_json(recovery_path)
assert recovery['prepared_only'] and not recovery['compilation_run'] and not recovery['qualification_run']
assert not recovery['proof_credit'] and recovery['this_agent_native_files_written'] == 0
assert not recovery['network_probe']['official_index_existence_established']

extra_state = {
    'canonical_A_shape': {'task': shape_task, 'result': shape, 'complete': True,
        'archive': shape_blob, 'raw_stdout_bytes': 32377535,
        'raw_stdout_sha256': '17da353c642b87270d40ccaf19803c462a1afc3ed88702cbb21ae8e8b9c2a033',
        'full_owned_audit_or_independent_replay_credit': False},
    'diagnostic_metadata_preservation': {'stage1_task': retention_stage1_task, 'stage1_result': retention_stage1,
        'independent_verification_task': verification_task, 'independent_verification_result': verification,
        'release_attempt_blocked': release_block, 'original_files_released': 0,
        'remaining_excluded_metadata_count': 3, 'excluded_metadata_release_authorized': False},
    'B_raw_defeq_observation': {'task': raw_b_task, 'result': raw_b,
        'meaning': 'Meta.isDefEq returned false normally; this is not a proof that the Boolean endpoint is false.'},
    'isolated_LogPoint_contains_repair': {'task': logpoint_task, 'result': logpoint,
        'production_source_promoted': False, 'current_source_pin_unchanged_by_diagnostic': True},
    'current322_serialized_duplicate_scan_at_run_time': {'task': serialized_task, 'result': serialized,
        'duplicates': duplicates, 'counts_are_diagnostic_not_original_owned_acceptance': True},
    'complete_three_diagnostic_evidence': {'archive': three_blob, 'descriptor': three_descriptor,
        'one_receipt_bound_isolated_object_excluded': True},
    'current_native_environment_observation': native_block,
    'complete_native_missing_input_inventory': {'archive': native_blob, 'task': native_task,
        'missing_count': 41505, 'missing_expected_bytes': 5712781792, 'present_same_size_not_rehashed': 28878},
    'official_exact_commit_cache_index_probe': {'task': official_task, 'attempts': official_attempts,
        'result': 'network_tunnel_403', 'cache_absence_or_404_inferred': False,
        'access_restriction_bypass_attempted': False},
    'prepared_six_proof_candidates': {'manifest_path': str(six_path), 'manifest_sha256': sha(six_path.read_bytes()),
        'modules': 6, 'proof_blocks': 14, 'original_theorem_heads': 109,
        'all_inverse_byte_comparisons_passed': True, 'compiled': False, 'promoted': False,
        'canonical_credit': False, 'only_diagnostic_copies_published': True},
    'prepared_six_isolated_wrappers': {'manifest_path': str(six_wrappers_path),
        'manifest_sha256': sha(six_wrappers_path.read_bytes()), 'count': 6,
        'executed': False, 'canonical_credit': False},
    'exact_native_restoration_design': {'verification_path': str(recovery_path),
        'verification_sha256': sha(recovery_path.read_bytes()), 'prepared_only': True,
        'download_or_restore_executed': False,
        'current_blocked_state_cannot_be_cleared_without_the_original_full_physical_verification': True},
    'current_acceptance_readiness': 'blocked_native_physical_inputs_missing',
    'all_prior_passes_are_timestamped_receipts_not_current_environment_requalification': True,
    'new_environment_qualification_performed': False,
    'newly_reported_free_space_is_not_credited_as_safe_A_audit_capacity': True,
}
