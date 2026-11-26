import ast
import base64
import collections
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parent
TASK = '3df47fa860e549dab204d053b11551d9'


def identity(name):
    raw = (BASE / name).read_bytes()
    return {'local_file': name, 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest(),
            'git_blob': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()}


def body(raw):
    if raw.get('structuredContent') is not None:
        return raw['structuredContent']
    return json.loads(next(x['text'] for x in raw['content'] if x['type'] == 'text'))


source_name = 'p2-native14-candidates-readonly-v1.py'
index_name = 'NATIVE14_EXACT_REUSE_INPUT_INDEX.json'
output_name = 'P2_NATIVE14_CANDIDATE_READONLY_OUTPUT.log'
source_identity = identity(source_name)
index_identity = identity(index_name)
assert source_identity['git_blob'] == 'b38ee99dce2b9f41a55398aeb5dc6e4c2000833d'
assert source_identity['sha256'] == '568c8b2fe0619312898a430d11e2f79afd7d8c4d74d5c75df6cb0a901a33dcfa'
assert index_identity['git_blob'] == '65f2cb2a0aafffdca7bfc42d3c46478b2be5936f'
assert index_identity['sha256'] == 'ce7f66e7f392a9574ad8ed4cb03a6dd9451c17699f407ce7eddfc03eb83b6daf'
index = json.loads((BASE / index_name).read_bytes())
tree = ast.parse((BASE / source_name).read_text())
constants = {n.targets[0].id: ast.literal_eval(n.value) for n in tree.body
             if isinstance(n, ast.Assign) and len(n.targets) == 1
             and isinstance(n.targets[0], ast.Name) and n.targets[0].id in ('PAYLOAD', 'ROOTS')}
payload = constants['PAYLOAD']
expected_rows = [{'module': r['module'], 'P1_pin': r['P1_exact_required_object'],
                  'P2_candidates': [x['path'] for x in r['P2_known_root_candidates']]}
                 for r in index['rows']]
assert payload['rows'] == expected_rows
assert payload['index_git_blob'] == index_identity['git_blob']
assert payload['index_bytes'] == index_identity['bytes']
assert payload['index_sha256'] == index_identity['sha256']

request = json.loads((BASE / 'P2_NATIVE14_CANDIDATE_READONLY_REQUEST.json').read_bytes())
assert request == {'command': (BASE / 'p2-native14-candidates-readonly-v1-command.sh').read_text(),
                   'cpu_threads': 1, 'cwd': '/workspace', 'memory_mb': 256, 'timeout_seconds': 60}
status = body(json.loads((BASE / 'P2_NATIVE14_CANDIDATE_READONLY_TERMINAL_STATUS.json').read_bytes()))
assert status['job_id'] == status['task_id'] == TASK
assert status['status'] == 'succeeded' and status['exit_code'] == 0
assert status['cwd'] == '/workspace' and status['memory_mb'] == 256
assert status['cpu_threads'] == 1 and status['timeout_seconds'] == 60
assert status['log_bytes'] == 44751 and not status['log_truncated'] and status['log_discarded_bytes'] == 0
history = json.loads((BASE / 'P2_NATIVE14_CANDIDATE_READONLY_COMPLETE_STATUS_HISTORY.json').read_bytes())
assert history['task_id'] == TASK and history['observation_count'] == len(history['observations'])
assert history['observations'][-1]['body'] == status
for observation in history['observations']:
    assert body(observation['raw_tool_result']) == observation['body']
    assert observation['body']['job_id'] == TASK

raw = (BASE / output_name).read_bytes()
transport = json.loads((BASE / 'P2_NATIVE14_CANDIDATE_READONLY_OUTPUT_TRANSPORT.json').read_bytes())
assert transport['request'] == {'task_id': TASK, 'offset': 0, 'limit': 65536}
response = transport['response']
assert raw == base64.b64decode(response['output_base64'], validate=True) == response['output'].encode()
assert len(raw) == status['log_bytes'] == response['next_offset']
assert response['eof'] is True and response['log_truncated'] is False and response['discarded_bytes'] == 0
assert response['stream'] == 'stdout+stderr'
result = json.loads(raw)
assert result['controller_sha256'] == source_identity['sha256']
assert result['index_git_blob'] == index_identity['git_blob']
assert result['index_bytes'] == index_identity['bytes'] and result['index_sha256'] == index_identity['sha256']
assert result['schema'] == 'p29_P2_exact_28_native_candidate_readonly_observation_v1'
assert result['status'] == 'COMPLETE_READONLY_CANDIDATE_OBSERVATIONS_NOT_COMPILE_OR_SUPPLIER_QUALIFICATION'
expected_candidates = [(r['module'], path, k, r['P1_pin'])
                       for r in expected_rows for k, path in enumerate(r['P2_candidates'])]
assert len(result['rows']) == len(expected_candidates) == 28
assert len({r['path'] for r in result['rows']}) == 28
for row, (module, path, root_index, pin) in zip(result['rows'], expected_candidates):
    assert (row['module'], row['path'], row['root_index'], row['expected_P1_pin']) == (module, path, root_index, pin)
    assert row['before'] == row['final'] and row['observation_unchanged_through_final_pass'] is True
    assert row['before']['entry_exists'] is False and row['before']['target_exists'] is None
    assert row['before']['lstat_error']['errno'] == 2
    assert row['before']['lstat_error']['type'] == 'FileNotFoundError'
    assert row['classification'] == 'NO_ENTRY_AT_THIS_EXACT_CANDIDATE'
    assert row['sha256'] is None and row['observed_bytes'] is None and row['hash_reused_from'] is None
    assert row['hash_stable_during_read'] is False and row['stable_exact_P1_match'] is False
    assert row['size_matches_P1'] is False and row['sha_matches_P1'] is False
assert result['counts'] == {'candidate_paths': 28, 'classifications': {'NO_ENTRY_AT_THIS_EXACT_CANDIDATE': 28},
                            'modules': 14, 'modules_with_at_least_one_stable_exact_P1_candidate': 0,
                            'physical_hash_reuses': 0, 'physical_objects_hashed': 0,
                            'stable_physical_hash_cache_entries': 0, 'total_object_bytes_read': 0}
per_module = {}
for row in result['rows']:
    item = per_module.setdefault(row['module'], {'matching_candidate_paths': [], 'checked_candidates': []})
    item['checked_candidates'].append({'path': row['path'], 'classification': row['classification']})
assert result['per_module'] == per_module
assert result['boundary'] == {'Lean_invocations': 0, 'filesystem_writes_requested': 0,
    'missing_candidate_is_global_P2_absence': False, 'native515_snapshot_modified': False,
    'native_or_standard_input_union_qualified': False, 'new_formal_credit': 0,
    'old_kernel_owned_replays': 0, 'scope_only_these_28_exact_paths': True,
    'source_files_read': 0, 'unlisted_P2_locations_not_searched': True}

artifacts = [source_name, 'p2-native14-candidates-readonly-v1-command.sh', index_name,
             'P2_NATIVE14_CANDIDATE_READONLY_REQUEST.json', 'P2_NATIVE14_CANDIDATE_READONLY_SUBMISSION.json',
             'P2_NATIVE14_CANDIDATE_READONLY_TERMINAL_STATUS.json', output_name,
             'P2_NATIVE14_CANDIDATE_READONLY_OUTPUT_TRANSPORT.json',
             'P2_NATIVE14_CANDIDATE_READONLY_COMPLETE_STATUS_HISTORY.json', Path(__file__).name]
receipt = {
    'schema': 'p29_native28_complete_readonly_reception_v1',
    'status': 'PASS_COMPLETE_ORIGINAL_TRANSPORT_EXACT_SCOPE_ALL28_NO_ENTRY',
    'task': status,
    'submission_count': 1,
    'output_reads': [{'offset': 0, 'limit': 65536, 'received_bytes': len(raw), 'next_offset': response['next_offset'],
                      'eof': response['eof'], 'log_truncated': response['log_truncated'], 'discarded_bytes': response['discarded_bytes']}],
    'original_output_base64_and_decoded_text_equal': True,
    'observed_status_history_counts': dict(collections.Counter(x['body']['status'] for x in history['observations'])),
    'checks': {'fixed_controller_and_index_exact': True, 'controller_payload_equals_original14_index': True,
               'real_request_command_equals_fixed_wrapper': True, 'real_task_budgets_match_request': True,
               'exact_28_candidates_no_extra_path': True, 'all_P1_pins_exact': True,
               'each_before_and_final_same_ENOENT': True, 'full_stdout_single_page_no_gaps_or_truncation': True,
               'all_reported_counts_recomputed': True, 'Python_integer_parsing_preserves_original_precision': True},
    'candidate_roots': constants['ROOTS'],
    'counts': result['counts'],
    'per_module': per_module,
    'artifacts': {name: identity(name) for name in artifacts},
    'scope': result['boundary'],
    'interpretation': ['All 28 authorized candidate paths returned ENOENT before and at the final observation.',
        'No object bytes were read or hashed, so no matching-object or different-object result is claimed.',
        'This result is not a global statement that these modules are absent from P2.',
        'The two Nonunit original object bytes remain reusable from the sealed Nonunit44 archive; no fresh P1 export occurred.',
        'No Nonunit44 binary archive parts were downloaded during this task.',
        'The twelve Buchstab object archive pointers remain unlocated in the previously bounded checked material.',
        'Any further object transfer or actual facet union qualification is a separate step; no Lean or old audit ran here.']}
name = 'P2_NATIVE14_CANDIDATE_READONLY_RECEPTION.json'
(BASE / name).write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + '\n')
print(json.dumps({'receipt': identity(name), 'counts': receipt['counts'], 'status_history': receipt['observed_status_history_counts'],
                  'artifacts': receipt['artifacts']}, indent=2))
