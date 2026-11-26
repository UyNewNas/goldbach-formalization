from pathlib import Path
import ast
import base64
import hashlib
import json

D = Path(__file__).resolve().parent
TASK = 'd3f6737160344cc699b8cd267884e34c'

def encode(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode('ascii')

def ident(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest(),
        'git_blob': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()}

def body(raw):
    return raw.get('structuredContent') or json.loads(next(x['text'] for x in raw['content'] if x['type'] == 'text'))

def pin(record):
    return {k: record[k] for k in ('bytes', 'sha256', 'git_blob')}

def write_once(name, raw):
    with (D / name).open('xb') as stream:
        stream.write(raw)
    return {'path': str(D / name), **ident(raw)}

source = (D / 'p2-nonempty-13-byte-receiver-v1.py').read_bytes()
contract_bytes = (D / 'NONEMPTY13_PIN_CONTRACT.json').read_bytes()
contract = json.loads(contract_bytes)
assert ident(source)['git_blob'] == '9882f429827f22f519d9145111af227c7b0af122'
assert ident(contract_bytes)['git_blob'] == '34d320afcecf49bfc63696033ba4463ad648b322'
source_tree = ast.parse(source)
assert ast.literal_eval(next(n for n in source_tree.body if isinstance(n, ast.Assign)
    and any(isinstance(t, ast.Name) and t.id == 'PIN' for t in n.targets)).value) == contract
original_encode = next(n for n in source_tree.body if isinstance(n, ast.FunctionDef) and n.name == 'encode')
local_encode = next(n for n in ast.parse(Path(__file__).read_text()).body if isinstance(n, ast.FunctionDef) and n.name == 'encode')
assert ast.dump(original_encode, include_attributes=False) == ast.dump(local_encode, include_attributes=False)
terminal = body(json.loads((D / 'NONEMPTY13_FINAL_TASK.json').read_bytes()))
assert terminal['job_id'] == terminal['task_id'] == TASK
assert terminal['status'] == 'succeeded' and terminal['exit_code'] == 0
assert (terminal['cwd'], terminal['memory_mb'], terminal['cpu_threads'], terminal['timeout_seconds']) == ('/workspace', 512, 1, 300)
assert not terminal['log_truncated'] and terminal['log_discarded_bytes'] == 0
transport = json.loads((D / 'NONEMPTY13_OUTPUT_TRANSPORT.json').read_bytes())
assert transport['task_id'] == TASK
chunks, page_receipts, offset = [], [], 0
for entry in sorted(transport['pages'], key=lambda x: x['request']['offset']):
    request, result = entry['request'], body(entry['raw'])
    assert request['task_id'] == TASK and request['offset'] == offset
    data = base64.b64decode(result['output_base64'], validate=True)
    assert len(data) <= request['limit'] and result['output'] == data.decode()
    assert not result['log_truncated'] and result['discarded_bytes'] == 0
    start = offset
    offset += len(data)
    assert result['next_offset'] == offset
    assert result['eof'] == (offset == terminal['log_bytes'])
    chunks.append(data)
    page_receipts.append({'offset': start, 'next_offset': offset, 'bytes': len(data),
        'sha256': hashlib.sha256(data).hexdigest(), 'eof': result['eof'], 'request': request})
stdout = b''.join(chunks)
assert len(stdout) == terminal['log_bytes']
marker = b'P29_NONEMPTY_P2_BYTE_RECEPTION '
assert stdout.startswith(marker) and stdout.endswith(b'\n') and stdout.count(b'\n') == 1
receipt = json.loads(stdout[len(marker):])
assert receipt['status'] == 'PASS_EXACT_OLD_BYTES_ONLY_NOT_MATHEMATICAL_OR_ACTUAL_IMPORT_QUALIFICATION'
assert receipt['root'] == contract['base']
assert pin(receipt['receiver']) == ident(source) and pin(receipt['pin_contract']) == ident(contract_bytes)
assert pin(receipt['input_index']) == contract['input_index']
assert pin(receipt['prior18_receipt']) == pin(contract['old18_receiver_receipt'])
assert receipt['prior18_receipt']['path'] == contract['old18_receiver_receipt']['path']
unit_group = next(g for g in contract['archives'] if g['id'] == 'unit128_existing')
assert pin(receipt['original_unit128_manifest']) == pin(unit_group['original_manifest_record'])
assert receipt['original_unit128_manifest']['path'] == unit_group['original_manifest_record']['path']
assert receipt['original_unit128_manifest']['stat'] == unit_group['original_manifest_record']['stat']
rows = {r['module']: r for r in contract['objects']}
assert len(rows) == 13 and set(receipt['selected_objects']) == set(rows)
assert set(receipt['authorized_candidate_observations']) == set(rows)
compact, object_reuse, source_reuse, candidate_classes = [], 0, 0, {}
for module, row in sorted(rows.items()):
    selected = receipt['selected_objects'][module]
    obs = receipt['authorized_candidate_observations'][module]
    assert [r['path'] for r in obs['objects']] == row['P2_candidates']
    assert [r['path'] for r in obs['sources']] == row['source']['P2_candidates']
    for role, chosen, expected, candidates, destination in (
        ('objects', selected, row, obs['objects'], row['destination_relative']),
        ('sources', selected['source'], row['source'], obs['sources'], row['source_destination_relative'])):
        assert (chosen['bytes'], chosen['sha256']) == (expected['bytes'], expected['sha256'])
        for c in candidates:
            candidate_classes[c['classification']] = candidate_classes.get(c['classification'], 0) + 1
        if chosen['selection'] == 'REUSE_EXISTING_SAME_PIN':
            matched = [c for c in candidates if c['selected_for_reuse']]
            assert len(matched) == 1 and chosen['original_candidate'] == matched[0]
            old = matched[0]
            assert old['classification'] == 'SAME_PIN_STABLE_CANDIDATE'
            assert old['sha256'] == expected['sha256'] and old['observed_bytes'] == expected['bytes']
            assert chosen['selected_path'] == old['path'] and chosen['final_stat'] == old['target_stat']
            if role == 'objects': object_reuse += 1
            else: source_reuse += 1
        else:
            assert chosen['selection'] == 'NEW_EXCLUSIVE_COPY_OF_ORIGINAL_PIN'
            assert all(not c['selected_for_reuse'] for c in candidates)
            assert chosen['selected_path'] == contract['base'] + '/' + destination
            new = chosen['new_file']
            assert new['path'] == chosen['selected_path']
            assert (new['bytes'], new['sha256']) == (expected['bytes'], expected['sha256'])
            assert chosen['final_stat'] == new['stat']
            if expected.get('git_blob') is not None:
                assert new['git_blob'] == expected['git_blob']
        assert len(chosen['final_stat']) == 7 and all(isinstance(x, int) for x in chosen['final_stat'])
        assert chosen['final_stat'][4] == expected['bytes']
    assert selected['provenance'] == {'input_index_blob': contract['input_index']['git_blob'],
        'provider': row['provider'], 'object_member': row['object_member'],
        'source_member': row['source']['member'], 'source_git_blob': row['source']['git_blob'],
        'qualification_group': row['qualification_group'], 'old_owned_count_not_new_credit': row['old_owned_count']}
    compact.append({'module': module, 'object_path': selected['selected_path'],
        'object_bytes': selected['bytes'], 'object_sha256': selected['sha256'],
        'object_selection': selected['selection'], 'object_stat': selected['final_stat'],
        'source_path': selected['source']['selected_path'], 'source_bytes': selected['source']['bytes'],
        'source_sha256': selected['source']['sha256'], 'source_selection': selected['source']['selection'],
        'source_stat': selected['source']['final_stat'], 'provenance': selected['provenance']})
assert len(receipt['archives']) == len(contract['archives']) == 3
expected_downloads = {contract['input_index']['git_blob']: contract['input_index']}
used_archives, protected_names = [], {contract['old18_receiver_receipt']['path'], unit_group['original_manifest_record']['path']}
for observed, group in zip(receipt['archives'], contract['archives']):
    assert observed['group'] == group['id']
    group_rows = [r for r in rows.values() if r['provider'] == group['id']]
    needed = {r['object_member'] for r in group_rows if receipt['selected_objects'][r['module']]['selection'] != 'REUSE_EXISTING_SAME_PIN'}
    needed |= {r['source']['member'] for r in group_rows if receipt['selected_objects'][r['module']]['source']['selection'] != 'REUSE_EXISTING_SAME_PIN'}
    if not needed:
        assert observed == {'group': group['id'], 'status': 'NOT_OPENED_ALL_REQUIRED_MEMBERS_REUSED',
            'archive_downloads': 0, 'archive_extraction_passes': 0}
        continue
    used_archives.append(group['id'])
    assert observed['bytes'] == group['archive']['bytes'] and observed['sha256'] == group['archive']['sha256']
    assert observed['manifest']['sha256'] == group['manifest']['sha256']
    if group['manifest']['bytes'] is not None: assert observed['manifest']['bytes'] == group['manifest']['bytes']
    assert observed['member_count'] == group['member_count']
    assert observed['captured_members'] == sorted(needed | {group['manifest']['member']})
    assert observed['other_member_payloads_materialized_or_audited'] is False
    assert observed['original_archive_fully_hashed'] and observed['single_member_extraction_pass']
    assert observed['total_original_member_bytes'] <= group['max_expanded_bytes']
    if group['expanded_member_bytes'] is not None: assert observed['total_original_member_bytes'] == group['expanded_member_bytes']
    if group['id'] == 'unit128_existing':
        assert observed['archive_downloads'] == 0 and observed['path'] == group['existing_path']
        assert observed['stat'] == group['expected_original_stat'] and observed['original_receipt_stat_matched']
        protected_names.add(group['existing_path'])
    else:
        assert observed['archive_downloads'] == 1 and observed['each_part_fetched_once']
        assert observed['parts'] == [{k: p[k] for k in ('index','offset','bytes','sha256','git_blob')} for p in group['parts']]
        for p in group['parts']:
            assert p['git_blob'] not in expected_downloads
            expected_downloads[p['git_blob']] = {k:p[k] for k in ('bytes','sha256','git_blob')}
assert set(receipt['downloads']) == set(expected_downloads)
for blob, expected in expected_downloads.items():
    assert pin(receipt['downloads'][blob]) == expected and receipt['downloads'][blob]['fetch_count'] == 1
assert set(receipt['existing_protected_files_unchanged']) == protected_names
assert receipt['counts'] == {'objects': 13, 'source_files': 13, 'object_bytes': 4445656, 'source_bytes': 92222,
    'reused_existing_objects': object_reuse, 'reused_existing_sources': source_reuse,
    'object_candidates_checked': 12, 'source_candidates_checked': 12, 'Unit_archive_downloads': 0,
    'Git_raw_bytes_received': sum(p['bytes'] for p in expected_downloads.values())}
assert receipt['capacity']['free_bytes_before'] >= receipt['capacity']['minimum_free_bytes'] == 67108864
assert (receipt['capacity']['requested_memory_mb'], receipt['capacity']['requested_cpu_threads'], receipt['capacity']['requested_timeout_seconds']) == (512,1,300)
scope = receipt['scope']
for k in ('old58_modified','future_Omitted_output_read_or_written','P3_Power_variant_introduced',
          'different_candidate_overwritten','unlisted_paths_scanned','global_absence_claim',
          'actual_compiled_header_or_native_standard_graph_qualified'):
    assert scope[k] is False
for k in ('Lean_invocations','normal_kernel_owned_replays','new_proof_credit'): assert scope[k] == 0
stdout_record = write_once('NONEMPTY13_ORIGINAL_STDOUT.log', stdout)
receipt_record = write_once('NONEMPTY13_BYTE_RECEPTION_RECEIPT.json', encode(receipt))
binding = {'schema':'p29_nonempty13_exact_terminal_byte_reception_binding_v1',
    'status':'PASS_EXACT_OLD_BYTES_ONLY', 'task_id':TASK, 'terminal':terminal,
    'actual_submission_blob':'3b4533d141da8c0fdff7752855abd10f817302bb',
    'request_blob':'12c086753ed6662c5953ed4b3d7ff0f6de2f9bf4',
    'source':ident(source), 'contract':ident(contract_bytes), 'original_stdout':stdout_record,
    'receipt':receipt_record, 'receipt_encoding':'Reconstructed from lossless original stdout with the identical original encode AST; no separate remote receipt read.',
    'pages':page_receipts, 'selected_objects':compact, 'counts':receipt['counts'],
    'candidate_classifications':candidate_classes, 'archives_used':used_archives,
    'Git_blobs_fetched_once':len(expected_downloads), 'capacity':receipt['capacity'], 'scope':scope,
    'additional_remote_jobs_or_reads':0, 'new_proof_credit':0}
binding_record = write_once('NONEMPTY13_RECEPTION_BINDING.json', encode(binding))
print(json.dumps({'stdout':stdout_record, 'receipt':receipt_record, 'binding':binding_record,
    'counts':receipt['counts'], 'archives_used':used_archives, 'candidate_classifications':candidate_classes},sort_keys=True))
