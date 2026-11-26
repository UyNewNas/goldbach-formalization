from pathlib import Path, PurePosixPath
import ast
import base64
import collections
import hashlib
import json

BASE = Path(__file__).resolve().parent
TASK = '213c8b9aa5a746e8bc4645ff10987dce'
SOURCE_PIN = (57256, '97fe63b8cd4966ec495b55d936796403d7343625b96d34970723e8eb0f987580', 'f20e1aae21a19d26aa9aa39f3912eb2d0640410b')
CONTRACT_PIN = (45087, '2a0f10ae7d23858499f6c9d857e5d18a2e9ade3f1d8c878aee9ee385c0e183b1', 'ec9396407e3ab379687ead798c78fa948f97868c')

def encode(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode('ascii')

def ident(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
            'git_blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()}

def body(raw):
    return raw.get('structuredContent') or json.loads(next(x['text'] for x in raw['content'] if x['type'] == 'text'))

def record_identity(record):
    return {key: record[key] for key in ('bytes', 'sha256', 'git_blob')}

def write(name, data):
    with (BASE / name).open('xb') as stream:
        stream.write(data)
    return {'path': str(BASE / name), **ident(data)}

source = (BASE / 'p2-omitted-18-byte-receiver-v1.py').read_bytes()
contract_raw = (BASE / 'P2_OMITTED18_PIN_CONTRACT.json').read_bytes()
assert tuple(ident(source).values()) == SOURCE_PIN
assert tuple(ident(contract_raw).values()) == CONTRACT_PIN
contract = json.loads(contract_raw)
source_ast = ast.parse(source)
pin_assignment = next(n for n in source_ast.body if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'PIN' for t in n.targets))
assert ast.literal_eval(pin_assignment.value) == contract
original_encode = next(n for n in source_ast.body if isinstance(n, ast.FunctionDef) and n.name == 'encode')
expected_encode = next(n for n in ast.parse(Path(__file__).read_text()).body if isinstance(n, ast.FunctionDef) and n.name == 'encode')
assert ast.dump(original_encode, include_attributes=False) == ast.dump(expected_encode, include_attributes=False)

terminal_raw = json.loads((BASE / 'P2_OMITTED18_FINAL_TASK.json').read_text())
terminal = body(terminal_raw)
assert terminal['job_id'] == terminal['task_id'] == TASK
assert terminal['status'] == 'succeeded' and terminal['exit_code'] == 0
assert terminal['cwd'] == '/workspace'
assert (terminal['memory_mb'], terminal['cpu_threads'], terminal['timeout_seconds']) == (512, 1, 300)
assert terminal['log_bytes'] == 65741 and terminal['log_discarded_bytes'] == 0 and not terminal['log_truncated']
transport = json.loads((BASE / 'P2_OMITTED18_OUTPUT_TRANSPORT.json').read_text())
assert transport['task_id'] == TASK and len(transport['pages']) == 2
chunks, page_receipts, offset = [], [], 0
for page in sorted(transport['pages'], key=lambda p: p['request']['offset']):
    request, result = page['request'], body(page['raw'])
    assert request['task_id'] == TASK and request['offset'] == offset
    raw = base64.b64decode(result['output_base64'], validate=True)
    assert len(raw) <= request['limit']
    assert not result['log_truncated'] and result['discarded_bytes'] == 0
    assert result['output'] == raw.decode('utf-8')
    previous = offset
    offset += len(raw)
    assert result['next_offset'] == offset
    assert result['eof'] == (offset == terminal['log_bytes'])
    chunks.append(raw)
    page_receipts.append({'request': request, 'start': previous, 'next_offset': offset,
                          'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest(),
                          'eof': result['eof'], 'stream': result['stream']})
stdout = b''.join(chunks)
assert stdout == (BASE / 'P2_OMITTED18_ORIGINAL_STDOUT.log').read_bytes()
assert len(stdout) == terminal['log_bytes']
prefix = b'P29_OMITTED_P2_BYTE_RECEPTION '
assert stdout.startswith(prefix) and stdout.endswith(b'\n') and stdout.count(b'\n') == 1
receipt = json.loads(stdout[len(prefix):])
assert receipt['status'] == 'PASS_EXACT_BYTES_ONLY_NOT_MATHEMATICAL_OR_ACTUAL_IMPORT_QUALIFICATION'
assert receipt['root'] == contract['base']
assert record_identity(receipt['receiver']) == ident(source)
assert record_identity(receipt['pin_contract']) == ident(contract_raw)
assert receipt['receiver']['path'] == contract['base'] + '/receiver.py'
assert receipt['pin_contract']['path'] == contract['base'] + '/PIN_CONTRACT.json'
expected_rows = {r['module']: r for r in contract['objects']}
assert len(expected_rows) == 18 and set(receipt['selected_objects']) == set(expected_rows)
assert set(receipt['authorized_candidate_observations']) == set(expected_rows)
compact_rows, classification_counts = [], collections.Counter()
for module, row in sorted(expected_rows.items()):
    selected = receipt['selected_objects'][module]
    assert (selected['bytes'], selected['sha256']) == (row['bytes'], row['sha256'])
    observations = receipt['authorized_candidate_observations'][module]
    assert [o['path'] for o in observations] == row['P2_candidates']
    classification_counts.update(o['classification'] for o in observations)
    assert all(not o['selected_for_reuse'] for o in observations)
    assert selected['selected_path'] == contract['base'] + '/' + row['destination_relative']
    expected_selection = ('NEW_EXCLUSIVE_COPY_OF_EXISTING_Git_BLOB' if row['provider'] == 'standalone_git'
                          else 'NEW_EXCLUSIVE_COPY_OF_SPECIFIED_PIN')
    assert selected['selection'] == expected_selection
    new = selected['new_file']
    assert new['path'] == selected['selected_path']
    assert (new['bytes'], new['sha256']) == (row['bytes'], row['sha256'])
    assert selected['final_stat'] == new['stat'] and new['stat'][4] == row['bytes']
    assert all(isinstance(v, int) for v in new['stat']) and len(new['stat']) == 7
    assert selected['provenance'] == row['provenance']
    assert selected['member_provenance'] == {'provider': row['provider'], 'member': row.get('object_member'),
        'existing_git_blob': row.get('git_blob'), 'source_member_or_Git': row['source']}
    if row['provider'] == 'standalone_git':
        assert new['git_blob'] == row['git_blob']
    src = selected['source_received']
    if row['source'] is None:
        assert src is None
    else:
        assert (src['bytes'], src['sha256']) == (row['source']['bytes'], row['source']['sha256'])
        assert src['path'] == contract['base'] + '/sources/' + module.replace('.', '/') + '.lean'
        assert src['stat'][4] == src['bytes']
        if 'git_blob' in row['source']:
            assert src['git_blob'] == row['source']['git_blob']
    compact_rows.append({'module': module, 'kind': row['kind'], 'path': selected['selected_path'],
        'bytes': selected['bytes'], 'sha256': selected['sha256'], 'git_blob': new['git_blob'],
        'selection': selected['selection'], 'stat': selected['final_stat'], 'source': src,
        'provider': row['provider'], 'object_member': row.get('object_member')})

assert len(receipt['archives']) == len(contract['archives']) == 3
for observed, group in zip(receipt['archives'], contract['archives']):
    assert observed['group'] == group['id']
    assert observed['bytes'] == group['archive']['bytes'] and observed['sha256'] == group['archive']['sha256']
    assert observed['parts'] == [{k: p[k] for k in ('index', 'offset', 'bytes', 'sha256', 'git_blob')} for p in group['parts']]
    assert observed['archive_fetched_once'] is True
    assert observed['other_member_payloads_materialized_or_audited'] is False
    assert observed['member_count'] == group['member_count'] and observed['archive_stat'][4] == group['archive']['bytes']
    assert (observed['manifest']['bytes'], observed['manifest']['sha256']) == (group['manifest']['bytes'], group['manifest']['sha256'])
    rows = [r for r in expected_rows.values() if r['provider'] == group['id']]
    captured = {r['object_member'] for r in rows}
    captured |= {r['source']['member'] for r in rows if r['source'] is not None}
    captured.add(group['manifest']['member'])
    assert observed['captured_members'] == sorted(captured)
expected_downloads = {v['git_blob']: {k: v[k] for k in ('bytes', 'sha256', 'git_blob')} for v in contract['documents'].values()}
for group in contract['archives']:
    for part in group['parts']:
        assert part['git_blob'] not in expected_downloads
        expected_downloads[part['git_blob']] = {k: part[k] for k in ('bytes', 'sha256', 'git_blob')}
for row in expected_rows.values():
    if row['provider'] == 'standalone_git':
        for item in (row, row['source']):
            assert item['git_blob'] not in expected_downloads
            expected_downloads[item['git_blob']] = {k: item[k] for k in ('bytes', 'sha256', 'git_blob')}
assert set(receipt['downloads']) == set(expected_downloads)
for blob, expected in expected_downloads.items():
    assert record_identity(receipt['downloads'][blob]) == expected
    assert receipt['downloads'][blob]['fetch_count'] == 1
for name, pin in contract['documents'].items():
    assert record_identity(receipt['authorities'][name]) == {k: pin[k] for k in ('bytes', 'sha256', 'git_blob')}
assert receipt['counts'] == {'archive_packages_received_once': 3, 'authorized_candidates_checked': 36,
    'foreign_project_bytes': 889120, 'foreign_project_objects': 4, 'native12_formal_sources_received': 0,
    'native_bytes': 8466440, 'native_objects': 14, 'object_bytes': 9355560, 'objects': 18,
    'received_source_files': 6, 'reused_existing_objects': 0}
assert receipt['capacity']['actual_Git_raw_bytes_received'] == sum(r['bytes'] for r in expected_downloads.values())
assert receipt['capacity']['free_bytes_before'] >= receipt['capacity']['minimum_free_bytes'] == 67108864
assert receipt['capacity']['requested_task_memory_mb'] == terminal['memory_mb']
assert receipt['capacity']['requested_cpu_threads'] == terminal['cpu_threads']
scope = receipt['scope']
for name in ('old_P2_project54_modified', 'different_candidate_overwritten', 'unlisted_paths_scanned',
             'global_absence_claim', 'actual_native_standard_import_union_qualified'):
    assert scope[name] is False
for name in ('Lean_invocations', 'normal_kernel_owned_replays', 'new_formal_credit'):
    assert scope[name] == 0
receipt_record = write('P2_OMITTED18_BYTE_RECEPTION_RECEIPT.json', encode(receipt))
summary = {'schema': 'p29_omitted18_exact_terminal_transport_binding_v1', 'task_id': TASK,
    'status': 'PASS_BYTE_RECEPTION_ONLY', 'terminal_task': terminal,
    'original_stdout': {'path': str(BASE / 'P2_OMITTED18_ORIGINAL_STDOUT.log'), **ident(stdout)},
    'complete_receipt': receipt_record,
    'receipt_encoding': 'Reconstructed from lossless original stdout using the identical AST-checked original encode(value); not independently reread from remote disk.',
    'receiver_source': ident(source), 'pin_contract': ident(contract_raw),
    'actual_submission_blob': '108d57c25f4e32058f4a4770a8139142ebcb1342',
    'approved_request_blob': '15fd90fdf7de8627c8372df5cd5b40c9c18d7e83',
    'approved_wrapper_blob': '3e76c4c9006f85807d42a1acbe527c5168d24de0',
    'pages': page_receipts, 'counts': receipt['counts'], 'capacity': receipt['capacity'],
    'candidate_classifications': dict(classification_counts),
    'exact_pin_comparisons_passed': len(compact_rows), 'selected_objects': compact_rows,
    'archive_packages_received_once': len(receipt['archives']), 'Git_blobs_fetched_once': len(expected_downloads),
    'scope': scope, 'no_additional_remote_task_or_read': True}
summary_record = write('P2_OMITTED18_RECEPTION_BINDING.json', encode(summary))
print(json.dumps({'receipt': receipt_record, 'binding': summary_record,
                  'candidate_classifications': dict(classification_counts), 'counts': receipt['counts'],
                  'capacity': receipt['capacity']}, sort_keys=True))
