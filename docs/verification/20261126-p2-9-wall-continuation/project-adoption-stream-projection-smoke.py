"""Small local fixtures only; never open the production adoption file."""
from pathlib import Path
import hashlib
import io
import json

source = Path(__file__).with_name('project-adoption-stream-projection.py').read_bytes()
scope = {'__name__': 'p29_adoption_stream_smoke'}
exec(compile(source, '<reviewed-stream-source-smoke>', 'exec'), scope)
Reader, Stream, Projector = (scope[n] for n in
    ('HashedUtf8Reader', 'BoundedJsonStream', 'AdoptionProjection'))
Bound = scope['ProjectionBound']
cases = []


def parse(payload, chunk, field_limit=4096, scalar_limit=1048576):
    reader = Reader(io.BytesIO(payload), len(payload), chunk_size=chunk)
    stream = Stream(reader, scalar_char_limit=scalar_limit)
    projector = Projector(stream, ['Wanted', 'FullMember', 'Missing'],
                          field_limit=field_limit, total_limit=65536)
    projector.document()
    assert reader.eof and reader.bytes_read == len(payload)
    assert reader.digest.hexdigest() == hashlib.sha256(payload).hexdigest()
    assert stream.consumed_bytes == len(payload)
    return projector.result(True)


fixture = {
    'adopted': {
        'Unselected': {'actual_import_map': {'U': ['ignored { } [ ]', False]}, 'skip': [1, 2]},
        'Wanted': {
            'actual_import_map': {
                'A': [['/workspace/A.olean', 'h1'], ['quote"slash\\.ir', 'h2']],
                'B': [None, {'braces': '} { [ ]', 'nested': [[], {}]}],
            },
            'source': 'ℝ/原稿.lean',
            'receipt': {'path': '/workspace/receipt.json', 'sha256': 'a' * 64},
            'scalars': [-1.25e-8, 6.02e23, True, False, None, 'escaped\n"\\tail'],
        },
        'FullMember': {'source': '/workspace/FullMember.lean', 'qualified': False},
    },
    'root_receipt': {'path': '/workspace/root-receipt.json', 'nested': [1, {'x': []}]},
    'root_decimal': -0.0025,
}
payload = (json.dumps(fixture, ensure_ascii=False, indent=2) + '\n').encode()
for chunk in (1, 2, 3, 5, 7, 13, 31, 64, 65536):
    result = parse(payload, chunk)
    assert result['adopted_direct_keys'] == list(fixture['adopted'])
    assert result['candidate_keys_seen'] == ['FullMember', 'Wanted']
    assert result['candidate_keys_absent'] == ['Missing']
    assert 'Unselected' not in result['selected_entries']
    for module in ('Wanted', 'FullMember'):
        row = result['selected_entries'][module]
        ident = row['original_entry_identity']
        raw = payload[ident['original_byte_offset']:
                      ident['original_byte_offset'] + ident['original_value_bytes']]
        assert hashlib.sha256(raw).hexdigest() == ident['original_value_sha256']
        assert json.loads(raw) == fixture['adopted'][module]
        for field in row['metadata_fields']:
            name = field['field']
            assert json.loads(field['original_value_json']) == fixture['adopted'][module][name]
            raw = payload[field['original_byte_offset']:
                          field['original_byte_offset'] + field['original_value_bytes']]
            assert raw.decode() == field['original_value_json']
            assert hashlib.sha256(raw).hexdigest() == field['original_value_sha256']
    omitted = result['selected_entries']['Wanted']['omitted_actual_import_maps'][0]
    assert omitted['direct_entries'] == 2 and omitted['body_omitted']
    assert 'original_value_json' not in omitted
    raw = payload[omitted['original_byte_offset']:
                  omitted['original_byte_offset'] + omitted['original_value_bytes']]
    assert json.loads(raw) == fixture['adopted']['Wanted']['actual_import_map']
    assert hashlib.sha256(raw).hexdigest() == omitted['original_value_sha256']
    for field in result['non_adopted_root_metadata']:
        assert json.loads(field['original_value_json']) == fixture[field['field']]
    assert {p['explicit_value'] for p in result['explicit_JSON_receipt_like_pointers']} == {
        '/workspace/receipt.json', '/workspace/root-receipt.json'}
    cases.append({'case': 'nested_selection_escapes_UTF8_numbers_exact_raw_spans', 'chunk_bytes': chunk,
                  'payload_bytes': len(payload), 'passed': True})

large_fixture = {'adopted': {'Wanted': {
    'actual_import_map': {str(i): [i, 'not retained'] for i in range(20)},
    'large_receipt': {'rows': ['x' * 30 for _ in range(40)],
                      'receipt_path': '/workspace/late.json'},
    'qualified_after_large_field': False}}, 'tail': 1.25e-7}
large = json.dumps(large_fixture, separators=(',', ':')).encode()
for chunk in (1, 7, 64):
    result = parse(large, chunk, field_limit=48)
    fields = {x['field']: x for x in result['selected_entries']['Wanted']['metadata_fields']}
    assert not fields['large_receipt']['original_value_json_captured_complete']
    assert fields['large_receipt']['omitted_reason'] == 'bounded_metadata_capture'
    assert json.loads(fields['qualified_after_large_field']['original_value_json']) is False
    assert result['selected_entries']['Wanted']['omitted_actual_import_maps'][0]['direct_entries'] == 20
    assert any(p['explicit_value'] == '/workspace/late.json'
               for p in result['explicit_JSON_receipt_like_pointers'])
    assert json.loads(result['non_adopted_root_metadata'][0]['original_value_json']) == 1.25e-7
    cases.append({'case': 'large_container_omitted_but_following_fields_and_pointer_retained',
                  'chunk_bytes': chunk, 'payload_bytes': len(large), 'passed': True})

scalar_fixture = json.dumps({'adopted': {'Wanted': {}}, 'receipt_body': 'x' * 4096}).encode()
reader = Reader(io.BytesIO(scalar_fixture), len(scalar_fixture), chunk_size=7)
stream = Stream(reader, scalar_char_limit=128)
projector = Projector(stream, ['Wanted', 'Missing'], field_limit=48)
try:
    projector.document()
    raise AssertionError('expected scalar buffer bound')
except Bound:
    reader.drain_hash_only()
    assert reader.eof and reader.bytes_read == len(scalar_fixture)
    assert reader.digest.hexdigest() == hashlib.sha256(scalar_fixture).hexdigest()
    assert projector.result(False)['candidate_keys_absent'] is None
    cases.append({'case': 'oversize_scalar_bounded_then_same_pass_hash_drain', 'passed': True})

for bad in (b'{"adopted":{},"x":1e-}', b'{"adopted":{},"x":[1,]}',
            b'{"adopted":{"Wanted":{}},"adopted":{}}'):
    try:
        parse(bad, 1)
        raise RuntimeError('malformed/duplicate-root JSON unexpectedly accepted')
    except (AssertionError, json.JSONDecodeError):
        cases.append({'case': 'invalid_or_duplicate_JSON_rejected',
                      'payload_sha256': hashlib.sha256(bad).hexdigest(), 'passed': True})

report = {'schema': 'p29_adoption_stream_local_smoke_v1',
          'production_source_sha256': hashlib.sha256(source).hexdigest(),
          'production_file_opened': False, 'remote_tasks_submitted': 0,
          'new_Lean_invocations': 0, 'case_count': len(cases), 'all_passed': True,
          'cases': cases}
out = Path(__file__).with_name('PROJECT_ADOPTION_STREAM_LOCAL_SMOKE.json')
out.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'case_count': len(cases), 'all_passed': True,
                  'report': str(out), 'report_sha256': hashlib.sha256(out.read_bytes()).hexdigest()}))
