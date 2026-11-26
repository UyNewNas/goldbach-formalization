import ast
import hashlib
import json
import stat
import tarfile
from pathlib import Path, PurePosixPath

BASE = Path(__file__).resolve().parent
RECEPTION = BASE / 'reception'


def identity(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
            'git_blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()}


descriptor_raw = (RECEPTION / 'ARCHIVE_DESCRIPTOR.json').read_bytes()
assert identity(descriptor_raw) == {'bytes': 42013,
    'sha256': 'ec3b7a8aac7100ccb63e6399a9f10c53eb6670f601f15363799aa084bf4eb5f7',
    'git_blob': 'f1a48a916acf07f850b540344034d99d420c0538'}
descriptor = json.loads(descriptor_raw)
source = (BASE / 'buchstab12-existing-objects-export-v1.py').read_bytes()
assert identity(source)['git_blob'] == 'e658c2643c889a881a5a1c1e661c7679b13f71cf'
tree = ast.parse(source)
pin_index = ast.literal_eval(next(n.value for n in tree.body if isinstance(n, ast.Assign)
    and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name) and n.targets[0].id == 'PIN_INDEX'))
part_paths = [RECEPTION / 'buchstab12-existing-objects.part00',
              RECEPTION / 'part01/buchstab12-existing-objects.part01',
              RECEPTION / 'part02/buchstab12.part02',
              RECEPTION / 'part03/buchstab12-existing-objects.part03',
              RECEPTION / 'part04/buchstab12-existing-objects.part04']
parts = []
assembled = bytearray()
for i, path in enumerate(part_paths):
    data = path.read_bytes()
    expected = descriptor['parts'][i]
    assert expected['index'] == i and expected['offset'] == len(assembled)
    assert identity(data) == {k: expected[k] for k in ('bytes', 'sha256', 'git_blob')}
    parts.append({'index': i, 'path': str(path), **identity(data)})
    assembled.extend(data)
assert identity(assembled) == {k: descriptor['archive'][k] for k in ('bytes', 'sha256', 'git_blob')}
archive_path = RECEPTION / 'buchstab12-existing-objects.tar.xz'
with archive_path.open('xb') as stream:
    stream.write(assembled)
del assembled
output = RECEPTION / 'complete'
output.mkdir(parents=False, exist_ok=False)
expected_names = {row['archive_member'] for row in pin_index['objects']}
expected_names |= {'PIN_INDEX.json', 'EXPORTER.py', 'BINDING_RECEIPT.json', 'FILE_MANIFEST.json'}
assert len(expected_names) == 16 and expected_names == set(descriptor['member_manifest'])
actual = {}
with tarfile.open(archive_path, 'r:xz') as archive:
    for member in archive:
        path = PurePosixPath(member.name)
        assert member.isfile() and not path.is_absolute() and '..' not in path.parts
        assert member.name in expected_names and member.name not in actual
        assert member.mode == 0o444 and member.uid == 0 and member.gid == 0 and member.mtime == 0
        stream = archive.extractfile(member)
        assert stream is not None
        data = stream.read()
        assert len(data) == member.size
        assert identity(data) == descriptor['member_manifest'][member.name]
        destination = output / member.name
        destination.parent.mkdir(parents=True, exist_ok=True)
        with destination.open('xb') as sink:
            sink.write(data)
        actual[member.name] = identity(data)
assert set(actual) == expected_names
manifest = json.loads((output / 'FILE_MANIFEST.json').read_bytes())
assert manifest == {name: info for name, info in actual.items() if name != 'FILE_MANIFEST.json'}
assert (output / 'EXPORTER.py').read_bytes() == source
assert json.loads((output / 'PIN_INDEX.json').read_bytes()) == pin_index
receipt = json.loads((output / 'BINDING_RECEIPT.json').read_bytes())
assert receipt == descriptor['binding_receipt']
assert receipt['original_index'] == pin_index['original_index'] == descriptor['original_index']
assert receipt['exporter'] == descriptor['exporter'] == identity(source)
assert receipt['all_original_pins_and_stamps_stable'] is True
assert descriptor['all_original_stamps_equal_before_after_ingestion_and_after_seal'] is True
assert len(receipt['original_objects']) == 12
objects = []
for row, bound in zip(pin_index['objects'], receipt['original_objects']):
    assert bound['module'] == row['module'] and bound['original_path'] == row['path']
    assert bound['archive_member'] == row['archive_member']
    assert bound['bytes'] == row['bytes'] and bound['sha256'] == row['sha256']
    assert actual[row['archive_member']] == {k: bound[k] for k in ('bytes', 'sha256', 'git_blob')}
    before = bound['before']
    assert before == bound['after_own_read'] == receipt['after_all_reads'][row['module']]
    assert before == descriptor['post_seal_original_snapshots'][row['module']]
    assert stat.S_ISREG(before['target_stat'][2]) and before['target_stat'][4] == row['bytes']
    objects.append({'module': row['module'], 'original_path': row['path'],
                    'member': row['archive_member'], **actual[row['archive_member']]})
assert sum(x['bytes'] for x in objects) == 7767032
assert receipt['boundary'] == descriptor['boundary']
boundary = receipt['boundary']
assert boundary['original_object_reads'] == 12
assert boundary['formal_source_files_read'] == boundary['Lean_invocations'] == boundary['old_normal_kernel_owned_replays'] == boundary['new_proof_credit'] == 0
assert boundary['NonunitRoughUniform_and_Core_read_or_reexported'] is False
assert boundary['P2_global_missing_claim'] is False and boundary['P2_actual_native_standard_union_qualified'] is False
part2_receipt = (RECEPTION / 'part02/RECEPTION.json').read_bytes()
assert identity(part2_receipt)['git_blob'] == '42383457844bb2832fcb596ad7109f13c15bb27d'
status_raw = json.loads((RECEPTION / 'PRODUCTION_TERMINAL_STATUS.json').read_bytes())
status = status_raw.get('structuredContent')
if status is None:
    status = json.loads(next(x['text'] for x in status_raw['content'] if x['type'] == 'text'))
request = json.loads((BASE / 'BUCHSTAB12_EXPORT_V1_REQUEST.json').read_bytes())
assert status['command'] == request['command'] and status['status'] == 'succeeded' and status['exit_code'] == 0
assert status['memory_mb'] == 512 and status['cpu_threads'] == 1 and status['timeout_seconds'] == 120
assert not status['output_truncated'] and status['output_bytes'] == 562748
report = {'schema': 'p29_buchstab12_complete_original_transport_reception_v1',
    'status': 'PASS_FIVE_PARTS_AND_ALL16_MEMBERS_EXACT_ORIGINAL12_OBJECT_PINS',
    'production_task': status['task_id'], 'production_request_git_blob': '18f416a677ed80b878ca8ae21d1557e3128043e9',
    'production_submission_git_blob': '478d3baed2f6f94a6928e7f0fc0022849bbdc185',
    'production_root_static_review_git_blob': 'b338416c9b3883bafe1ab893f4eb0d2fd3d7a539',
    'production_runtime': {k: status[k] for k in ['runtime_seconds', 'memory_peak_bytes', 'cpu_time_seconds', 'exit_code', 'output_bytes', 'output_truncated']},
    'sealed_archive': {'path': str(archive_path), **identity(archive_path.read_bytes())},
    'descriptor': identity(descriptor_raw), 'parts': parts,
    'member_count': 16, 'members': actual, 'objects': objects,
    'complete_local_directory': str(output), 'source_exporter_exact': True,
    'all_original_snapshots_equal': True, 'all128bit_or64bit_metadata_integers_preserved_by_Python': True,
    'part2_independent_reception': identity(part2_receipt),
    'production_formal_source_reads': 0, 'production_Lean_invocations': 0, 'production_original_object_reads': 12,
    'sealed_part_reads_reread_original_objects': False, 'source_compiler_invocations': 0,
    'new_proof_credit': 0, 'P2_global_missing_claim': False, 'P2_input_union_qualified': False,
    'no_new_standalone_object_blobs_created': True,
    'verification_script': identity(Path(__file__).read_bytes())}
name = BASE / 'BUCHSTAB12_COMPLETE_RECEPTION.json'
name.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'report': identity(name.read_bytes()), 'archive': report['sealed_archive'],
                  'members': 16, 'objects': 12, 'original_object_bytes': sum(x['bytes'] for x in objects)}, indent=2))
