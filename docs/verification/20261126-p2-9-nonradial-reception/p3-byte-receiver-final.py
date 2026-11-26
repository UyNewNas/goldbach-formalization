from pathlib import Path, PurePosixPath
import base64, datetime, hashlib, io, json, tarfile, urllib.request

# These archive constants bind the completed unique P2 v2 readonly export;
# all three stdout pages and all fifteen original members were received exactly.
ARCHIVE_BLOB = '8a8702a17098ae6129603a421d94f48526cfd653'
ARCHIVE_BYTES = 102274
ARCHIVE_SHA256 = 'c48f8974537d91d1113a9d67b71ca7a3ee0407a67ced3476456f1f85ece56cbb'

BASE = Path('/workspace/p29-nonradial-receive-20261126-0285b3ed')
OLD = Path('/workspace/p29-unit-tail-20261126-8131f7d6')
MODULE = 'ImbalancedChen.P2FiniteMarkedGamma5NonradialSupport'
SOURCE_BLOB = '2091608eaeec53f3f8b60224fb7b10048642805e'
SOURCE_SHA256 = '3d6f71b982a984e7fdd880b21ab496237ebeb656bed24990dedcfec96dff74bd'
OBJECT_SHA256 = '0285b3ed20b8b8d3b5a540dab4f2c6e60a8120a0c6eead3f081036ae8dbe5883'
RECORD_SHA256 = 'b9798231004d75befa227ecf4d8b4b9a5238a8cd25413d1c19bd2fc4d27ad97f'
AUDIT_SHA256 = '70335088765bca1a2f6475b998a9e587343901a6767ed6748bca7a20fa5e8f45'
CLOSURE_SIGNATURE = 'a5261ca78e6cba51f8d88906419b3baf19bdc07612f165105fc575e3ab7d78e7'
EXPORTER_SHA256 = 'bcff80ededb5478ba85bcec98ffdebc59780cd03b28b6e4d7c96b33aa7011c70'
UNIT_BORROWED_SHA256 = '3e7c6baf5d8ef30790fd6e485c258c97d957f1c8a8bbfad22945a12578aba219'
UNIT_QUALIFICATION_SHA256 = '1d63ecbcc0a21300314d26b8493d6ed07d30d622c745e1ffc1956bf10b324a21'
EXPECTED_DEPS = {
    'ImbalancedChen.P2FiniteMarkedGamma5PhysicalExtension',
    'ImbalancedChen.P2FiniteMarkedGamma5LogProfileCore',
    'ImbalancedChen.P2SmoothPositiveArgumentCore',
    'ImbalancedChen.P4BSmoothGateUpperStep',
    'ImbalancedChen.P2SeedOmegaCutoffConstants',
}
protected = {}
sha = lambda b: hashlib.sha256(b).hexdigest()
git_blob = lambda b: hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
encode = lambda x: (json.dumps(x, sort_keys=True, indent=2) + '\n').encode()


def stamp(path):
    s = Path(path).stat()
    return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns]


def read_old(path, expected):
    path = Path(path)
    assert path.is_relative_to(OLD), ('outside original P3 qualification root', str(path))
    before = stamp(path)
    data = path.read_bytes()
    assert stamp(path) == before
    assert sha(data) == expected, ('old input drifted', str(path), sha(data), expected)
    row = {'path': str(path), 'bytes': len(data), 'sha256': expected, 'stat': before}
    if str(path) in protected:
        assert protected[str(path)] == row
    protected[str(path)] = row
    return data


def write_new(path, data):
    path = Path(path)
    assert path.is_relative_to(BASE)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as f:
        f.write(data)


assert isinstance(ARCHIVE_BLOB, str) and len(ARCHIVE_BLOB) == 40
assert isinstance(ARCHIVE_BYTES, int) and 0 < ARCHIVE_BYTES < 1000000
assert isinstance(ARCHIVE_SHA256, str) and len(ARCHIVE_SHA256) == 64
assert not BASE.exists(), 'Do not repeat an existing receiver; inspect its original receipt.'
BASE.mkdir()
write_new(BASE / 'receiver.py', SOURCE_TEXT.encode())

response = json.load(urllib.request.urlopen(
    'https://api.github.com/repos/UyNewNas/goldbach-formalization/git/blobs/' + ARCHIVE_BLOB,
    timeout=45))
assert response['encoding'] == 'base64'
archive = base64.b64decode(''.join(response['content'].split()), validate=True)
assert len(archive) == ARCHIVE_BYTES and sha(archive) == ARCHIVE_SHA256
assert git_blob(archive) == ARCHIVE_BLOB
write_new(BASE / 'original-nonradial.tar.gz', archive)

members = {}
with tarfile.open(fileobj=io.BytesIO(archive), mode='r:gz') as tf:
    infos = tf.getmembers()
    assert sum(info.size for info in infos) < 100000000
    for info in infos:
        name = info.name
        p = PurePosixPath(name)
        assert info.isfile() and not p.is_absolute() and '..' not in p.parts
        assert str(p) == name and name not in members
        f = tf.extractfile(info)
        assert f is not None
        content = f.read()
        assert len(content) == info.size
        members[name] = content
assert 'FILE_MANIFEST.json' in members
manifest = json.loads(members['FILE_MANIFEST.json'])
assert manifest['schema'] == 'p29_nonradial_object_archive_manifest_v1'
assert manifest['module'] == MODULE
assert manifest['source_recompilations'] == manifest['kernel_replays'] == manifest['new_manuscript_credit'] == 0
assert set(manifest['files']) == set(members) - {'FILE_MANIFEST.json'}
for name, entry in manifest['files'].items():
    assert entry == {'bytes': len(members[name]), 'sha256': sha(members[name])}
assert sha(members['EXPORTER.py']) == EXPORTER_SHA256

source_name = 'source/' + MODULE.replace('.', '/') + '.lean'
object_name = 'objects/' + MODULE.replace('.', '/') + '.olean'
assert sha(members[source_name]) == SOURCE_SHA256 and git_blob(members[source_name]) == SOURCE_BLOB
assert sha(members[object_name]) == OBJECT_SHA256
assert sha(members['ORIGINAL_RECORD.json']) == RECORD_SHA256
assert sha(members['original-audit/latest.json']) == AUDIT_SHA256
record = json.loads(members['ORIGINAL_RECORD.json'])
records = json.loads(members['ORIGINAL_RELEVANT_RECORDS.json'])
audit = json.loads(members['original-audit/latest.json'])
binding = json.loads(members['BINDING_RECEIPT.json'])
assert records[MODULE] == record
assert set(records) == EXPECTED_DEPS | {MODULE}
assert record['module'] == MODULE and record['exit_code'] == 0 and record['new_strict_compile'] is True
assert record['source_sha256'] == SOURCE_SHA256 and record['object_sha256'] == OBJECT_SHA256
assert record['closure_signature'] == CLOSURE_SIGNATURE
assert record['deps'] == {'ImbalancedChen.P2FiniteMarkedGamma5PhysicalExtension':
                          'c80ed8b590734eb936bafd1a50889d1f431a8617bf21d059d7f4f30c4d68138c'}
assert audit['module'] == MODULE and audit['accepted'] is True
assert audit['source_sha256'] == SOURCE_SHA256 and audit['object_sha256'] == OBJECT_SHA256
assert audit['compile_closure_signature'] == CLOSURE_SIGNATURE
assert audit['audit']['exit_code'] == audit['replay']['exit_code'] == 0
assert audit['audit']['declaration_count'] == 6
assert audit['input_snapshot']['project'] == audit['replay_binding']['project']
assert set(audit['input_snapshot']['project']) == set(records)
for name, digest in audit['artifacts'].items():
    assert sha(members['original-artifacts/' + name]) == digest
assert len(record['attempts']) == 2
assert [attempt['exit_code'] for attempt in record['attempts']] == [1, 0]
for index, attempt in enumerate(record['attempts'], 1):
    name = 'original-normal/attempt' + str(index) + '.log'
    assert name in members
    assert binding['origin_files'][name]['origin'] == str(Path('/workspace/p2-9-20261125') / attempt['log'])
assert binding['module'] == MODULE and binding['source_git_blob'] == SOURCE_BLOB
assert binding['source_sha256'] == SOURCE_SHA256 and binding['object_sha256'] == OBJECT_SHA256
assert binding['original_record_canonical_sha256'] == RECORD_SHA256
assert binding['original_receipt_sha256'] == AUDIT_SHA256
assert binding['original_closure_signature'] == CLOSURE_SIGNATURE
assert binding['original_owned_declaration_count'] == 6
assert set(binding['relevant_record_modules']) == set(records)
assert binding['original_relevant_records_sha256'] == sha(members['ORIGINAL_RELEVANT_RECORDS.json'])
assert binding['all_relevant_records_and_actual_dependency_files_unchanged'] is True
assert binding['all_original_normal_attempt_logs_preserved'] is True
assert binding['source_object_original_audit_and_full_types_preserved'] is True
assert binding['source_recompilations'] == binding['kernel_replays'] == binding['new_manuscript_credit'] == 0
assert binding['remote_source_or_object_writes'] == 0

# The original eighteen-module proof qualification is reused, never rerun.
borrowed = json.loads(read_old(OLD / 'verification/BORROWED_OBJECTS.json', UNIT_BORROWED_SHA256))
qualified = json.loads(read_old(OLD / 'verification/SUPPLY_QUALIFICATION.json', UNIT_QUALIFICATION_SHA256))
assert len(borrowed) == 18 and set(borrowed) == set(qualified['borrowed_modules'])
assert qualified['status'] == 'PASS_CURRENT_P3_BOUND_IMPORTS_NAMED_KERNEL_FULL_OWNED'
assert qualified['borrowed_object_records_sha256'] == UNIT_BORROWED_SHA256
assert qualified['owned_count'] == 394
assert qualified['named_kernel']['exit_code'] == qualified['full_owned']['exit_code'] == 0
assert qualified['source_recompilations'] == qualified['new_manuscript_credit'] == 0
for phase in ['named_kernel', 'full_owned']:
    old = qualified[phase]
    read_old(old['log_path'], old['log_sha256'])

prebound = {}
for name, entry in sorted(records.items()):
    original = audit['input_snapshot']['project'][name]
    assert original['source_sha256'] == entry['source_sha256']
    assert original['object_sha256'] == entry['object_sha256']
    assert str(Path('/workspace/p2-9-20261125') / original['source']) == str(Path('/workspace/p2-9-20261125') / entry['source'])
    assert original['object'] == entry['object']
    assert entry['exit_code'] == 0
    for dep, digest in entry.get('deps', {}).items():
        assert dep in records and records[dep]['object_sha256'] == digest
    if name == MODULE:
        continue
    existing = borrowed[name]
    assert existing['module'] == name
    assert existing['source_sha256'] == entry['source_sha256']
    assert existing['object_sha256'] == entry['object_sha256']
    assert set(existing['direct_project_imports']) == set(entry.get('deps', {}))
    src = read_old(existing['source'], entry['source_sha256'])
    obj = read_old(existing['object'], entry['object_sha256'])
    assert len(src) == existing['source_bytes'] and len(obj) == existing['object_bytes']
    prebound[name] = {
        'module': name, 'source': existing['source'], 'source_sha256': sha(src),
        'source_bytes': len(src), 'object': existing['object'], 'object_sha256': sha(obj),
        'object_bytes': len(obj), 'direct_project_imports': existing['direct_project_imports'],
        'original_P2_record': entry,
    }
assert set(prebound) == EXPECTED_DEPS

# Every member is preserved verbatim; no old directory is written or reassembled.
for name, content in sorted(members.items()):
    write_new(BASE / 'original-evidence' / name, content)
for path, observation in protected.items():
    assert stamp(path) == observation['stat'], ('old file metadata changed', path)
    assert sha(Path(path).read_bytes()) == observation['sha256'], ('old file bytes changed', path)

receipt = {
    'schema': 'p29_nonradial_P3_byte_reception_and_five_project_dependencies_prebinding_v1',
    'status': 'RECEIVED_BYTES_AND_FIVE_PROJECT_DEPENDENCIES_PREBOUND_NO_LEAN',
    'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'receiver': str(BASE), 'module': MODULE,
    'receiver_script_sha256': sha(SOURCE_TEXT.encode()), 'receiver_script_git_blob': git_blob(SOURCE_TEXT.encode()),
    'original_export_job': '051da48b01a74499a1ac30bf39ae463d',
    'previous_failed_export_job': 'ae356f6e7ff64a6e8d4d086e6d4819cd',
    'previous_failed_export_evidence_blob': '0fd0a6d5b581c725dd1b1f66debfb8a2df14b679',
    'archive': {'git_blob': ARCHIVE_BLOB, 'bytes': len(archive), 'sha256': sha(archive)},
    'file_manifest_sha256': sha(members['FILE_MANIFEST.json']),
    'binding_receipt_sha256': sha(members['BINDING_RECEIPT.json']),
    'preserved_archive_members': len(members),
    'source': str(BASE / 'original-evidence' / source_name), 'source_git_blob': SOURCE_BLOB,
    'source_sha256': SOURCE_SHA256, 'source_bytes': len(members[source_name]),
    'object': str(BASE / 'original-evidence' / object_name),
    'object_sha256': OBJECT_SHA256, 'object_bytes': len(members[object_name]),
    'original_P2_accepted_owned_count': 6, 'original_normal_attempts': [1, 0],
    'reused_P3_eighteen_module_qualification': {
        'root': str(OLD), 'receipt_sha256': UNIT_QUALIFICATION_SHA256,
        'borrowed_objects_sha256': UNIT_BORROWED_SHA256, 'original_owned_count': 394,
    },
    'prebound_dependencies': prebound, 'protected_existing_P3_files': protected,
    'source_compilations': 0, 'kernel_replays': 0, 'full_owned_replays': 0,
    'new_manuscript_credit': 0, 'existing_P3_files_unchanged': True,
    'actual_combined_import_probe_run': False,
    'actual_combined_import_probe_pending_until_other_suppliers_arrive': True,
    'whole_standard_input_equality_claim': False, 'full_P2_9_complete': False,
    'scope': 'Exact original NonradialSupport source/object/evidence transfer and five existing P3 project-dependency byte matches only. The original accepted six owned declarations are not new proof credit. No Lean process, target compilation, kernel replay, full-owned replay, standard-facet union claim, or downstream target acceptance.',
}
write_new(BASE / 'P3_RECEPTION_PREBINDING.json', encode(receipt))
print(json.dumps(receipt, sort_keys=True, indent=2), flush=True)
