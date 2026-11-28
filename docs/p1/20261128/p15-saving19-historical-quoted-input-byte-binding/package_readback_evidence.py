"""Seal the historical quoted-input identity check; never invoke Lean/Lake."""
from pathlib import Path
import datetime
import filecmp
import hashlib
import json
import zipfile

if not __debug__:
    raise SystemExit('Integrity checks require unoptimized Python')

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'readback-00003'


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def save(name, value):
    (ROOT / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


result = json.loads((OUT / 'READBACK_RESULTS.json').read_text())
assert result['status'] == 'PASS_READ_ONLY_HISTORICAL_QUOTE_BYTEWISE_READBACK'
assert result['files'] == 26 and result['total_bytes'] == 80189086
assert result['new_mathematical_credit'] == 0
assert result['old_normal_kernel_or_audit_replay_commands'] == 0
lane = json.loads((ROOT / 'LANE_00003.json').read_text())
assert lane['status'] == 'VALIDATION_LANE_FINISHED' and lane['exit_code'] == 0
assert lane['state_sha256'] == '9f0688f701d861e3af832a1ab17d8d0fab41c1d30a3261f24922cae058e7b152'
command = json.loads((OUT / 'COMMAND.json').read_text())
assert command['exit_code'] == 0
assert command['cwd'] == '/workspace/blue-member-build'
assert command['argv'] == [
    'lean', '-DmaxRecDepth=100000', '-DmaxHeartbeats=4000000',
    str(ROOT / 'ReadQuotedInputsAudit_00003.lean')]
before = json.loads((OUT / 'INPUTS_BEFORE.json').read_text())
assert before == json.loads((OUT / 'INPUTS_AFTER.json').read_text())
assert len(before) == len({row['path'] for row in before}) == 268
for row in before:
    path = Path(row['path'])
    assert path.stat().st_size == row['bytes'] and digest(path) == row['sha256']
assert len(result['rows']) == 26
for row in result['rows']:
    assert row['full_bytewise_equal']
    left = row['current_original']
    right = row['decoded_historical_quoted_input']
    assert left['bytes'] == right['bytes'] and left['sha256'] == right['sha256']
    assert filecmp.cmp(left['path'], right['path'], shallow=False)
    assert digest(right['path']) == right['sha256']
assert (OUT / 'EXECUTED_READER.lean').read_bytes() == (ROOT / 'ReadQuotedInputsAudit_00003.lean').read_bytes()
assert (OUT / 'EXECUTED_WORKER.py').read_bytes() == (ROOT / 'readback_worker_00003.py').read_bytes()
review = json.loads((ROOT / 'INDEPENDENT_READBACK_REVIEW.json').read_text())
assert review['blocking_findings'] == []
for key, path in [
    ('source_sha256', OUT / 'EXECUTED_READER.lean'),
    ('worker_sha256', OUT / 'EXECUTED_WORKER.py'),
    ('driver_sha256', ROOT / 'validate_00003.py'),
    ('result_sha256', OUT / 'READBACK_RESULTS.json'),
    ('lane_sha256', ROOT / 'LANE_00003.json'),
    ('input_manifest_sha256', OUT / 'INPUTS_BEFORE.json'),
]:
    assert review[key] == digest(path)

owners = json.loads((ROOT / 'ORIGINAL_ACCEPTED_OWNERS.json').read_text())['owners']
assert len(owners) == 34
assert sum(len(row['source_and_five_outputs']) for row in owners) == 204
old = ROOT.parent / '20261128-p15-saving19-accepted-source-reuse'
oldmeta = json.loads((old / 'ARCHIVE.json').read_text())
oldzip = old / oldmeta['archive']
assert digest(oldzip) == oldmeta['sha256']
with zipfile.ZipFile(oldzip) as archive:
    assert archive.testzip() is None

save('ADMISSION.json', {
    'status': 'ACCEPTED_EXACT_HISTORICAL_QUOTED_INPUT_BYTE_IDENTITY',
    'attempt': 'readback-00003',
    'existing_data_modules_read': 26,
    'existing_accepted_modules_pinned': 34,
    'source_and_five_output_fields_pinned': 204,
    'input_fingerprints_unchanged': 268,
    'files': 26,
    'bytes': 80189086,
    'packed_leaves': 425984,
    'reader_does_not_read_current_JSON_files': True,
    'reader_getEnv_find_value_reads_original_imported_definition_Expr': True,
    'full_bytewise_comparison_after_independent_decode': True,
    'OfNat_scope': 'Only the exactly pinned historical mkNatLit sources: the reader checks OfNat.ofNat arity3/typeNat/natVal argument, but does not independently validate the instance argument. No claim for arbitrary OfNat expressions.',
    'new_compiletime_metadata_read_commands': 1,
    'old_normal_kernel_or_old_audit_replay_commands': 0,
    'new_mathematical_credit': 0,
    'historical_quoted_inputs_bound_to_current_26_JSON': True,
    'concrete_parse_shape_numerics_ownership_claimed': False,
    'P1_monolithic_archive_closed': False,
    'all13_cells_complete': False,
    'original_register': '18/21',
    'three_HOLDs_unchanged': True,
    'whole_P1_4_complete': False,
    'whole_P1_5_complete': False,
})

members = {}
for path in ROOT.rglob('*'):
    if not path.is_file() or path.is_symlink():
        continue
    relative = path.relative_to(ROOT)
    if 'decoded' in relative.parts or '__pycache__' in relative.parts:
        continue
    if path.name in ['ARCHIVE.json', 'PUBLISHED.json'] or path.suffix == '.zip':
        continue
    members[str(relative)] = path.read_bytes()
for name in ['ARCHIVE.json', 'PUBLISHED.json', 'SOURCE_REUSE.json', 'INDEPENDENT_REVIEW.json', oldmeta['archive']]:
    members['prior-accepted-source-reuse/' + name] = (old / name).read_bytes()
index = [dict(path=name, bytes=len(data), sha256=hashlib.sha256(data).hexdigest())
         for name, data in sorted(members.items())]
members['FILE_INDEX.json'] = (json.dumps(index, indent=2) + '\n').encode()
target = ROOT / 'saving19-historical-quoted-input-byte-binding-evidence.zip'
assert not target.exists()
with zipfile.ZipFile(target, 'x', zipfile.ZIP_DEFLATED) as archive:
    for name, data in sorted(members.items()):
        archive.writestr(name, data)
with zipfile.ZipFile(target) as archive:
    assert archive.testzip() is None
    assert len(archive.namelist()) == len(members)
    for row in index:
        data = archive.read(row['path'])
        assert len(data) == row['bytes'] and hashlib.sha256(data).hexdigest() == row['sha256']
save('ARCHIVE.json', dict(
    archive=target.name, bytes=target.stat().st_size, sha256=digest(target),
    members=len(members), all_member_CRCs_and_fingerprints_verified=True,
    original_decoded_80MB_not_duplicated=True,
    original_JSON_full_bytewise_comparisons=26,
    old_normal_kernel_or_audit_replays=0, new_mathematical_credit=0,
    sealed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
print('SEALED', target.stat().st_size, digest(target), len(members))
