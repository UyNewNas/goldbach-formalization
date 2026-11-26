import sys
sys.dont_write_bytecode = True
import base64
import datetime
import hashlib
import io
import json
import lzma
import os
import shutil
import stat
import tarfile
from pathlib import Path

PIN_INDEX = {'schema': 'p29_buchstab12_exact_old_object_transfer_selection_v1', 'original_index': {'git_blob': '65f2cb2a0aafffdca7bfc42d3c46478b2be5936f', 'bytes': 35907, 'sha256': 'ce7f66e7f392a9574ad8ed4cb03a6dd9451c17699f407ce7eddfc03eb83b6daf'}, 'objects': [{'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabBands', 'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBands.olean', 'bytes': 1005224, 'sha256': '7af00b12866a5df8dc2da5157172281aa509182a2a321390d60db10588b43b23', 'archive_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBands.olean'}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabBase', 'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBase.olean', 'bytes': 495736, 'sha256': 'bdb45e61412726782fc7801b23f786f8436a763d94330223c38c698e49137979', 'archive_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBase.olean'}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabBaseEstimate', 'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBaseEstimate.olean', 'bytes': 302232, 'sha256': 'a0ed17870cc9b34aa77cc1eacc96380f26a136e98f5aba1a8f5e70418b0ff195', 'archive_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBaseEstimate.olean'}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabBounds', 'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBounds.olean', 'bytes': 417864, 'sha256': '40e6739d0928ae2c70deca8b80307dd87595f0076c851e4a2cf9e0098a749b75', 'archive_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabBounds.olean'}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabCount', 'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabCount.olean', 'bytes': 215320, 'sha256': '539aa96f95335718ebeaab8c69e9cdbdd5d00d7c929e8c61909592dfff628d7d', 'archive_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabCount.olean'}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabFunction', 'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabFunction.olean', 'bytes': 313800, 'sha256': 'f78a815dea0aad0833aac831dc2233cdcd3fd5c7681d6220be3b253786b1b5ee', 'archive_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabFunction.olean'}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabIntegral', 'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabIntegral.olean', 'bytes': 355112, 'sha256': '812cb313a21b538c183715b1b829d286628fd30a8a067ca43fb915a54b9a083b', 'archive_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabIntegral.olean'}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabPNT', 'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabPNT.olean', 'bytes': 239240, 'sha256': '1f48755c44eadce94bfd62332f1ca9c8892aefd7692a34407ecbcdb8350bcaef', 'archive_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabPNT.olean'}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabPrimeSums', 'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabPrimeSums.olean', 'bytes': 708360, 'sha256': '85e0756e603bb8b5e51b87247b989a3eb0a7c0c25c9b6dfb1e786ebf2fbca739', 'archive_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabPrimeSums.olean'}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniform', 'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniform.olean', 'bytes': 452912, 'sha256': '326ca610964a3a6b2659cd4230681c266abbeb48c7b1fc0fcca322f33c592d90', 'archive_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniform.olean'}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniformAbel', 'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformAbel.olean', 'bytes': 1921552, 'sha256': '0891f3fa7c30839054029fa5b2b3d28b116a9bddb8a74e2207d223913ff0b368', 'archive_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformAbel.olean'}, {'module': 'MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniformFixedCompat', 'path': '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformFixedCompat.olean', 'bytes': 1339680, 'sha256': '71575dea300b4d15714d5c92392589faed3542cc3ee13a51284dbb6e0eb9faa1', 'archive_member': 'objects/MathlibNt/SieveTheory/LiLiuPrereqBuchstabUniformFixedCompat.olean'}], 'identity_table': {'path': '/workspace/scratch/005887317b49/p29-current/OMITTED_P2_NATIVE515_NAME_COVERAGE.json', 'bytes': 12714, 'sha256': 'ecbfd2825d47ea7d91becbaff8ff5e90a919f15f75b653b5b1fe6738a8bb997b', 'git_blob': '05579099ea2765195634f5508c42b766fbc4c546'}, 'prior_authority_reference': {'exact_original_controller': {'path': '/workspace/scratch/005887317b49/p29-current/nonunit-reuse-fixed.py', 'bytes': 24776, 'sha256': '553d01ed48c5717f3fc87f7141fb92287f19b91488b5979120455ff76f3da5c9', 'git_blob': '217cf5b3e7fd29422a29a74d2e3fb717444b0d8b'}, 'original_archive_member': {'path': 'controller-evidence/controller.py', 'bytes': 24776, 'sha256': '553d01ed48c5717f3fc87f7141fb92287f19b91488b5979120455ff76f3da5c9'}, 'lines_with_pinned_old_authorities': ["mp=SUPPLY/'supply-bindings/IMPORT_PART_BINDINGS.json';protect(mp,'a0b1c135be1c2dbe33c3854db85a43cd27bb9f6777d5c21c6a41fe5170e200c6')", "np=SUPPLY/'SOURCE_AND_OUTPUTS_AFTER.json';protect(np,'8041164c6992dff40b6219e0838eb31c64e7b9097c36d9ac5320d524a240adb2')"], 'original_prior_full_import_map_not_read_here': True, 'native12_objects_not_in_this_44_member_manifest': True}, 'existing_Nonunit2_44member_archive_reexported': False, 'P2_28_candidate_result': {'job_id': '3df47fa860e549dab204d053b11551d9', 'stdout_git_blob': '0cee1f5eaf2225179bf8591c8806b00d059897ab', 'stdout_sha256': '32d897f4d7212609572781c2f6ba342868a6fdd6d61c6400c9c96b6680ed8e85', 'all_28_candidates_no_entry': True, 'P2_global_missing_claim': False}}
BASE = Path('/workspace/p29-buchstab12-transfer-20261126-65f2cb2')
ARCHIVE_NAME = 'buchstab12-existing-objects.tar.xz'
DESCRIPTOR_NAME = 'ARCHIVE_DESCRIPTOR.json'
EXPECTED_TOTAL_OBJECT_BYTES = 7767032
RAW_PART_BYTES = 400000
MAX_STDOUT_BYTES = 700000
MAX_ARCHIVE_BYTES = 12 * 1024 * 1024
MIN_FREE_BYTES = 16 * 1024 * 1024


def stamp(s):
    return [s.st_dev, s.st_ino, s.st_mode, s.st_nlink, s.st_size,
            s.st_mtime_ns, s.st_ctime_ns]


def snapshot(row):
    path = Path(row['path'])
    resolved = path.resolve(strict=True)
    logical = path.lstat()
    target = path.stat()
    assert resolved.is_relative_to('/workspace')
    assert stat.S_ISREG(target.st_mode)
    assert target.st_size == row['bytes']
    return {'resolved_path': str(resolved), 'logical_lstat': stamp(logical),
            'target_stat': stamp(target)}


def encoded_json(obj):
    return (json.dumps(obj, sort_keys=True, indent=2) + '\n').encode('ascii')


def bytes_identity(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
            'git_blob': hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()}


source_text = globals().get('SOURCE_TEXT')
assert isinstance(source_text, str), 'Use the pinned in-memory launcher.'
exporter = source_text.encode('utf-8')
assert not BASE.exists() and not BASE.is_symlink(), 'Exclusive new transfer directory already exists.'
free_before = shutil.disk_usage('/workspace').free
assert free_before >= MIN_FREE_BYTES, 'Insufficient free space for this bounded new transfer archive.'
assert PIN_INDEX['original_index']['git_blob'] == '65f2cb2a0aafffdca7bfc42d3c46478b2be5936f'
assert PIN_INDEX['original_index']['sha256'] == 'ce7f66e7f392a9574ad8ed4cb03a6dd9451c17699f407ce7eddfc03eb83b6daf'
rows = PIN_INDEX['objects']
assert len(rows) == 12 and len({r['module'] for r in rows}) == 12
assert sum(r['bytes'] for r in rows) == EXPECTED_TOTAL_OBJECT_BYTES
assert all(r['module'].startswith('MathlibNt.SieveTheory.LiLiuPrereqBuchstab') for r in rows)
for row in rows:
    relative = row['module'].replace('.', '/') + '.olean'
    assert row['path'] == '/workspace/blue-member-build/.lake/packages/goldbach/.lake/build/lib/lean/' + relative
    assert row['archive_member'] == 'objects/' + relative
    assert isinstance(row['bytes'], int) and 0 < row['bytes'] <= 2 * 1024 * 1024
    assert len(row['sha256']) == 64 and all(c in '0123456789abcdef' for c in row['sha256'])
assert len({r['path'] for r in rows}) == len({r['archive_member'] for r in rows}) == 12
started_utc = datetime.datetime.now(datetime.timezone.utc).isoformat()
before = {r['module']: snapshot(r) for r in rows}
members = {}
ingestion = []
for row in rows:
    path = Path(row['path'])
    original = before[row['module']]
    with path.open('rb') as stream:
        assert stamp(os.fstat(stream.fileno())) == original['target_stat']
        data = stream.read(row['bytes'] + 1)
        assert stamp(os.fstat(stream.fileno())) == original['target_stat']
    assert len(data) == row['bytes']
    digest = hashlib.sha256(data).hexdigest()
    assert digest == row['sha256'], 'Original Buchstab object no longer matches the fixed P1 pin.'
    after_read = snapshot(row)
    assert after_read == original, 'Original object logical path or physical stamp changed during reading.'
    members[row['archive_member']] = data
    ingestion.append({'module': row['module'], 'original_path': row['path'],
                      'archive_member': row['archive_member'], **bytes_identity(data),
                      'before': original, 'after_own_read': after_read})
after_all_reads = {r['module']: snapshot(r) for r in rows}
assert before == after_all_reads, 'An original object changed during the twelve-object ingestion.'
boundary = {'original_object_reads': 12, 'formal_source_files_read': 0,
            'NonunitRoughUniform_and_Core_read_or_reexported': False,
            'directory_scans': 0, 'Lean_invocations': 0, 'old_normal_kernel_owned_replays': 0,
            'new_proof_credit': 0, 'P2_global_missing_claim': False,
            'P2_actual_native_standard_union_qualified': False,
            'original_files_modified': False, 'only_new_transfer_directory_written': str(BASE)}
receipt = {'schema': 'p29_buchstab12_original_object_ingestion_v1', 'started_utc': started_utc,
           'completed_ingestion_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'exporter': bytes_identity(exporter), 'original_index': PIN_INDEX['original_index'],
           'original_objects': ingestion, 'after_all_reads': after_all_reads,
           'all_original_pins_and_stamps_stable': True, 'boundary': boundary}
members['PIN_INDEX.json'] = encoded_json(PIN_INDEX)
members['BINDING_RECEIPT.json'] = encoded_json(receipt)
members['EXPORTER.py'] = exporter
manifest = {name: bytes_identity(data) for name, data in sorted(members.items())}
members['FILE_MANIFEST.json'] = encoded_json(manifest)
assert len(members) == 16
assert sum(len(data) for data in members.values()) + 32768 < MAX_ARCHIVE_BYTES
BASE.mkdir(mode=0o700, parents=False, exist_ok=False)
archive_path = BASE / ARCHIVE_NAME
with archive_path.open('xb') as sink:
    with lzma.LZMAFile(sink, mode='w', format=lzma.FORMAT_XZ, preset=6) as compressed:
        with tarfile.open(fileobj=compressed, mode='w|', format=tarfile.USTAR_FORMAT) as archive:
            for name, data in sorted(members.items()):
                info = tarfile.TarInfo(name)
                info.size = len(data)
                info.mode = 0o444
                info.mtime = 0
                info.uid = info.gid = 0
                info.uname = info.gname = ''
                archive.addfile(info, io.BytesIO(data))
    sink.flush()
    os.fsync(sink.fileno())
archive_path.chmod(0o444)
sealed_stamp = stamp(archive_path.stat())
assert stat.S_ISREG(sealed_stamp[2]) and 0 < sealed_stamp[4] < MAX_ARCHIVE_BYTES
parts = []
full_sha = hashlib.sha256()
full_git = hashlib.sha1(b'blob ' + str(sealed_stamp[4]).encode() + b'\0')
first_part = None
with archive_path.open('rb') as stream:
    assert stamp(os.fstat(stream.fileno())) == sealed_stamp
    offset = 0
    while True:
        data = stream.read(RAW_PART_BYTES)
        if not data:
            break
        if first_part is None:
            first_part = data
        full_sha.update(data)
        full_git.update(data)
        parts.append({'index': len(parts), 'offset': offset, **bytes_identity(data)})
        offset += len(data)
    assert stamp(os.fstat(stream.fileno())) == sealed_stamp
assert offset == sealed_stamp[4] and stamp(archive_path.stat()) == sealed_stamp
after_seal = {r['module']: snapshot(r) for r in rows}
assert after_seal == before, 'An original object changed before the archive seal was complete.'
descriptor = {'schema': 'p29_buchstab12_sealed_archive_transport_v1',
    'status': 'SEALED_EXISTING_OBJECT_BYTES_ONLY_NOT_NEW_QUALIFICATION',
    'archive_path': str(archive_path), 'archive': {'bytes': offset, 'sha256': full_sha.hexdigest(),
        'git_blob': full_git.hexdigest(), 'stable_sealed_stat': sealed_stamp},
    'member_count': len(members), 'member_manifest': {name: bytes_identity(data) for name, data in sorted(members.items())},
    'binding_receipt': receipt, 'post_seal_original_snapshots': after_seal,
    'all_original_stamps_equal_before_after_ingestion_and_after_seal': True,
    'exporter': bytes_identity(exporter), 'original_index': PIN_INDEX['original_index'],
    'free_bytes_before_directory_creation': free_before, 'maximum_archive_bytes': MAX_ARCHIVE_BYTES,
    'raw_part_bytes': RAW_PART_BYTES, 'parts': parts, 'first_part_emitted_by_this_job': 0,
    'remaining_parts_protocol': 'Only read the already sealed archive at these exact offsets; validate its pinned stat and each part SHA. Never reread original objects or recompress.',
    'maximum_stdout_bytes': MAX_STDOUT_BYTES, 'boundary': boundary,
    'completed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
descriptor_raw = encoded_json(descriptor)
descriptor_path = BASE / DESCRIPTOR_NAME
with descriptor_path.open('xb') as stream:
    stream.write(descriptor_raw)
    stream.flush()
    os.fsync(stream.fileno())
descriptor_path.chmod(0o444)
assert stamp(archive_path.stat()) == sealed_stamp
meta = {'descriptor_path': str(descriptor_path), 'descriptor_file': bytes_identity(descriptor_raw),
        'descriptor': descriptor, 'emitted_part': parts[0]}
encoded_first_part = base64.b64encode(first_part).decode('ascii')
output = ('P29_BUCHSTAB12_ARCHIVE_META ' + json.dumps(meta, sort_keys=True, separators=(',', ':'))
          + '\nP29_BUCHSTAB12_ARCHIVE_PART 0 ' + encoded_first_part + '\n').encode('ascii')
assert len(output) <= MAX_STDOUT_BYTES, 'The fixed first-part transport would exceed the complete stdout bound.'
sys.stdout.buffer.write(output)
sys.stdout.buffer.flush()
