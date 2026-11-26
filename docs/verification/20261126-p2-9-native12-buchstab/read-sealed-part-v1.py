import sys
sys.dont_write_bytecode = True
import base64
import hashlib
import json
import os
import stat
from pathlib import Path

PIN = {'descriptor_path': '/workspace/p29-buchstab12-transfer-20261126-65f2cb2/ARCHIVE_DESCRIPTOR.json', 'descriptor_file': {'bytes': 42013, 'git_blob': 'f1a48a916acf07f850b540344034d99d420c0538', 'sha256': 'ec3b7a8aac7100ccb63e6399a9f10c53eb6670f601f15363799aa084bf4eb5f7'}, 'archive_path': '/workspace/p29-buchstab12-transfer-20261126-65f2cb2/buchstab12-existing-objects.tar.xz', 'archive': {'bytes': 1657884, 'git_blob': '931cb4aaa68b3b08c2bbb809a3470a8f19f031d6', 'sha256': '626152e850c142897b9b02902b8e75b3f7d9f5e5ab67371656bdca531c8f89f0', 'stable_sealed_stat': [27, 918126, 33060, 1, 1657884, 1795677474483813078, 1795677474491812958]}, 'parts': [{'bytes': 400000, 'git_blob': '356ce981ef43e2d25cf2c4a8ad3a714f4b50d5a6', 'index': 0, 'offset': 0, 'sha256': '42700ae060cce04e32e1f8768722a30c6a21d9f84b2646f99863b6b1baeb0282'}, {'bytes': 400000, 'git_blob': '5e0b3e4bcdfc3aa3174a4b24281ce938c369a630', 'index': 1, 'offset': 400000, 'sha256': 'd63d6bf76dd2f8cd1c7b5a1ee23e5a0f32be1e06008e06c6a0c834fe54f9684f'}, {'bytes': 400000, 'git_blob': 'de67e6be7f8f3f7c548f7900b8b129b23e6c64a3', 'index': 2, 'offset': 800000, 'sha256': '5c0d081502cc2c1531d29145ec80e2bc872cc6f54e591128024e9d71a246762a'}, {'bytes': 400000, 'git_blob': '2e1f1aa826b7d9a212c9e828266a1e5bb6bf6db9', 'index': 3, 'offset': 1200000, 'sha256': 'aed2fa37ad47c75e198a0b407435c9261e5aa7c74ec23c5bd751f4f00e32ca84'}, {'bytes': 57884, 'git_blob': 'd2bbb4605da04773d284ad0edcb0826d38f1d8ca', 'index': 4, 'offset': 1600000, 'sha256': 'd985a8d64a5839fde5601883cc3eaef1aca086ae8b7bf32f19d6fd70cc0aaed0'}]}
assert isinstance(PART_INDEX, int) and PART_INDEX in (1, 2, 3, 4)
assert isinstance(SOURCE_TEXT, str)


def stamp(s):
    return [s.st_dev, s.st_ino, s.st_mode, s.st_nlink, s.st_size,
            s.st_mtime_ns, s.st_ctime_ns]


descriptor_path = Path(PIN['descriptor_path'])
descriptor_before = stamp(descriptor_path.lstat())
assert stat.S_ISREG(descriptor_before[2])
assert descriptor_before[4] == PIN['descriptor_file']['bytes']
with descriptor_path.open('rb') as stream:
    assert stamp(os.fstat(stream.fileno())) == descriptor_before
    descriptor_raw = stream.read(PIN['descriptor_file']['bytes'] + 1)
    assert stamp(os.fstat(stream.fileno())) == descriptor_before
assert len(descriptor_raw) == PIN['descriptor_file']['bytes']
assert hashlib.sha256(descriptor_raw).hexdigest() == PIN['descriptor_file']['sha256']
assert hashlib.sha1(b'blob ' + str(len(descriptor_raw)).encode() + b'\0' + descriptor_raw).hexdigest() == PIN['descriptor_file']['git_blob']
assert stamp(descriptor_path.lstat()) == descriptor_before
descriptor = json.loads(descriptor_raw)
assert descriptor['schema'] == 'p29_buchstab12_sealed_archive_transport_v1'
assert descriptor['archive_path'] == PIN['archive_path']
assert descriptor['archive'] == PIN['archive']
assert descriptor['parts'] == PIN['parts']
part = PIN['parts'][PART_INDEX]
assert part['index'] == PART_INDEX and 0 < part['bytes'] <= 400000
assert part['offset'] == PART_INDEX * 400000
assert part['offset'] + part['bytes'] <= PIN['archive']['bytes']
archive_path = Path(PIN['archive_path'])
archive_before = stamp(archive_path.lstat())
assert stat.S_ISREG(archive_before[2])
assert archive_before == PIN['archive']['stable_sealed_stat']
with archive_path.open('rb') as stream:
    assert stamp(os.fstat(stream.fileno())) == archive_before
    stream.seek(part['offset'])
    data = stream.read(part['bytes'])
    assert stamp(os.fstat(stream.fileno())) == archive_before
assert len(data) == part['bytes']
assert hashlib.sha256(data).hexdigest() == part['sha256']
assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == part['git_blob']
archive_after = stamp(archive_path.lstat())
descriptor_after = stamp(descriptor_path.lstat())
assert archive_after == archive_before and descriptor_after == descriptor_before
reader = SOURCE_TEXT.encode('utf-8')
meta = {'schema': 'p29_buchstab12_existing_sealed_part_read_v1',
        'production_task_id': 'job_4cab2f4444374767ace1493321097347',
        'archive_path': str(archive_path), 'archive': PIN['archive'],
        'descriptor_path': str(descriptor_path), 'descriptor_file': PIN['descriptor_file'],
        'part': part, 'archive_before': archive_before, 'archive_after': archive_after,
        'descriptor_before': descriptor_before, 'descriptor_after': descriptor_after,
        'reader': {'bytes': len(reader), 'sha256': hashlib.sha256(reader).hexdigest(),
                   'git_blob': hashlib.sha1(b'blob ' + str(len(reader)).encode() + b'\0' + reader).hexdigest()},
        'original_object_reads': 0, 'formal_source_reads': 0, 'filesystem_writes': 0,
        'recompressions': 0, 'Lean_invocations': 0, 'archive_full_SHA_recomputed_this_part': False,
        'new_proof_credit': 0, 'maximum_stdout_bytes': 550000}
output = ('P29_BUCHSTAB12_SEALED_PART_META ' + json.dumps(meta, sort_keys=True, separators=(',', ':'))
          + '\nP29_BUCHSTAB12_SEALED_PART ' + str(PART_INDEX) + ' '
          + base64.b64encode(data).decode('ascii') + '\n').encode('ascii')
assert len(output) <= 550000
sys.stdout.buffer.write(output)
sys.stdout.buffer.flush()
