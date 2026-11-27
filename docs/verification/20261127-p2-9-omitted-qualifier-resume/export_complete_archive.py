import base64
import hashlib
import json
import lzma
import math
from pathlib import Path

BASE = Path('/workspace/p29-omitted-prime-wall-p2-20261126-ef40c77')
SOURCE = BASE / 'qualified-omitted-prime-wall.tar.xz'
DEST = BASE / 'qualified-omitted-prime-wall-root-transport-dict128.tar.xz'
SOURCE_BYTES = 13529388
SOURCE_SHA = '08f8d568f01d80dd4b4fa490b7fbe0d117265e343ebaef0c9d346579f544d978'
PART_BYTES = 393216


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''):
            h.update(block)
    return h.hexdigest()


def stamp(path):
    s = path.stat()
    return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns]


assert SOURCE.is_file() and not SOURCE.is_symlink() and SOURCE.stat().st_size == SOURCE_BYTES
before = stamp(SOURCE)
assert digest(SOURCE) == SOURCE_SHA and stamp(SOURCE) == before
assert not DEST.exists() and not DEST.is_symlink()
tar_hash = hashlib.sha256()
tar_bytes = 0
encoder = lzma.LZMACompressor(format=lzma.FORMAT_XZ,
    filters=[{'id': lzma.FILTER_LZMA2, 'preset': 9, 'dict_size': 134217728}])
with lzma.open(SOURCE, 'rb') as source, DEST.open('xb') as dest:
    while True:
        block = source.read(1048576)
        if not block:
            break
        tar_bytes += len(block)
        assert tar_bytes <= 1073741824
        tar_hash.update(block)
        dest.write(encoder.compress(block))
    dest.write(encoder.flush())
del encoder
assert stamp(SOURCE) == before and digest(SOURCE) == SOURCE_SHA
check_hash = hashlib.sha256()
check_bytes = 0
with lzma.open(DEST, 'rb') as f:
    for block in iter(lambda: f.read(1048576), b''):
        check_bytes += len(block)
        check_hash.update(block)
assert check_bytes == tar_bytes and check_hash.digest() == tar_hash.digest()
selected = DEST if DEST.stat().st_size < SOURCE_BYTES else SOURCE
size = selected.stat().st_size
parts = []
with selected.open('rb') as f:
    index = 0
    while True:
        data = f.read(PART_BYTES)
        if not data:
            break
        parts.append({'index': index, 'offset': index * PART_BYTES, 'bytes': len(data),
                      'sha256': hashlib.sha256(data).hexdigest()})
        index += 1
meta = {'schema': 'p29_complete_original_tar_lossless_transport_v1',
        'source_job': '32442b1b929641aaadccf28bae7d8f52',
        'original_archive': {'path': str(SOURCE), 'bytes': SOURCE_BYTES, 'sha256': SOURCE_SHA},
        'transport': {'path': str(selected), 'bytes': size, 'sha256': digest(selected)},
        'tar_bytes': tar_bytes, 'tar_sha256': tar_hash.hexdigest(),
        'same_original_tar_bytes': True, 'tar_repacked': False,
        'original_archive_unchanged': stamp(SOURCE) == before,
        'expected_members': 374,
        'expected_manifest_sha256': '9c6092358690df4615ae8f99f2383e06528f18077b25448c2a724569ac393a02',
        'compression': 'XZ/LZMA2 preset9 dict128MiB' if selected == DEST else 'original unchanged XZ',
        'part_bytes': PART_BYTES, 'parts': parts, 'first_part_in_stdout': True,
        'Lean_calls': 0, 'source_compilations': 0, 'new_formal_credit': 0}
with selected.open('rb') as f:
    first = f.read(PART_BYTES)
assert hashlib.sha256(first).hexdigest() == parts[0]['sha256']
header = 'P29_COMPLETE_TRANSPORT_META ' + json.dumps(meta, separators=(',', ':'))
payload = 'P29_COMPLETE_PART_0 ' + base64.b64encode(first).decode('ascii')
assert len((header + '\n' + payload + '\n').encode()) <= 540000
print(header, flush=True)
print(payload, flush=True)
