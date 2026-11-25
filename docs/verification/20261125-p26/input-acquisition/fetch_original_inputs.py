"""Read exact original numerical witnesses from the public release by HTTP ranges.
No certificate truth is inferred. Every selected member must match the previously
bound P1 input bytes/SHA; already matching local inputs are never overwritten.
"""
from pathlib import Path
from urllib.request import Request, urlopen
from collections import OrderedDict
import hashlib, io, json, time, zipfile

REPO = Path('/workspace/p26-source-closure')
OUT = Path('/workspace/p26-original-inputs')
URL = 'https://github.com/UyNewNas/chen-imbalanced-semiprimes/releases/download/v2026.10.10/chen-numerical-evidence-20261010.zip'
SIZE = 323605374
PUBLISHED_FULL_SHA = '8f1bdf63e1aa972256b2422f824f3d177617b31bf41b6a2b8cf29b0562647ad1'
SCALE = REPO / 'docs/verification/20261125-p26/ORIGINAL_INPUT_SCALE.json'
assert hashlib.sha256(SCALE.read_bytes()).hexdigest() == '3e022a419c35152589c2c3fb26cb0fe5839c79a348277b0643174b4f078f3954'

class RangeFile(io.RawIOBase):
    def __init__(self):
        super().__init__(); self.position = 0; self.cache = OrderedDict()
        self.block_size = 512 * 1024; self.requests = []; self.downloaded = 0
        tail_path = Path('/workspace/p26-evidence-zip-tail.bin')
        self.tail = tail_path.read_bytes() if tail_path.exists() else b''
        assert not self.tail or len(self.tail) == 65536
    def seekable(self): return True
    def readable(self): return True
    def tell(self): return self.position
    def seek(self, offset, whence=io.SEEK_SET):
        self.position = offset if whence == io.SEEK_SET else (self.position + offset if whence == io.SEEK_CUR else SIZE + offset)
        if not 0 <= self.position <= SIZE: raise ValueError('seek outside archive')
        return self.position
    def block(self, index):
        if index in self.cache:
            self.cache.move_to_end(index); return self.cache[index]
        start = index * self.block_size; end = min(SIZE, start + self.block_size) - 1
        request = Request(URL, headers={'Range': f'bytes={start}-{end}', 'Accept-Encoding': 'identity'})
        before = time.monotonic()
        with urlopen(request, timeout=45) as response:
            expected = f'bytes {start}-{end}/{SIZE}'
            assert response.status == 206 and response.headers.get('Content-Range') == expected, (response.status, response.headers.get('Content-Range'), expected)
            data = response.read(end-start+2)
            assert len(data) == end-start+1
        self.requests.append({'start': start, 'end': end, 'bytes': len(data), 'seconds': time.monotonic()-before})
        self.downloaded += len(data); self.cache[index] = data
        if len(self.cache) > 32: self.cache.popitem(last=False)
        return data
    def read(self, size=-1):
        if size is None or size < 0: size = SIZE - self.position
        size = min(size, SIZE-self.position)
        if self.tail and self.position >= SIZE-len(self.tail):
            data = self.tail[self.position-(SIZE-len(self.tail)):self.position-(SIZE-len(self.tail))+size]
            self.position += len(data); return data
        pieces = []
        while size:
            block_index, offset = divmod(self.position, self.block_size)
            block = self.block(block_index); count = min(size, len(block)-offset)
            assert count > 0; pieces.append(block[offset:offset+count]); self.position += count; size -= count
        return b''.join(pieces)

OUT.mkdir(exist_ok=True)
specs = json.loads(SCALE.read_bytes())['all_inputs']
specs.sort(key=lambda row: (row['cell'] != 1, row['cell'], row['family']))
stream = RangeFile(); acquired = []
report_path = OUT / 'PUBLIC_INPUT_ACQUISITION.json'
def save_report(complete=False):
    report = {'source_url': URL, 'release_asset_id': 626620833, 'archive_bytes_from_release_metadata': SIZE,
              'published_full_archive_sha256': PUBLISHED_FULL_SHA, 'full_archive_hash_verified': False,
              'method': 'selected ZIP members over verified HTTP byte ranges',
              'expected_input_manifest': str(SCALE), 'expected_input_manifest_sha256': hashlib.sha256(SCALE.read_bytes()).hexdigest(),
              'matching_inputs': acquired, 'all26_original_input_bytes_match': complete,
              'network_bytes_downloaded_this_run': stream.downloaded, 'range_requests': stream.requests,
              'existing_originals_overwritten': False, 'Lean_or_numeric_certificate_executed': False}
    report_path.write_text(json.dumps(report, indent=2)+'\n')
    return report
with zipfile.ZipFile(stream) as archive:
    names = archive.namelist()
    for spec in specs:
        name = Path(spec['loader_absolute_path']).name; target = OUT/name
        row = {'cell': spec['cell'], 'family': spec['family'], 'local_path': str(target), 'bytes': spec['bytes'], 'sha256': spec['sha256']}
        if target.exists():
            data = target.read_bytes(); assert len(data) == spec['bytes'] and hashlib.sha256(data).hexdigest() == spec['sha256'], name
            row['source'] = 'unchanged already-bound local input'; row['release_member_read'] = False
        else:
            matches = [path for path in names if Path(path).name == name]
            assert len(matches) == 1, (name, len(matches))
            info = archive.getinfo(matches[0]); assert info.file_size == spec['bytes'], (name, info.file_size, spec['bytes'])
            data = archive.read(info); assert len(data) == spec['bytes'] and hashlib.sha256(data).hexdigest() == spec['sha256'], name
            with target.open('xb') as output: output.write(data)
            row.update(source='public release member', release_member_read=True, zip_member=info.filename, zip_crc32=info.CRC)
        acquired.append(row); save_report(); print('INPUT_MATCH', json.dumps(row), flush=True)
assert len(acquired) == 26
report = save_report(True)
print('ALL_INPUT_BYTES_MATCH', json.dumps({'inputs': len(acquired), 'raw_bytes': sum(r['bytes'] for r in acquired), 'downloaded_range_bytes': stream.downloaded, 'report': str(report_path)}), flush=True)
