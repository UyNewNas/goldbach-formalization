import argparse
import hashlib
import json
import struct
import subprocess
import tempfile
import zlib
from pathlib import Path

URL = 'https://github.com/UyNewNas/chen-imbalanced-semiprimes/releases/download/v2026.10.10/chen-numerical-evidence-20261010.zip'
parser = argparse.ArgumentParser(description='Recover recorded ZIP members and verify their individual identities.')
parser.add_argument('--project-dir', required=True, type=Path)
parser.add_argument('--receipts', required=True, type=Path)
parser.add_argument('--only', action='append', default=[])
args = parser.parse_args()
records = json.loads(args.receipts.read_text())
if args.only:
    requested = set(args.only)
    records = [r for r in records if r['name'] in requested]
    if {r['name'] for r in records} != requested:
        raise ValueError('unknown requested fixture')
if not records:
    raise ValueError('empty fixture selection')
if not args.project_dir.is_dir():
    raise ValueError('project directory must already exist')
dest = args.project_dir / '../tmp/publication-20261010/verification-renewal-v2/_runs/full-final'
dest.mkdir(parents=True, exist_ok=True)
results = []
for record in records:
    name = record['name']
    if Path(name).name != name or not record['member'].endswith('/' + name):
        raise ValueError('invalid fixture name')
    target = dest / name
    if target.exists():
        raw = target.read_bytes()
        if len(raw) != record['bytes'] or hashlib.sha256(raw).hexdigest() != record['sha256']:
            raise ValueError('existing fixture has different bytes: ' + name)
        results.append({'name': name, 'status': 'verified-existing'})
        continue
    start = record['local_header_offset']
    length = record['compressed'] + 4096
    with tempfile.TemporaryDirectory() as tmp:
        chunk = Path(tmp) / 'member.range'
        cmd = ['curl', '-sSL', '--fail', '--max-time', '40', '--max-filesize', str(length),
               '--range', f'{start}-{start + length - 1}', '-o', str(chunk),
               '--write-out', '%{http_code} %{size_download}', URL]
        process = subprocess.run(cmd, capture_output=True, text=True, check=True)
        if not process.stdout.startswith('206 '):
            raise ValueError('server did not return a partial response')
        raw = chunk.read_bytes()
    header = struct.unpack_from('<4s5H3I2H', raw)
    if header[0] != b'PK\x03\x04' or header[3] != 8 or header[2] & 1:
        raise ValueError('unexpected local ZIP header: ' + name)
    name_len, extra_len = header[9:11]
    if raw[30:30 + name_len].decode('utf-8') != record['member']:
        raise ValueError('local ZIP name mismatch: ' + name)
    start_data = 30 + name_len + extra_len
    compressed = raw[start_data:start_data + record['compressed']]
    if len(compressed) != record['compressed']:
        raise ValueError('truncated ZIP member: ' + name)
    inflater = zlib.decompressobj(-15)
    data = inflater.decompress(compressed, record['bytes'] + 1)
    if not inflater.eof or inflater.unused_data or len(data) != record['bytes']:
        raise ValueError('invalid expanded size: ' + name)
    if hashlib.sha256(data).hexdigest() != record['sha256'] or format(zlib.crc32(data) & 0xffffffff, '08x') != record['crc32']:
        raise ValueError('fixture identity mismatch: ' + name)
    with target.open('xb') as output:
        output.write(data)
    results.append({'name': name, 'status': 'recovered-verified'})
print(json.dumps({'count': len(results), 'results': results}))
