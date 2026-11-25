#!/usr/bin/env bash
set -euo pipefail
python3 -B - <<'PY'
from pathlib import Path
import base64, hashlib, io, json, lzma, tarfile

root = Path('/workspace/p1-complete-proof')
specs = [('diagnostics/982744d2.barycentric-lambda-bool-retry.normal.log', '20261125-p14-continuation/barycentric-lambda-bool-retry/982744d2574278aca8cf4d6ef4de6e59c0c67f4f/normal/ImbalancedChen.P5OldFifthFiveCoordinateBarycentric/attempt-00000/normal.log', '9dcb057620c942366b6c44265a613cf2847abfde38c6befd6a353ec2c7d6138e'), ('pipelines/982744d2.barycentric-lambda-bool-and-consumers.PIPELINE_RESULT.json', '20261125-p14-continuation-bootstrap/982744d2574278aca8cf4d6ef4de6e59c0c67f4f/barycentric-lambda-bool-and-consumers/PIPELINE_RESULT.json', None), ('diagnostics/bb377de8.typed-key-uniqueness-sort-rewrite-retry.normal.log', '20261125-p14-continuation/typed-key-uniqueness-sort-rewrite-retry/bb377de86aa1e92f461c3d01471010cb0791dad5/normal/ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCertificate/attempt-00000/normal.log', '129b91e6ef76737fdfcb0df38f353906b21cdc7e68e48a183b9e9368b930cf3e'), ('pipelines/bb377de8.typed-key-uniqueness-sort-rewrite-retry.PIPELINE_RESULT.json', '20261125-p14-continuation-bootstrap/bb377de86aa1e92f461c3d01471010cb0791dad5/typed-key-uniqueness-sort-rewrite-retry/PIPELINE_RESULT.json', None)]
pipeline_pins = {'pipelines/982744d2.barycentric-lambda-bool-and-consumers.PIPELINE_RESULT.json': {'source_commit': '982744d2574278aca8cf4d6ef4de6e59c0c67f4f', 'accepted_owners': [], 'stage_count': 14, 'canonical_json_sha256': '631c4218f7e9c736bbe90f9465e41f0373471d301cf209a79180e422486205b9'}, 'pipelines/bb377de8.typed-key-uniqueness-sort-rewrite-retry.PIPELINE_RESULT.json': {'source_commit': 'bb377de86aa1e92f461c3d01471010cb0791dad5', 'accepted_owners': [], 'stage_count': 1, 'canonical_json_sha256': 'abaca430e6b14b0360baace3f11035c353534bcee3bf9d6bb1ea163a314b0802'}}
payloads = {}
rows = []
for name, rel, expected in specs:
    path = root / rel
    assert path.is_file() and all(not p.is_symlink() for p in (path, *path.parents))
    data = path.read_bytes()
    assert len(data) <= 4 * 1024 * 1024
    digest = hashlib.sha256(data).hexdigest()
    if expected is not None:
        assert digest == expected, name
    if name in pipeline_pins:
        pin = pipeline_pins[name]
        report = json.loads(data)
        assert report['source_commit'] == pin['source_commit']
        assert report['accepted_owners'] == pin['accepted_owners']
        assert len(report['stages']) == pin['stage_count'] and report['whole_P1_4_complete'] is False
        canonical = json.dumps(report, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode()
        assert hashlib.sha256(canonical).hexdigest() == pin['canonical_json_sha256']
    payloads[name] = data
    rows.append({'path': name, 'source_path': str(path), 'bytes': len(data),
                 'sha256': digest, 'expected_sha256': expected})
manifest = {'schema': 'p14_existing_file_diagnostic_export_v1',
            'purpose': 'READ_ONLY_EXISTING_FILES_NOT_NEW_PROOF_ACCEPTANCE',
            'files': rows, 'file_count': len(rows), 'omitted_files': [],
            'new_compilation_or_scan_performed': False,
            'acceptance_claimed': False, 'whole_P1_4_complete': False}
payloads['EXPORT_MANIFEST.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
raw = io.BytesIO()
with tarfile.open(fileobj=raw, mode='w', format=tarfile.PAX_FORMAT) as tar:
    for name in sorted(payloads):
        data = payloads[name]
        info = tarfile.TarInfo(name)
        info.size = len(data)
        info.mode = 0o644
        info.mtime = 0
        info.uid = info.gid = 0
        info.uname = info.gname = ''
        tar.addfile(info, io.BytesIO(data))
for row in rows:
    assert hashlib.sha256(Path(row['source_path']).read_bytes()).hexdigest() == row['sha256']
blob = lzma.compress(raw.getvalue(), preset=6)
out = root / '20261125-p14-continuation-export/diagnostic-read-04.tar.xz'
out.parent.mkdir(parents=True, exist_ok=True)
with out.open('xb') as f:
    f.write(blob)
print(json.dumps({'status': 'EXISTING_FILE_EXPORT_NOT_ACCEPTANCE', 'path': str(out),
                  'bytes': len(blob), 'sha256': hashlib.sha256(blob).hexdigest(),
                  'manifest_sha256': hashlib.sha256(payloads['EXPORT_MANIFEST.json']).hexdigest(),
                  'file_count': len(rows)}), flush=True)
print('P14_DIAGNOSTIC_BASE64_BEGIN', flush=True)
print(base64.b64encode(blob).decode(), flush=True)
print('P14_DIAGNOSTIC_BASE64_END', flush=True)
PY
