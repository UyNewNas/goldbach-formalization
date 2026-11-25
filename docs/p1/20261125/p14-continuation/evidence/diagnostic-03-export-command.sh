#!/usr/bin/env bash
set -euo pipefail
python3 -B - <<'PY'
from pathlib import Path
import base64, hashlib, io, json, lzma, tarfile

root = Path('/workspace/p1-complete-proof')
specs = [
    ('diagnostics/957c7c77.owner-b13-error.normal.log',
     '20261125-p14-continuation/owner-b13-error/957c7c773bef05a6271fb504c06d967d67ce2908/normal/ImbalancedChen.P1OriginalFifthActualB13IntegralError/attempt-00000/normal.log',
     '7300eac3e3a89dfe802208b68f0b66b899b9312bd5fd245fccda7c705db25d83'),
    ('pipelines/957c7c77.PIPELINE_RESULT.json',
     '20261125-p14-continuation-bootstrap/957c7c773bef05a6271fb504c06d967d67ce2908/PIPELINE_RESULT.json',
     None),
    ('diagnostics/b6ba72c2.typed-key-uniqueness-certificate-syntax-retry.normal.log',
     '20261125-p14-continuation/typed-key-uniqueness-certificate-syntax-retry/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a/normal/ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCertificate/attempt-00000/normal.log',
     '04420a0add4a41d344cdb5ac059b767061e2d6e2daaa9b33db4a1e4cef311c2c'),
    ('pipelines/b6ba72c2.typed-key-uniqueness-syntax-retry.PIPELINE_RESULT.json',
     '20261125-p14-continuation-bootstrap/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a/typed-key-uniqueness-syntax-retry/PIPELINE_RESULT.json',
     None),
    ('diagnostics/b6ba72c2.barycentric-expression-retry.normal.log',
     '20261125-p14-continuation/barycentric-expression-retry/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a/normal/ImbalancedChen.P5OldFifthFiveCoordinateBarycentric/attempt-00000/normal.log',
     '0d8d75c6767cb4659bc09cce10c5547edfb6d62e244fefa7044e488b148d07e6'),
    ('pipelines/b6ba72c2.numeric-second-repairs.PIPELINE_RESULT.json',
     '20261125-p14-continuation-bootstrap/b6ba72c275b747321f6ffbf17d18ff8e19f98a0a/numeric-second-repairs/PIPELINE_RESULT.json',
     None),
]
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
    if name == 'pipelines/957c7c77.PIPELINE_RESULT.json':
        report = json.loads(data)
        assert report['source_commit'] == '957c7c773bef05a6271fb504c06d967d67ce2908'
        assert report['accepted_owners'] == ['ImbalancedChen.P1OriginalFifthActualCrossingSections']
        assert len(report['stages']) == 8 and report['whole_P1_4_complete'] is False
        canonical = json.dumps(report, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode()
        assert hashlib.sha256(canonical).hexdigest() == '6d267568730b7d7049213dc6e48f65f4b214429b516f041dec6ca44b41e7b5d2'
    if name == 'pipelines/b6ba72c2.typed-key-uniqueness-syntax-retry.PIPELINE_RESULT.json':
        report = json.loads(data)
        assert report['source_commit'] == 'b6ba72c275b747321f6ffbf17d18ff8e19f98a0a'
        assert report['accepted_owners'] == []
        assert len(report['stages']) == 1 and report['whole_P1_4_complete'] is False
        canonical = json.dumps(report, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode()
        assert hashlib.sha256(canonical).hexdigest() == '68571a20082dd79dd66e6a8f1894dbec979753800d782169042cf16562ff0b74'
    if name == 'pipelines/b6ba72c2.numeric-second-repairs.PIPELINE_RESULT.json':
        report = json.loads(data)
        assert report['source_commit'] == 'b6ba72c275b747321f6ffbf17d18ff8e19f98a0a'
        assert report['accepted_owners'] == ['ImbalancedChen.P1FifthNamedParentActualIntegral']
        assert len(report['stages']) == 15 and report['whole_P1_4_complete'] is False
        canonical = json.dumps(report, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode()
        assert hashlib.sha256(canonical).hexdigest() == '9b01817ec89ac7b737550f171e4251bccc6d7cf20f741e3de4b6bf3ef6827735'
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
out = root / '20261125-p14-continuation-export/diagnostic-read-03.tar.xz'
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
