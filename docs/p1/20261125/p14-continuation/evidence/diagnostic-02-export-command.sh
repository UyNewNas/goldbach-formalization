#!/usr/bin/env bash
set -euo pipefail
python3 -B - <<'PY'
from pathlib import Path
import base64, hashlib, io, json, lzma, tarfile

root = Path('/workspace/p1-complete-proof')
specs = [
    ('diagnostics/five-coordinate-barycentric.normal.log',
     '20261125-p14-continuation/barycentric/8eabdf5c9563ae73eb091242f376a5b28456f97f/normal/ImbalancedChen.P5OldFifthFiveCoordinateBarycentric/attempt-00000/normal.log',
     'e3d70131ab022f11cca58be0de8c8a6f805131a45e55ac0f29e027847c21df63'),
    ('pipelines/8eabdf5c.numeric-repaired.PIPELINE_RESULT.json',
     '20261125-p14-continuation-bootstrap/8eabdf5c9563ae73eb091242f376a5b28456f97f/numeric-repaired/PIPELINE_RESULT.json',
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
    if name == 'pipelines/8eabdf5c.numeric-repaired.PIPELINE_RESULT.json':
        report = json.loads(data)
        assert report['source_commit'] == '8eabdf5c9563ae73eb091242f376a5b28456f97f'
        assert report['accepted_owners'] == ['ImbalancedChen.P1FifthMask5NamedParent1Owner', 'ImbalancedChen.P1FifthMask6NamedParent0Owner', 'ImbalancedChen.P5OldFifthFiveCoordinateTree', 'ImbalancedChen.P5OldFifthOneCoordinateVertexChord']
        assert len(report['stages']) == 19 and report['whole_P1_4_complete'] is False
        canonical = json.dumps(report, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode()
        assert hashlib.sha256(canonical).hexdigest() == '1fd133558243a9cce609cffe98a20c5af53008715788e115b8a0941199101786'
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
out = root / '20261125-p14-continuation-export/diagnostic-read-02.tar.xz'
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
