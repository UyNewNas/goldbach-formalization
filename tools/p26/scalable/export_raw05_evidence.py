#!/usr/bin/env python3
"""Losslessly export the existing raw05 normal/kernel/owned evidence and bytes."""
from pathlib import Path
import base64
import hashlib
import io
import json
import tarfile

ROOT = Path('/workspace/p1-complete-proof/20261125-p26-archive-v4-inputs-v1/07826355aedef5a01e76c36ad304bc6b115f3c2b/ImbalancedChen.P2OriginalSaving19ArchiveGeometryData05')
BLUE = Path('/workspace/blue-member-build')
MODULE = 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData05'


def identity(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def main():
    result_path = ROOT / 'runs/attempt-00000/RESULT.json'
    result_data = result_path.read_bytes()
    assert identity(result_data) == {'bytes': 17809, 'sha256': 'fc8ef0b78bea65f0437cb6ebcc46ccb4f374aa8101ec51907a507b5903f3a959'}
    result = json.loads(result_data)
    assert result['status'] == 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS'
    assert result['accepted_owners'] == [MODULE]
    normal = json.loads((ROOT / 'normal' / MODULE / 'NORMAL_PASS.json').read_text())
    files = [(p, 'previous-p1-evidence/' + str(p.relative_to(ROOT)))
             for p in sorted(ROOT.rglob('*')) if p.is_file()]
    relative = MODULE.replace('.', '/')
    for member, actual in [('project/' + relative + '.lean', relative + '.lean'),
                           ('objects/' + relative + '.olean', '.lake/build/lib/lean/' + relative + '.olean')]:
        path = BLUE / actual
        assert identity(path.read_bytes()) == normal['source_plus_five_outputs'][actual]
        files.append((path, member))
    raw = next(row for row in result['loader_inputs'] if row['family'] == 'geometry' and row['cell'] == 5)
    raw_path = Path(raw['resolved_actual_path'])
    assert identity(raw_path.read_bytes()) == {k: raw[k] for k in ['bytes', 'sha256']}
    files.append((raw_path, 'original-input/' + raw_path.name))
    out, members = io.BytesIO(), []
    with tarfile.open(fileobj=out, mode='w:xz', preset=6) as tar:
        for path, member in files:
            data = path.read_bytes()
            info = tarfile.TarInfo(member)
            info.size = len(data)
            info.mode = 0o644
            tar.addfile(info, io.BytesIO(data))
            members.append({'member': member, 'original_path': str(path), **identity(data)})
        manifest = json.dumps({'schema': 'raw05_recovered_evidence_export_v1',
                               'members': members, 'source_commit': result['source_commit'],
                               'Lean_executed_for_export': False,
                               'historical_status': result['status']}, indent=2).encode()
        info = tarfile.TarInfo('RECOVERED_EXPORT_MANIFEST.json')
        info.size = len(manifest)
        info.mode = 0o644
        tar.addfile(info, io.BytesIO(manifest))
    data = out.getvalue()
    print(json.dumps({'archive': identity(data), 'listed_members': len(members),
                      'total_members': len(members) + 1}), flush=True)
    print(base64.b64encode(data).decode(), flush=True)


if __name__ == '__main__':
    main()
