#!/usr/bin/env python3
"""Export the completed receipt-only resume once, without running proof work."""
from pathlib import Path
import base64
import hashlib
import io
import json
import lzma
import tarfile

root = Path('/workspace/p1-complete-proof/20261128-p14-signed-owned-postprocess-resume')
result_path = root / 'run/SIGNED_RECEIPT_RESUME_RESULT.json'
result_raw = result_path.read_bytes()
assert len(result_raw) == 15690
assert hashlib.sha256(result_raw).hexdigest() == '720e192c3e175bbe35c01600d191dc476a2027c26cd48051deb8d48ae30b4e5b'
result = json.loads(result_raw)
assert result['source_commit'] == 'e84ff9cbe0fa44efa1817633e8c6c0a08dfff120'
assert result['status'] == 'PASS_RESUMED_POSTPROCESS_EXISTING_AUDIT_LEGACY_NORMAL_KERNEL_COMPLETE_OWNED'
assert result['accepted_owners_by_this_independent_postprocess'] == ['ImbalancedChen.P5OriginalSignedMidpoint']
assert all(result[name] == 0 for name in ('new_normal_invocations', 'new_kernel_invocations',
    'new_full_owned_audit_invocations', 'new_guard_events'))
assert result['whole_P1_4_complete'] is False
assert root.is_dir() and all(not p.is_symlink() for p in (root, *root.parents))
files = []
total = 0
for path in sorted(root.rglob('*')):
    assert not path.is_symlink(), str(path)
    if path.is_dir():
        continue
    assert path.is_file() and path.stat().st_size <= 2 * 1024 * 1024, str(path)
    data = path.read_bytes()
    total += len(data)
    assert total <= 8 * 1024 * 1024
    files.append(({'path': 'signed_resume/' + path.relative_to(root).as_posix(),
        'original_path': str(path), 'bytes': len(data),
        'sha256': hashlib.sha256(data).hexdigest()}, data))
for before, after in [('GIT_BEFORE.json', 'GIT_AFTER.json'), ('LIVE_BEFORE.json', 'LIVE_AFTER.json'),
                      ('OLD_WAIT_BEFORE.json', 'OLD_WAIT_AFTER.json')]:
    assert (root / 'run' / before).read_bytes() == (root / 'run' / after).read_bytes()
runtime = json.loads((root / 'run/POSTPROCESS_RUNTIME_EVIDENCE.json').read_bytes())
assert runtime['new_guard_events'] == 0 and runtime['outer_lock_used'] is False
assert runtime['postprocess_before_byte_offset'] == runtime['postprocess_after_byte_offset']
records = json.loads((root / 'run/OWNED_EXPORTS.json').read_bytes())
assert len(records) == result['owned_total']
assert sum(not row['is_private'] for row in records) == result['public_total']
assert sum(row['is_private'] for row in records) == result['private_total']
assert json.loads((root / 'run/PUBLIC_EXPORTS.json').read_bytes()) == [r for r in records if not r['is_private']]
manifest = {'schema': 'p14_signed_resume_original_receipt_export_v1', 'original_root': str(root),
    'original_result_sha256': hashlib.sha256(result_raw).hexdigest(),
    'files': [r for r, _ in files], 'omitted_files': [],
    'new_proof_invocations': 0, 'whole_P1_4_complete': False}
raw = io.BytesIO()
with tarfile.open(fileobj=raw, mode='w') as archive:
    for row, data in files:
        info = tarfile.TarInfo(row['path'])
        info.size, info.mode = len(data), 0o644
        archive.addfile(info, io.BytesIO(data))
    data = (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode()
    info = tarfile.TarInfo('EXPORT_MANIFEST.json')
    info.size, info.mode = len(data), 0o644
    archive.addfile(info, io.BytesIO(data))
for row, data in files:
    assert Path(row['original_path']).read_bytes() == data
archive_bytes = lzma.compress(raw.getvalue(), preset=9)
assert len(archive_bytes) <= 4 * 1024 * 1024
output = root.parent / '20261128-p14-signed-owned-postprocess-resume-export.tar.xz'
with output.open('xb') as stream:
    stream.write(archive_bytes)
print(json.dumps({'schema': 'p14_signed_resume_original_receipt_transport_v1', 'path': str(output),
    'bytes': len(archive_bytes), 'sha256': hashlib.sha256(archive_bytes).hexdigest(),
    'file_count': len(files), 'uncompressed_bytes': total, 'omitted_count': 0}), flush=True)
print(base64.b64encode(archive_bytes).decode(), flush=True)
