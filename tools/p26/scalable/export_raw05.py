#!/usr/bin/env python3
"""Read existing pinned P1 raw05 bytes and emit a transport archive.

No Lean is run; no source/object is generated or changed. This export does not
claim an independent kernel receipt for the raw owner.
"""
from pathlib import Path
import base64
import hashlib
import io
import json
import tarfile

ROOT = Path('/workspace/blue-member-build')
SHORT = 'ImbalancedChen/P2OriginalSaving19ArchiveGeometryData05'
FILES = [
    (ROOT / (SHORT + '.lean'), 'project/' + SHORT + '.lean', 531,
     'da1c03bdc971dadf1f17462a0ab80bf87164453db4a18b0834d4af047d508e78'),
    (ROOT / '.lake/build/lib/lean' / (SHORT + '.olean'), 'objects/' + SHORT + '.olean', 1069952,
     '13ea3b265dcd5c57ba961f95784e8c076c6db287aefbf0bdaf81cbfe39076f45'),
]


def main():
    members = []
    output = io.BytesIO()
    with tarfile.open(fileobj=output, mode='w:xz', preset=6) as archive:
        for path, member, size, sha in FILES:
            data = path.read_bytes()
            assert len(data) == size and hashlib.sha256(data).hexdigest() == sha
            info = tarfile.TarInfo(member)
            info.size = size
            archive.addfile(info, io.BytesIO(data))
            members.append({'original_path': str(path), 'member': member, 'bytes': size, 'sha256': sha})
        manifest = json.dumps({'members': members, 'Lean_executed': False,
                               'raw_owner_independent_kernel_receipt_claimed': False}, indent=2).encode()
        info = tarfile.TarInfo('RAW05_EXPORT_MANIFEST.json')
        info.size = len(manifest)
        archive.addfile(info, io.BytesIO(manifest))
    payload = output.getvalue()
    print(json.dumps({'archive_bytes': len(payload), 'archive_sha256': hashlib.sha256(payload).hexdigest(),
                      'members': members}), flush=True)
    print(base64.b64encode(payload).decode(), flush=True)


if __name__ == '__main__':
    main()
