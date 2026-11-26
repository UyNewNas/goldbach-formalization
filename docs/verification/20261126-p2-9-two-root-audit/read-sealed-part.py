#!/usr/bin/env python3
"""Read one fixed range of the completed archive; no audit or source reread."""
import base64
import hashlib
import json
from pathlib import Path
import stat


def identity(path):
    s = path.stat()
    if not stat.S_ISREG(s.st_mode):
        raise ValueError('archive is not regular')
    return {'requested_path': str(path), 'resolved_path': str(path.resolve()),
            'st_dev': s.st_dev, 'st_ino': s.st_ino, 'st_size': s.st_size,
            'st_mtime_ns': s.st_mtime_ns, 'st_ctime_ns': s.st_ctime_ns,
            'st_mode': s.st_mode}


def main():
    path = Path(CONFIG['archive'])
    part = CONFIG['part']
    if str(path) != '/workspace/p29-polyhedral-affine-7981839-archive/complete.tar.xz':
        raise ValueError('wrong archive')
    if identity(path) != CONFIG['archive_identity']:
        raise ValueError('archive identity changed since original pack')
    if not (0 <= part['offset'] < CONFIG['archive_bytes'] and
            0 < part['bytes'] <= 1200000 and
            part['offset'] + part['bytes'] <= CONFIG['archive_bytes']):
        raise ValueError('invalid exact range')
    with path.open('rb') as stream:
        stream.seek(part['offset'])
        raw = stream.read(part['bytes'])
    if len(raw) != part['bytes'] or hashlib.sha256(raw).hexdigest() != part['sha256']:
        raise ValueError('original archive part changed')
    if identity(path) != CONFIG['archive_identity']:
        raise ValueError('archive identity changed during range read')
    print('P29_TWO_ROOT_PART_META ' + json.dumps(CONFIG, sort_keys=True), flush=True)
    print('P29_TWO_ROOT_PART_BASE64 ' + base64.b64encode(raw).decode('ascii'), flush=True)


if __name__ == '__main__':
    main()
