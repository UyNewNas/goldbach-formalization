#!/usr/bin/env python3
"""Locate exact already-accepted Archive suppliers; never execute a proof."""
from pathlib import Path
import hashlib
import json
import os
import sys


def fingerprint(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': digest.hexdigest()}


def main():
    request = json.loads(Path(sys.argv[1]).read_text())
    wanted = {}
    for row in request['suppliers']:
        for kind in ('source', 'object'):
            suffix = '.lean' if kind == 'source' else '.olean'
            wanted.setdefault(row['module'].split('.')[-1] + suffix, []).append((row, kind))
    exact, other = {}, {}
    for parent, dirs, files in os.walk('/workspace', followlinks=False):
        dirs[:] = [name for name in dirs if name != '.git']
        for name in wanted.keys() & set(files):
            path = Path(parent) / name
            if not path.is_file() or path.is_symlink():
                continue
            pin = fingerprint(path)
            for row, kind in wanted[name]:
                key = (row['module'], kind)
                expected = row[kind]
                matches = all(pin[field] == expected[field] for field in ('bytes', 'sha256'))
                (exact if matches else other).setdefault(key, []).append(pin)
    result = []
    for row in request['suppliers']:
        result.append({'module': row['module'], 'expected': row,
                       'exact': {kind: exact.get((row['module'], kind), []) for kind in ('source', 'object')},
                       'different_bytes': {kind: other.get((row['module'], kind), []) for kind in ('source', 'object')}})
    print(json.dumps({'schema': 'p26_archive_extra_supplier_inventory_v1',
                      'suppliers': result, 'count': len(result),
                      'proof_commands': 0, 'evidence_bodies_opened': False}, indent=2))


if __name__ == '__main__':
    main()
