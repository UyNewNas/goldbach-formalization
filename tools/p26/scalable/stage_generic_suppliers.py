#!/usr/bin/env python3
"""Retrieve eight exact published generic suppliers into isolated P2 staging."""
from pathlib import Path
import hashlib
import io
import json
import subprocess
import tarfile

STAGE = Path('/workspace/p26-continuation-59264dd64286/scalable-geometry')
COMMIT = 'e609d83002f4814995d888105768e8a4a284d321'
ORIGIN = 'https://github.com/UyNewNas/goldbach-formalization.git'
ARCHIVE_PATH = 'docs/verification/20261126-p26/geometry01-decoded-shape/suppliers.tar.xz'
ARCHIVE_SHA = 'c5717cac83aba2f0ee10c8def1cb604ff101717258d28a8e404fbad915d9078d'


def main():
    repo = STAGE / 'supplier-fetch.git'
    if not repo.exists():
        subprocess.run(['git', 'init', '--bare', str(repo)], check=True)
        subprocess.run(['git', '--git-dir=' + str(repo), 'remote', 'add', 'origin', ORIGIN], check=True)
    got = subprocess.check_output(['git', '--git-dir=' + str(repo), 'remote', 'get-url', 'origin'], text=True).strip()
    assert got == ORIGIN
    subprocess.run(['git', '--git-dir=' + str(repo), 'fetch', '--filter=blob:none', '--depth=1', 'origin', COMMIT], check=True)
    data = subprocess.check_output(['git', '--git-dir=' + str(repo), 'show', COMMIT + ':' + ARCHIVE_PATH])
    assert len(data) == 13655836 and hashlib.sha256(data).hexdigest() == ARCHIVE_SHA
    pins = json.loads((STAGE / 'tools/p26/scalable/SUPPLIER_PINS.json').read_text())
    wanted = [r for r in pins['suppliers'] if r['cells'] == [5, 12]]
    assert len(wanted) == 8
    installed = []
    with tarfile.open(fileobj=io.BytesIO(data), mode='r:xz') as archive:
        for row in wanted:
            rel = row['module'].replace('.', '/')
            for kind, suffix, directory in [('source', '.lean', 'project'), ('object', '.olean', 'objects')]:
                member = directory + '/' + rel + suffix
                blob = archive.extractfile(member).read()
                assert len(blob) == row[kind]['bytes'] and hashlib.sha256(blob).hexdigest() == row[kind]['sha256']
                dest = STAGE / 'suppliers' / member
                dest.parent.mkdir(parents=True, exist_ok=True)
                if dest.exists():
                    assert dest.read_bytes() == blob
                else:
                    dest.write_bytes(blob)
                installed.append({'module': row['module'], 'kind': kind,
                                  'bytes': len(blob), 'sha256': row[kind]['sha256']})
    receipt = {'git_commit': COMMIT, 'archive_path': ARCHIVE_PATH, 'archive_sha256': ARCHIVE_SHA,
               'generic_suppliers': len(wanted), 'installed': installed, 'Lean_executed': False}
    target = STAGE / 'suppliers/GENERIC_STAGING.json'
    if target.exists():
        assert json.loads(target.read_text()) == receipt
    else:
        target.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'generic_suppliers_installed': len(wanted), 'installed_files': len(installed),
                      'receipt': str(target), 'Lean_executed': False}), flush=True)


if __name__ == '__main__':
    main()
