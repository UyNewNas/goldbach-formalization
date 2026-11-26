#!/usr/bin/env python3
"""Pin and hardlink nine already accepted P1 suppliers; never invoke Lean."""
from pathlib import Path
import hashlib
import json
import os
import shutil


ROOT = Path('/workspace/p26-continuation-59264dd64286')
STAGE = ROOT / 'scalable-geometry'


def fingerprint(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def identical(got, expected):
    return all(got[k] == expected[k] for k in ('bytes', 'sha256'))


def main():
    manifest = STAGE / 'tools/p26/scalable/SUPPLIER_PINS.json'
    suppliers = [row for row in json.loads(manifest.read_text())['suppliers'] if 5 in row['cells']]
    assert len(suppliers) == 9
    assert all(row['independent_kernel_receipt_pinned'] for row in suppliers)
    entries = []
    for row in suppliers:
        module = row['module']
        rel = Path(module.replace('.', '/'))
        raw = module.endswith('ArchiveGeometryData05')
        for kind, suffix, destination_directory in [('source', '.lean', 'project'), ('object', '.olean', 'objects')]:
            if raw:
                directory = 'sources' if kind == 'source' else 'objects'
                source = ROOT / 'cell00/archive-extra' / directory / rel.with_suffix(suffix)
            else:
                source = ROOT / 'geometry01' / destination_directory / rel.with_suffix(suffix)
            assert source.is_file(), ('Missing frozen P1 supplier', str(source))
            before = fingerprint(source)
            assert identical(before, row[kind]), ('Supplier mismatch', str(source), before, row[kind])
            destination = STAGE / 'suppliers' / destination_directory / rel.with_suffix(suffix)
            destination.parent.mkdir(parents=True, exist_ok=True)
            method = 'existing_identical'
            if destination.exists():
                assert identical(fingerprint(destination), row[kind]), ('Refusing overwrite', str(destination))
            else:
                os.link(source, destination)
                method = 'hardlink'
            installed = fingerprint(destination)
            assert identical(installed, row[kind])
            assert source.stat().st_dev == destination.stat().st_dev
            assert source.stat().st_ino == destination.stat().st_ino
            entries.append({'module': module, 'kind': kind, 'source': before, 'installed': installed, 'method': method})
    evidence = {'schema': 'cell05_p1_hardlink_suppliers_v1', 'manifest': fingerprint(manifest),
                'modules': len(suppliers), 'entries': entries, 'suppliers_recompiled': False,
                'all_supplier_independent_kernel_receipts_pinned': True,
                'disk_free_bytes': shutil.disk_usage(STAGE).free}
    output = STAGE / 'suppliers/P1_SUPPLIER_STAGE.json'
    data = (json.dumps(evidence, ensure_ascii=False, indent=2) + '\n').encode()
    if output.exists():
        previous = json.loads(output.read_text())
        assert previous['manifest'] == evidence['manifest']
        assert previous['modules'] == evidence['modules']
        print(json.dumps({'already_staged': True, 'receipt': fingerprint(output)}))
    else:
        with output.open('xb') as stream:
            stream.write(data)
        print(json.dumps({'hardlinked_accepted_supplier_modules': len(suppliers), 'receipt': fingerprint(output),
                          'disk_free_bytes': evidence['disk_free_bytes']}))


if __name__ == '__main__':
    main()
