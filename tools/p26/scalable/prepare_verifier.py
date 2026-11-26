#!/usr/bin/env python3
"""Freeze locally-authored Lean/audit sources and exact supplier pins.

This writes candidate verification inputs only. It does not run Lean, submit
cloud work, or infer independent raw-owner kernel receipts from Core imports.
"""
from pathlib import Path
import hashlib
import json
import tarfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
TRANSFER = Path('/tmp/p26-59264dd64286/transfer')
OUT = Path('/dev/shm/p26-59264dd64286/scalable-geometry-verifier-v1.tar.xz')


def fp(path):
    path = Path(path)
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def save(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    data = value if isinstance(value, str) else json.dumps(value, indent=2) + '\n'
    if path.exists():
        assert path.read_text() == data, ('Frozen registry drift', str(path))
    else:
        path.write_text(data)


def main():
    source = json.loads((HERE / 'SOURCE_MANIFEST.json').read_text())
    geometry_path = TRANSFER / 'GEOMETRY01_ACCEPTED_PINNED_CLOSURE.json'
    core_path = TRANSFER / 'ARCHIVE_CORE_PROBE.json'
    geometry = json.loads(geometry_path.read_text())
    core = json.loads(core_path.read_text())
    old = {row['module']: row for row in geometry['rows']}
    suppliers = []
    for item in source['supplier_source_registry']:
        module = item['module']
        src = fp(REPO / (module.replace('.', '/') + '.lean'))
        assert all(src[k] == item['source'][k] for k in ['bytes', 'sha256'])
        if module in old:
            found = old[module]
            assert src['sha256'] == found['source_sha256'] and src['bytes'] == found['source_bytes']
            obj = {'bytes': found['bytes'], 'sha256': found['object_sha256']}
            kernel_pinned = found['normal_kernel_accepted']
            basis = {'kind': 'reviewed_geometry01_supplier_checkpoint',
                     'source_registry': fp(geometry_path)}
        else:
            assert module.endswith(('ArchiveGeometryData05', 'ArchiveGeometryData12'))
            assert core['context']['project_sources'][module] == src['sha256']
            path = '.lake/build/lib/lean/' + module.replace('.', '/') + '.olean'
            obj = core['context']['dependency_objects_and_traces'][path]
            kernel_pinned = False
            basis = {'kind': 'P1_Core_strict_dependency_context_exact_object_usage',
                     'source_registry': fp(core_path),
                     'raw_owner_independent_kernel_receipt_not_yet_materialized': True}
        cells = [int(module[-2:])] if module.endswith(('ArchiveGeometryData05', 'ArchiveGeometryData12')) else [5, 12]
        suppliers.append({'module': module, 'cells': cells, 'source': src, 'object': obj,
                          'project_imports': item['project_imports'], 'evidence_basis': basis,
                          'independent_kernel_receipt_pinned': kernel_pinned,
                          'suppliers_must_not_be_recompiled': True})
    supplier_path = HERE / 'SUPPLIER_PINS.json'
    save(supplier_path, {'schema': 'scalable_geometry_supplier_pins_v1', 'suppliers': suppliers,
                         'supplier_count': len(suppliers),
                         'raw_owner_kernel_receipts_pending': [x['module'] for x in suppliers if not x['independent_kernel_receipt_pinned']],
                         'host_pins_are_Lean_acceptance': False})
    template = REPO / 'tools/p26/geometry01-owned-audits/P2OriginalSaving19Geometry01Shape.lean'
    audit_text = template.read_text()
    targets = []
    for row in source['owners']:
        module = row['module']
        audit = HERE / 'owned-audits' / (module.split('.')[-1] + '.lean')
        save(audit, audit_text.replace('ImbalancedChen.P2OriginalSaving19Geometry01Shape', module))
        src = REPO / row['source']['path']
        assert fp(src)['sha256'] == row['source']['sha256']
        targets.append({'module': module, 'cell': row['cell'], 'source': fp(src),
                        'audit': fp(audit), 'audit_relative_path': str(audit.relative_to(HERE))})
    verifier = {'schema': 'scalable_geometry_frozen_verifier_v1', 'driver': fp(HERE / 'verify_pilot.py'),
                'mature_helper': fp(HERE / 'Geometry01Decoding_verify.py'),
                'supplier_manifest': fp(supplier_path), 'source_manifest': fp(HERE / 'SOURCE_MANIFEST.json'),
                'owned_audit_template': fp(template), 'targets': targets, 'held_targets': [],
                'P2_6_complete': False, 'new_owner_normal_kernel_owned_accepted': False}
    save(HERE / 'ScalableGeometry_VERIFIER.json', verifier)
    for cell in [5, 12]:
        save(HERE / f'cloud_order_cell{cell:02d}.txt', ''.join(x['module'] + '\n' for x in targets if x['cell'] == cell))
    OUT.parent.mkdir(parents=True, exist_ok=True)
    assert not OUT.exists(), 'Refuse to replace a frozen transfer package'
    with tarfile.open(OUT, 'w:xz', preset=6) as tar:
        for row in targets:
            path = Path(row['source']['path'])
            tar.add(path, arcname='project/' + str(path.relative_to(REPO)))
        for path in sorted(HERE.rglob('*')):
            if path.is_file() and '__pycache__' not in path.parts:
                tar.add(path, arcname='tools/p26/scalable/' + str(path.relative_to(HERE)))
    print(json.dumps({'archive': fp(OUT), 'targets': len(targets),
                      'cell05_targets': sum(x['cell'] == 5 for x in targets),
                      'cell12_targets': sum(x['cell'] == 12 for x in targets),
                      'supplier_count': len(suppliers),
                      'raw_owner_independent_kernel_receipts_pending': 2}))


if __name__ == '__main__':
    main()
