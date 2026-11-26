#!/usr/bin/env python3
"""Export a successfully verified six-owner cell05 pilot with exact source/objects."""
from pathlib import Path
import argparse
import hashlib
import io
import json
import tarfile

DEFAULT_STAGE = Path('/workspace/p26-continuation-59264dd64286/scalable-geometry')


def pin(path):
    data = Path(path).read_bytes()
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def same(path, expected):
    return pin(path) == {k: expected[k] for k in ['bytes', 'sha256']}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--stage', type=Path, default=DEFAULT_STAGE)
    args = ap.parse_args()
    stage = args.stage.resolve()
    successes = sorted((stage / 'verification').glob('*/SUCCESS.json'))
    candidates = [(path, json.loads(path.read_text())) for path in successes]
    candidates = [(path, data) for path, data in candidates if data.get('phase') == 'cell05']
    assert candidates, 'No successful cell05 verification exists'
    success_path, success = candidates[-1]
    assert success['status'] == 'succeeded' and success['accepted_targets'] == 6
    assert success['frozen_inputs_unchanged'] and not success['P2_6_complete']
    verifier_path = stage / 'tools/p26/scalable/ScalableGeometry_VERIFIER.json'
    verifier = json.loads(verifier_path.read_text())
    targets = [row for row in verifier['targets'] if row['cell'] == 5]
    assert len(targets) == 6
    target_names = {row['module'] for row in targets}
    assert same(verifier_path, success['verifier_manifest'])
    assert same(stage / 'tools/p26/scalable/SUPPLIER_PINS.json', success['supplier_manifest'])
    checked, owned_count, modes = [], 0, {'normal': 0, 'kernel': 0, 'owned': 0}
    for record in success['records']:
        identity = record.get('receipt') or record['reused_successful_receipt']
        path = Path(identity['path'])
        assert path.is_relative_to(stage) and same(path, identity)
        step = json.loads(path.read_text())
        assert step['status'] == 'succeeded' and step['exit_code'] == 0
        assert step['module'] in target_names
        for field in ['source', 'object', 'log']:
            assert same(step[field]['path'], step[field]), (step['module'], field)
        modes[step['mode']] += 1
        row = {'module': step['module'], 'mode': step['mode'], 'receipt': str(path.relative_to(stage)),
               **pin(path), 'elapsed_seconds': step['elapsed_seconds'],
               'peak_rss_bytes': step['peak_rss_bytes']}
        if step['mode'] == 'owned':
            assert same(step['audit_source']['path'], step['audit_source'])
            assert same(step['owned_declarations']['path'], step['owned_declarations'])
            owned = json.loads(Path(step['owned_declarations']['path']).read_text())
            assert owned['module'] == step['module']
            assert sorted(owned['inventory']['environment']) == sorted(owned['inventory']['serialized'])
            assert sorted(d['name'] for d in owned['declarations']) == sorted(owned['inventory']['environment'])
            assert len(owned['declarations']) == step['owned_declaration_count'] == owned['owned_declaration_count']
            assert set(owned['axioms_union']) <= {'propext', 'Classical.choice', 'Quot.sound'}
            row['owned_declaration_count'] = owned['owned_declaration_count']
            row['axioms_union'] = owned['axioms_union']
            owned_count += owned['owned_declaration_count']
        checked.append(row)
    assert modes == {'normal': 6, 'kernel': 6, 'owned': 6}
    selected = []
    for directory in ['project', 'objects', 'tools', 'verification']:
        selected.extend(path for path in (stage / directory).rglob('*')
                        if path.is_file() and '__pycache__' not in path.parts)
    selected.extend(path for path in (stage / 'suppliers').glob('*.json') if path.is_file())
    assert len(selected) == len(set(selected))
    members = [{'member': str(path.relative_to(stage)), **pin(path)} for path in sorted(selected)]
    manifest = {'schema': 'cell05_scalable_accepted_export_v1', 'status': 'SIX_NEW_OWNERS_NORMAL_KERNEL_FULL_OWNED_PASSED',
                'members': members, 'success_member': str(success_path.relative_to(stage)),
                'verified_steps': checked, 'step_counts': modes,
                'owned_declaration_count': owned_count,
                'new_target_count': 6, 'row_interval': [0, 16],
                'full_supplier_kernel_closed': success['full_supplier_kernel_closed'],
                'whole_geometry_decoded': False, 'P2_6_complete': False,
                'suppliers_recompiled': False, 'Lean_executed_for_export': False}
    output_root = stage / 'exports'
    output_root.mkdir(parents=True, exist_ok=True)
    output = output_root / 'cell05-scalable-completed-evidence.tar.xz'
    manifest_bytes = (json.dumps(manifest, indent=2) + '\n').encode()
    with tarfile.open(output, 'w:xz', preset=6) as tar:
        for path in sorted(selected):
            data = path.read_bytes()
            info = tarfile.TarInfo(str(path.relative_to(stage)))
            info.size = len(data)
            info.mode = 0o644
            tar.addfile(info, io.BytesIO(data))
        info = tarfile.TarInfo('ACCEPTED_EXPORT_MANIFEST.json')
        info.size = len(manifest_bytes)
        info.mode = 0o644
        tar.addfile(info, io.BytesIO(manifest_bytes))
    (output_root / 'ACCEPTED_EXPORT_MANIFEST.json').write_bytes(manifest_bytes)
    print(json.dumps({'archive': str(output), **pin(output), 'listed_members': len(members),
                      'owned_declaration_count': owned_count, 'step_counts': modes,
                      'full_supplier_kernel_closed': success['full_supplier_kernel_closed']}), flush=True)


if __name__ == '__main__':
    main()
