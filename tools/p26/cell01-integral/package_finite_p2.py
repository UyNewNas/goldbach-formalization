"""Preserve the completed P2 rows9–24 checks without granting join credit."""
import hashlib
import io
import json
from pathlib import Path
import tarfile

ROOT = Path(__file__).resolve().parents[3]
BASE = Path('/workspace/p26-cell01-finite-p2-20261128')
OUT = ROOT / 'docs/verification/20261128-p26-cell01-continuation/finite9-24'


def pin(path):
    raw = path.read_bytes()
    return {'path': str(path), 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def check(item):
    assert pin(Path(item['path'])) == item, item['path']


def main():
    batch = BASE / ('batch-' + '-'.join(map(str, range(9, 25))))
    summary_path = batch / 'SUMMARY.json'
    summary = json.loads(summary_path.read_text())
    assert summary['status'] == 'passed_local_finite_checks'
    assert summary['formal_acceptance'] is False and summary['P2_6_complete'] is False
    assert summary['rows'] == list(range(9, 25)) and summary['owned_declarations'] == 4672
    check(summary['inputs'])
    inputs = json.loads(Path(summary['inputs']['path']).read_text())
    assert len(inputs) == summary['external_and_project_inputs_rechecked'] == 15871
    for item in inputs: check(item)
    manifest_path = BASE / 'MANIFEST.json'
    prepared = json.loads(manifest_path.read_text())
    for key in ['qualification_parent', 'core_parent', 'wrapper_source']:
        check(prepared[key])
    parent = json.loads(Path(prepared['qualification_parent']['path']).read_text())
    check(parent['verifier_source'])
    members = {'SUMMARY.json': summary_path, 'INPUT_FINGERPRINTS.json': Path(summary['inputs']['path']),
               'CONTROLS.json': manifest_path, 'OwnedTemplate.lean': BASE / 'OwnedTemplate.lean',
               'FINITE_IMPORT_TEMPLATE.json': BASE / 'FINITE_IMPORT_TEMPLATE.json'}
    for name in ['build_finite_p1.py', 'build_finite_p2.py', 'qualify_suppliers.py']:
        members['tools/' + name] = ROOT / 'tools/p26/cell01-integral' / name
    assert len(summary['results']) == 16
    for row, result_pin in zip(range(9, 25), summary['results']):
        check(result_pin)
        path = Path(result_pin['path'])
        run = json.loads(path.read_text())
        assert run['row'] == row and run['status'] == 'passed_local_finite_checks'
        assert run['owned_declarations'] == 292
        assert [item['label'] for item in run['commands']] == ['normal', 'kernel', 'owned']
        for item in run['commands']:
            assert item['exit_code'] == 0
            check(item['log'])
        for key in ['source', 'object', 'audit_source']: check(run[key])
        name = run['module'].replace('.', '/')
        source = ROOT / (name + '.lean')
        assert all(pin(source)[k] == run['source'][k] for k in ['bytes', 'sha256'])
        members['sources/' + name + '.lean'] = source
        members['objects/' + name + '.olean'] = Path(run['object']['path'])
        for file in path.parent.iterdir():
            if file.is_file(): members['verification/' + run['module'] + '/' + file.name] = file
    manifest = {'schema': 'p26_cell01_finite9_24_transport_v1',
        'formal_acceptance': False, 'P2_6_complete': False,
        'current_P2_import_join_accepted': False,
        'scope': 'Sixteen exact original finite owners passed local normal, stock kernel and full owned checks; aggregate import join, original floor transport and integrals remain separate.',
        'members': {name: pin(path) for name, path in members.items()}}
    OUT.mkdir(parents=True, exist_ok=True)
    archive = OUT / 'evidence.tar.xz'
    payload = {name: path.read_bytes() for name, path in members.items()}
    payload['MANIFEST.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
    with tarfile.open(archive, 'w:xz') as tar:
        for name, raw in sorted(payload.items()):
            entry = tarfile.TarInfo(name)
            entry.size, entry.mode = len(raw), 0o644
            tar.addfile(entry, io.BytesIO(raw))
    with tarfile.open(archive) as tar:
        assert len(tar.getmembers()) == len(payload)
        for item in tar: assert tar.extractfile(item).read() == payload[item.name]
    for name, item in manifest['members'].items(): assert pin(members[name]) == item
    report = {'formal_acceptance': False, 'P2_6_complete': False,
        'rows': list(range(9, 25)), 'normal': 16, 'stock_kernel': 16, 'full_owned': 16,
        'owned_declarations': 4672, 'input_files_rechecked': len(inputs),
        'current_P2_import_join_accepted': False,
        'archive': pin(archive), 'readback_members': len(payload),
        'source': pin(Path(__file__)), 'summary': pin(summary_path),
        'qualification_parent': prepared['qualification_parent'], 'core_parent': prepared['core_parent']}
    (OUT / 'CAPSULE.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    main()
