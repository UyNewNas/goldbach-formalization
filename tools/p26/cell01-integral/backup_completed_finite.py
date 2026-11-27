"""Preserve completed local finite checks; this grants no import-join credit."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import tarfile

ROOT = Path(__file__).resolve().parents[3]


def pin(path):
    raw = path.read_bytes()
    return {'path': str(path), 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def check(item):
    assert pin(Path(item['path'])) == item, item['path']


def main(base, out):
    paths = list(base.glob('batch-*/SUMMARY.json'))
    assert len(paths) == 1
    summary_path = paths[0]
    summary = json.loads(summary_path.read_text())
    assert summary['status'] == 'passed_local_finite_checks'
    assert summary['formal_acceptance'] is False and summary['P2_6_complete'] is False
    rows = summary['rows']
    assert rows == sorted(set(rows)) and rows and all(1 <= row < 144 for row in rows)
    assert summary['owned_declarations'] == 292 * len(rows)
    assert len(summary['results']) == len(rows)
    check(summary['inputs'])
    inputs = json.loads(Path(summary['inputs']['path']).read_text())
    assert len(inputs) == summary['external_and_project_inputs_rechecked']
    for item in inputs: check(item)
    prepared_path = base / 'MANIFEST.json'
    prepared = json.loads(prepared_path.read_text())
    for key in ['qualification_parent', 'core_parent', 'wrapper_source']: check(prepared[key])
    members = {'SUMMARY.json': summary_path, 'INPUT_FINGERPRINTS.json': Path(summary['inputs']['path']),
               'CONTROLS.json': prepared_path, 'OwnedTemplate.lean': base / 'OwnedTemplate.lean',
               'FINITE_IMPORT_TEMPLATE.json': base / 'FINITE_IMPORT_TEMPLATE.json'}
    for name in ['build_finite_p1.py', 'build_finite_p2.py', 'qualify_suppliers.py']:
        members['tools/' + name] = ROOT / 'tools/p26/cell01-integral' / name
    members['tools/backup_completed_finite.py'] = Path(__file__)
    for row, item in zip(rows, summary['results']):
        check(item)
        run_path = Path(item['path'])
        run = json.loads(run_path.read_text())
        module = f'ImbalancedChen.P2OriginalSaving19Cell01Row{row:03d}Finite'
        assert run['row'] == row and run['module'] == module
        assert run['status'] == 'passed_local_finite_checks' and run['owned_declarations'] == 292
        assert run['inputs'] == summary['inputs']
        assert [c['label'] for c in run['commands']] == ['normal', 'kernel', 'owned']
        for command in run['commands']:
            assert command['exit_code'] == 0
            check(command['log'])
        for key in ['source', 'object', 'audit_source']: check(run[key])
        relative = module.replace('.', '/')
        source = ROOT / (relative + '.lean')
        assert all(pin(source)[k] == run['source'][k] for k in ['bytes', 'sha256'])
        members['sources/' + relative + '.lean'] = source
        members['objects/' + relative + '.olean'] = Path(run['object']['path'])
        for path in run_path.parent.iterdir():
            if path.is_file(): members['verification/' + module + '/' + path.name] = path
    out.mkdir(parents=True, exist_ok=True)
    target = out / 'CAPSULE.json'
    assert not target.exists(), 'Do not overwrite a completed backup.'
    manifest = {'formal_acceptance': False, 'P2_6_complete': False,
        'current_P2_import_join_accepted': False,
        'scope': 'Exact completed standalone local finite-owner checks only.',
        'members': {name: pin(path) for name, path in members.items()}}
    payload = {name: path.read_bytes() for name, path in members.items()}
    payload['MANIFEST.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
    archive = out / 'evidence.tar.xz'
    with tarfile.open(archive, 'w:xz') as tar:
        for name, raw in sorted(payload.items()):
            entry = tarfile.TarInfo(name)
            entry.size, entry.mode = len(raw), 0o644
            tar.addfile(entry, io.BytesIO(raw))
    with tarfile.open(archive) as tar:
        assert len(tar.getmembers()) == len(payload)
        for entry in tar: assert tar.extractfile(entry).read() == payload[entry.name]
    for name, item in manifest['members'].items(): assert pin(members[name]) == item
    report = {'formal_acceptance': False, 'P2_6_complete': False,
        'current_P2_import_join_accepted': False, 'rows': rows,
        'normal': len(rows), 'stock_kernel': len(rows), 'full_owned': len(rows),
        'standalone_owned_occurrences': summary['owned_declarations'],
        'global_unique_declarations_claimed': False,
        'input_files_rechecked': len(inputs), 'archive': pin(archive),
        'readback_members': len(payload), 'summary': pin(summary_path),
        'source': pin(Path(__file__))}
    target.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args()
    main(args.base, args.out)
