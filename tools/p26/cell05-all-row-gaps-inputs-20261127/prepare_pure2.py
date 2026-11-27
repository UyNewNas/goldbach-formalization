#!/usr/bin/env python3
"""Copy two already accepted pure suppliers from the preserved original archive.

This is a data-only extraction. It executes no code from the archive and no Lean.
Original receipt bodies, paths, flags, and acceptance boundaries are unchanged.
"""
import argparse
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import tarfile

INNER = 'cell00-480-suppliers.tar.xz'
EXPECTED = (35675620, 'f945d949653f37567a7e66dfbc39a37b854d4114a4ef17b2279221ab8c971a7b')
MODULES = ('ImbalancedChen.P2OriginalLogMomentQ96ArithmeticPure',
           'ImbalancedChen.P2OriginalSaving19RowNumericsPure')
FULL = 'evidence/original/workspace/p26-recovery-candidates/cell00-rows-moment-floor/FULL_SOURCE_CLOSURE.json'


def identity(body):
    return {'bytes': len(body), 'sha256': hashlib.sha256(body).hexdigest()}


def save(path, body):
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        assert path.read_bytes() == body, f'Existing data differs: {path}'
    else:
        with path.open('xb') as f:
            f.write(body)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkpoint', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    outer = args.checkpoint.resolve(strict=True)
    output = args.output.resolve()
    with tarfile.open(outer, 'r') as t:
        row = t.getmember(INNER)
        assert row.isfile()
        inner = t.extractfile(row).read()
    pin = identity(inner)
    assert (pin['bytes'], pin['sha256']) == EXPECTED
    selected = {}
    with tarfile.open(fileobj=io.BytesIO(inner), mode='r:xz') as t:
        members = t.getmembers()
        assert len({x.name for x in members}) == len(members)
        byname = {x.name: x for x in members}
        manifest_body = t.extractfile('MANIFEST.json').read()
        manifest = json.loads(manifest_body)
        rows = {x['archive_path']: x for x in manifest['files']}
        assert len(rows) == len(manifest['files'])
        selected_names = {'MANIFEST.json', 'AUDIT.json', 'RUNTIME.json', FULL}
        for name, row in rows.items():
            if row.get('module') in MODULES or any('/' + m.rsplit('.', 1)[1] + '/' in name for m in MODULES):
                selected_names.add(name)
        assert len(selected_names) == 16
        for name in sorted(selected_names):
            p = PurePosixPath(name)
            assert not p.is_absolute() and '..' not in p.parts
            assert byname[name].isfile()
            body = t.extractfile(name).read()
            if name != 'MANIFEST.json':
                assert identity(body) == {k: rows[name][k] for k in ('bytes', 'sha256')}
            selected[name] = body
    audit = json.loads(selected['AUDIT.json'])
    closure = json.loads(selected[FULL])
    modules = [r for r in audit['modules'] if r['module'] in MODULES]
    assert len(modules) == 2
    for row in modules:
        assert row['acceptance_boundary'] == 'DIRECT_NORMAL_AND_KERNEL_RECEIPTS_VERIFIED'
        for mode in ('normal', 'kernel'):
            receipt_pin = row['receipts'][mode]['receipt']
            name = 'evidence/original' + receipt_pin['path']
            body = selected[name]
            assert identity(body) == {k: receipt_pin[k] for k in ('bytes', 'sha256')}
            record = json.loads(body)
            assert record['module'] == row['module'] and record['mode'] == mode
            assert record['status'] == 'succeeded' and record['exit_code'] == 0
            for k in ('source', 'object'):
                assert all(record[k][f] == row[k][f] for f in ('bytes', 'sha256'))
            log = selected['evidence/original' + record['log']['path']]
            assert identity(log) == {k: record['log'][k] for k in ('bytes', 'sha256')}
            prior = row['receipts'][mode]['prior_hash_pin']
            assert prior['manifest'] == '/' + FULL.removeprefix('evidence/original/')
            obj = closure
            for part in prior['pointer'].split('/')[1:]:
                obj = obj[int(part)] if isinstance(obj, list) else obj[part]
            assert all(obj[k] == receipt_pin[k] for k in ('path', 'bytes', 'sha256'))
    index = {
        'schema': 'p26_cell05_all_row_gaps_pure2_transport_v1',
        'original_outer_archive': str(outer),
        'original_inner_archive': {'member': INNER, **pin},
        'original_manifest': identity(selected['MANIFEST.json']),
        'original_modules': modules,
        'files': [{'relative_path': n, **identity(b),
                   'original_manifest_row': rows.get(n)} for n, b in sorted(selected.items())],
        'module_count': 2,
        'old_normal_commands_replayed': 0,
        'old_kernel_commands_replayed': 0,
        'new_Lean_commands': 0,
        'historical_explicit_trust_zero_claimed': False,
        'historical_loaded_runtime_inventory_claimed': False,
        'new_supplier_owned_audits_claimed': False,
        'P2_6_complete': False,
    }
    selected['TRANSPORT.json'] = (json.dumps(index, ensure_ascii=False, indent=2) + '\n').encode()
    for name, body in selected.items():
        save(output / 'pure2' / name, body)
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode='w:xz', format=tarfile.USTAR_FORMAT) as t:
        for name, body in sorted(selected.items()):
            info = tarfile.TarInfo(name)
            info.size = len(body)
            info.mode = 0o644
            info.uid = info.gid = info.mtime = 0
            t.addfile(info, io.BytesIO(body))
    archive = buffer.getvalue()
    save(output / 'pure2-original-evidence.tar.xz', archive)
    report = {'schema': 'p26_pure2_extraction_result_v1', 'archive': identity(archive),
              'members': len(selected), 'expanded_bytes': sum(map(len, selected.values())),
              'transport': identity(selected['TRANSPORT.json']), 'new_Lean_commands': 0}
    save(output / 'PURE2_EXPORT.json', (json.dumps(report, indent=2) + '\n').encode())
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
