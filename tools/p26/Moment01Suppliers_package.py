#!/usr/bin/env python3
"""Recheck and package the accepted Moment01 closure without compiling anything."""
from pathlib import Path
import hashlib
import io
import json
import re
import tarfile

REPO = Path(__file__).resolve().parents[2]
BASE = Path('/workspace/p26-recovery-candidates')
ROOT = BASE / 'archive-moment01'
OUTPUT = Path('/dev/shm/p26-59264dd64286/moment01-suppliers.tar.xz')
REPORT = REPO / 'docs/verification/20261126-p26/Moment01_SUPPLIERS.json'


def fp(path):
    path = Path(path)
    b = path.read_bytes()
    return {'path': str(path), 'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()}


def read(path):
    return json.loads(Path(path).read_text())


def same(a, b):
    return all(a.get(k) == b.get(k) for k in ['bytes', 'sha256'])


def check(item):
    actual = fp(item['path'])
    assert actual == {k: item[k] for k in ['path', 'bytes', 'sha256']}, ('Changed archived file', item, actual)


def main():
    closure_path = ROOT / 'FULL_SOURCE_CLOSURE.json'
    closure = read(closure_path)
    final = read(ROOT / 'FINAL_RESULT.json')
    shape = read(ROOT / 'SHAPE_RESULT.json')
    assert final['status'] == 'WHOLE_PARSE_TYPED_AND_SHAPE_NORMAL_KERNEL_PASSED'
    rows = closure['sources_objects_and_receipts']
    assert len(rows) == 88
    geometry_manifest_path = REPO / 'docs/verification/20261126-p26/Geometry01Decoding_SUPPLIERS.json'
    geometry = {r['module']: r for r in read(geometry_manifest_path)['accepted']}
    known = {r['module'] for r in rows}
    members = {}

    def add(path, member):
        item = fp(path)
        if member in members:
            assert members[member] == item
        else:
            members[member] = item
        return {**item, 'archive_member': member}

    def evidence(path):
        path = Path(path)
        return add(path, 'evidence/' + str(path.relative_to(BASE)))

    audited, reused = [], 0
    for row in rows:
        module = row['module']
        check(row['source'])
        check(row['object'])
        repo_source = REPO / (module.replace('.', '/') + '.lean')
        assert same(fp(repo_source), row['source']), ('Repository source hash mismatch', module)
        imports = re.findall(r'(?m)^import\s+(\S+)', Path(row['source']['path']).read_text())
        assert imports == row['imports'], ('Import manifest mismatch', module)
        assert all(m in known for m in imports if m.startswith('ImbalancedChen.')), ('Missing project dependency', module)
        record = {'module': module,
                  'source': add(row['source']['path'], 'project/' + module.replace('.', '/') + '.lean'),
                  'object': add(row['object']['path'], 'objects/' + module.replace('.', '/') + '.olean'),
                  'repository_source': fp(repo_source), 'imports': imports,
                  'reused_supplier': row['reused_without_compilation'], 'receipts': {}}
        if row['reused_without_compilation']:
            reused += 1
            original = geometry[module]
            assert same(original['source'], row['source']) and same(original['object'], row['object'])
        for mode in ['normal', 'kernel']:
            if row['reused_without_compilation']:
                ref = geometry[module]['receipts'][mode]
            else:
                ref = row[mode + '_receipt']
            check(ref)
            receipt = read(ref['path'])
            embedded_index = ref.get('embedded_command_index')
            if embedded_index is not None:
                receipt = receipt['commands'][embedded_index]
            assert receipt['exit_code'] == 0 and receipt.get('status', 'succeeded') == 'succeeded', (module, mode)
            assert same(receipt['source'], row['source']), (module, mode, 'Wrong source receipt')
            if 'object' in receipt:
                assert same(receipt['object'], row['object']), (module, mode, 'Wrong object receipt')
            attached = evidence(ref['path'])
            if embedded_index is not None:
                attached['embedded_command_index'] = embedded_index
            attached['receipt_contains_object_fingerprint'] = 'object' in receipt
            if 'log' in receipt:
                check(receipt['log'])
                attached['log'] = evidence(receipt['log']['path'])
            record['receipts'][mode] = attached
        audited.append(record)
    assert reused == 7
    by_name = {r['module']: r for r in audited}
    reached = set()

    def visit(module):
        if module in reached:
            return
        reached.add(module)
        for imported in by_name[module]['imports']:
            if imported.startswith('ImbalancedChen.'):
                visit(imported)

    visit('ImbalancedChen.P2OriginalSaving19Moment01Shape')
    assert reached == known, ('Unexpected or missing closure members', sorted(known - reached), sorted(reached - known))
    extras = []
    for name in ['FINAL_RESULT.json', 'SHAPE_RESULT.json', 'FULL_SOURCE_CLOSURE.json',
                 'PURE_PARSE_RESULT.json', 'TYPED_RESULT.json', 'BOOTSTRAP.json',
                 'TYPED_BOOTSTRAP.json', 'FINAL_BIND_REPAIR.json']:
        extras.append(evidence(ROOT / name))
    for failed in final['failures_preserved']:
        check(failed)
        extras.append(evidence(failed['path']))
    original = final['original_input']
    check(original)
    raw = add(original['path'], 'original-inputs/' + Path(original['path']).name)
    add(geometry_manifest_path, 'evidence/Geometry01Decoding_SUPPLIERS.json')
    report = {'schema': 'saving19-moment01-reused-suppliers-20261126',
              'status': 'EXACT_SOURCE_OBJECT_NORMAL_KERNEL_RECEIPTS_RECHECKED',
              'target': 'ImbalancedChen.P2OriginalSaving19Moment01Shape',
              'project_closure_count': 88, 'new_previously_accepted_owners': 81,
              'reused_generic_suppliers': 7, 'record_count': 144,
              'original_input': raw, 'accepted': audited,
              'repository_source_hash_mismatches': [], 'additional_evidence': extras,
              'all_archive_members': members, 'existing_geometry01_overlap_identical': True,
              'original_closure_manifest': fp(closure_path),
              'original_shape_receipts': shape['owner'],
              'local_compiler_calls': 0, 'cloud_compiler_calls': 0,
              'new_claim_of_floor_validity': False, 'new_claim_of_Archive_aliases': False}
    REPORT.parent.mkdir(parents=True, exist_ok=True)
    REPORT.write_text(json.dumps(report, indent=2) + '\n')
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    assert not OUTPUT.exists(), 'Preserve any existing package.'
    data = REPORT.read_bytes()
    with tarfile.open(OUTPUT, 'w:xz', preset=1) as tar:
        h = tarfile.TarInfo('Moment01_SUPPLIERS.json')
        h.size, h.mode = len(data), 0o644
        tar.addfile(h, io.BytesIO(data))
        for member, item in sorted(members.items()):
            tar.add(item['path'], arcname=member, recursive=False)
    summary = {'archive': fp(OUTPUT), 'manifest': fp(REPORT),
               'accepted': len(audited), 'generic_reused': reused, 'members': len(members) + 1,
               'repository_source_hash_mismatches': []}
    OUTPUT.with_suffix('').with_suffix('.summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == '__main__':
    main()
