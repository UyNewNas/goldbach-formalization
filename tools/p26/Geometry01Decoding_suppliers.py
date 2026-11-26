#!/usr/bin/env python3
"""Audit and package cell01 supplier bytes and existing receipts; never compile."""
from pathlib import Path
import hashlib
import io
import json
import re
import tarfile

BASE = Path('/workspace/p26-recovery-candidates')
PARSER = BASE / 'geometry-direct-packed/attempts/cell01-full-v2'
TYPED = PARSER / 'typed-v1'
REPO = Path(__file__).resolve().parents[2]
OUTPUT = Path('/dev/shm/p26-59264dd64286/geometry01-suppliers.tar.xz')
REPORT = REPO / 'docs/verification/20261126-p26/Geometry01Decoding_SUPPLIERS.json'


def fp(path):
    path = Path(path)
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def check(expected):
    actual = fp(expected['path'])
    assert actual == expected, ('Fingerprint mismatch', expected, actual)
    return actual


def same(a, b):
    return all(a.get(k) == b.get(k) for k in ['bytes', 'sha256'])


def read(path):
    return json.loads(Path(path).read_text())


def main():
    bootstrap = read(TYPED / 'BOOTSTRAP.json')
    progress = read(TYPED / 'PROGRESS.json')
    parser_manifest = read(PARSER / 'SOURCE_MANIFEST.json')
    pilot = PARSER.parent / 'cell01-pilot-v1'
    pilot_manifest = read(pilot / 'SOURCE_MANIFEST.json')
    legacy_owners = {r['module']: r for r in parser_manifest['owners'] + pilot_manifest['owners']}
    accepted_typed = set(progress['accepted_owners'])
    suppliers = {r['module']: {**r, 'role': 'parser_or_schema_supplier'} for r in bootstrap['accepted_suppliers']}
    assert len(suppliers) == 182 and len(accepted_typed) == 96
    for f in sorted((TYPED / 'owners').glob('*.json')):
        r = read(f)
        r['object'] = fp(TYPED / 'objects' / (r['module'].replace('.', '/') + '.olean'))
        r['owner_manifest'] = fp(f)
        r['role'] = 'accepted_typed_supplier' if r['module'] in accepted_typed else 'normal_only_pending_kernel'
        assert r['module'] not in suppliers
        suppliers[r['module']] = r
    assert len(suppliers) == 279
    members = {}

    def add(path, member):
        item = fp(path)
        if member in members:
            assert members[member] == item
        else:
            members[member] = item
        return {**item, 'archive_member': member}

    def add_evidence(path):
        path = Path(path)
        assert path.is_relative_to(BASE)
        return add(path, 'evidence/' + str(path.relative_to(BASE)))

    embedded = {}
    for p in [BASE / 'archive-char-input/local/DIAGNOSTIC.json',
              BASE / 'archive-char-input/local/COMPANION_DIAGNOSTIC.json']:
        diagnostic = read(p)
        for index, row in enumerate(diagnostic['commands']):
            embedded[(row['module'], row['stage'])] = (p, index, row)

    def receipt_candidates(module, mode):
        short = module.split('.')[-1]
        if module in legacy_owners:
            p = Path(legacy_owners[module][mode + '_receipt']['path'])
            return [(p, None, read(p))]
        if (module, mode) in embedded:
            return [embedded[(module, mode)]]
        if short == 'P2OriginalSaving19PackedChars':
            p = BASE / f'archive-packed-chars/logs/{mode}-core-v2-result.json'
            return [(p, None, read(p))]
        if short == 'P2OriginalSaving19ArchivePackedLoader':
            folder = BASE / 'archive-moment00/logs' / short
        elif short == 'P2OriginalSaving19ParseFromValue00':
            folder = BASE / 'archive-segment-generator/full-cell00/logs' / short
        elif short == 'P2OriginalSaving19ArchiveSchema':
            folder = BASE / 'archive-schema/logs'
        elif short == 'P2OriginalSaving19ArchiveRationalChars':
            folder = BASE / 'archive-geometry00-typed/logs' / short
        else:
            folder = TYPED / 'logs' / short
        result = []
        for p in sorted(folder.glob(mode + '-*-result.json')):
            try:
                row = read(p)
            except json.JSONDecodeError:
                continue
            result.append((p, None, row))
        return result

    certified, pending = [], []
    for module, original in suppliers.items():
        check(original['source'])
        check(original['object'])
        source = Path(original['source']['path'])
        project_source = REPO / (module.replace('.', '/') + '.lean')
        assert same(fp(project_source), original['source']), ('Repository source mismatch', module)
        imports = re.findall(r'(?m)^import\s+(ImbalancedChen\.\S+)', source.read_text())
        assert imports == original['project_imports'], ('Import manifest mismatch', module)
        assert all(m in suppliers for m in imports), ('Unpackaged project dependency', module)
        row = {'module': module, 'role': original['role'],
               'source': add(source, 'project/' + module.replace('.', '/') + '.lean'),
               'object': add(original['object']['path'], 'objects/' + module.replace('.', '/') + '.olean'),
               'project_imports': imports, 'receipts': {}}
        if 'owner_manifest' in original:
            check(original['owner_manifest'])
            row['owner_manifest'] = add_evidence(original['owner_manifest']['path'])
        for mode in ['normal', 'kernel']:
            matches = []
            for path, index, receipt in receipt_candidates(module, mode):
                if receipt.get('exit_code') != 0 or receipt.get('status', 'succeeded') != 'succeeded':
                    continue
                if not same(receipt.get('source', {}), original['source']):
                    continue
                if 'object' in receipt and not same(receipt['object'], original['object']):
                    continue
                matches.append((path, index, receipt))
            if not matches:
                assert original['role'] == 'normal_only_pending_kernel' and mode == 'kernel', (module, mode, 'Missing valid receipt')
                continue
            assert len(matches) == 1, ('Ambiguous acceptance receipt', module, mode)
            path, index, receipt = matches[0]
            ref = add_evidence(path)
            if index is not None:
                ref['embedded_command_index'] = index
            ref['exit_code'] = 0
            ref['source_sha256_matches'] = True
            ref['receipt_contains_object_fingerprint'] = 'object' in receipt
            if 'log' in receipt:
                check(receipt['log'])
                ref['log'] = add_evidence(receipt['log']['path'])
            row['receipts'][mode] = ref
        if set(row['receipts']) == {'normal', 'kernel'}:
            certified.append(row)
        else:
            pending.append(row)
    assert len(certified) == 278 and len(pending) == 1
    assert sum(r['role'] == 'accepted_typed_supplier' for r in certified) == 96
    extras = []
    for p in [PARSER / 'SOURCE_MANIFEST.json', PARSER / 'SOURCE_INPUTS.json',
              PARSER / 'FROZEN_SUPPLIERS.json', PARSER / 'BOOTSTRAP.json',
              pilot / 'SOURCE_MANIFEST.json', pilot / 'FROZEN_SUPPLIERS.json',
              TYPED / 'BOOTSTRAP.json', TYPED / 'PROGRESS.json',
              TYPED / 'INDEPENDENT_REVIEW.json',
              BASE / 'archive-packed-chars/RESULT.json',
              BASE / 'archive-char-input/SOURCE_ORIGIN.json']:
        extras.append(add_evidence(p))
    for name in ['generate.py', 'render_rows.py', 'quotation.py', 'raw_planner.py']:
        extras.append(add_evidence(TYPED / name))
    incomplete = TYPED / 'logs/P2OriginalSaving19Geometry01DirectDecodedRows066'
    for name in ['kernel-initial-command.json', 'kernel-initial-result.json',
                 'kernel-initial.log', 'kernel-initial-driver.log']:
        extras.append(add_evidence(incomplete / name))
    fixture = bootstrap['original_fixture']
    check(fixture)
    raw = add(fixture['path'], 'original-inputs/' + Path(fixture['path']).name)
    continuation_path = REPO / 'docs/verification/20261126-p26/Geometry01Decoding_CONTINUATION.json'
    continuation = read(continuation_path)
    pending_sources = []
    for entry in continuation['generated'] + [{'source': s} for s in continuation['shape_sources']]:
        source = entry['source']
        check(source)
        pending_sources.append(add(source['path'], 'project/ImbalancedChen/' + Path(source['path']).name))
    add(continuation_path, 'Geometry01Decoding_CONTINUATION.json')
    report = {'schema': 'saving19-geometry01-reused-suppliers-20261126',
              'whole_parser_project_closure': 180, 'generic_schema_suppliers': 2,
              'accepted_typed_suppliers': 96, 'normal_kernel_accepted_total': 278,
              'normal_only_pending_kernel': 1, 'pending_new_source_count': len(pending_sources),
              'original_input': raw, 'accepted': certified, 'normal_only': pending,
              'new_sources_pending_cloud_compile': pending_sources,
              'cloud_order': continuation['cloud_order'], 'additional_evidence': extras,
              'all_archive_members': members, 'source_and_object_bytes_rechecked': True,
              'local_compiler_calls': 0, 'cloud_compiler_calls': 0,
              'empty_kernel_receipt_is_acceptance': False,
              'overall_typed_geometry_proved': False}
    REPORT.parent.mkdir(parents=True, exist_ok=True)
    REPORT.write_text(json.dumps(report, indent=2) + '\n')
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    assert not OUTPUT.exists(), 'Do not overwrite an earlier supplier package.'
    report_bytes = REPORT.read_bytes()
    with tarfile.open(OUTPUT, 'w:xz', preset=1) as tar:
        header = tarfile.TarInfo('Geometry01Decoding_SUPPLIERS.json')
        header.size = len(report_bytes)
        header.mode = 0o644
        tar.addfile(header, io.BytesIO(report_bytes))
        for member, item in sorted(members.items()):
            tar.add(item['path'], arcname=member, recursive=False)
    result = {'archive': fp(OUTPUT), 'manifest': fp(REPORT),
              'accepted': len(certified), 'normal_only': len(pending),
              'new_sources': len(pending_sources), 'members': len(members) + 1}
    summary = OUTPUT.with_suffix('').with_suffix('.summary.json')
    summary.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
