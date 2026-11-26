#!/usr/bin/env python3
"""Project immutable reference bindings from the two accepted evidence sets."""

import argparse
import hashlib
import json
import lzma
from pathlib import Path
import tarfile


HERE = Path(__file__).resolve().parent
OLD_ROOT = Path('/workspace/p2-1-20261125')
NEW_ROOT = Path('/workspace/p2-1-original96-20261126')
PRIVATE = Path('.lake/p2-private')
NEW_ATTEMPT = Path('evidence/original96-acceptance/attempt-002')
NEW_ARCHIVE = NEW_ROOT / 'original96-acceptance-attempt-002.tar.xz'
OLD_PROOFS = {
    'joint-receipt.json': '62e640bf94b650cac11b0b1cb42e6137b30101420d4a1a43c1484d9bd039651f',
    'export-manifest.json': '6e9da9d095b500c85c85d70a358db135e1b19b6eea4d80f5a2de40974e85ed0f',
    'joint.log': 'd4c1f7cd67222b2c785e698791ae76255e222f7f38c2c6e1de18349e6bb061a9',
    'Joint.lean': '29642c9e8a381585ef71a4d94f3c46e061e900491e2c2803df726837e40d81cc',
}
NEW_ROOTS = [
    'ImbalancedChen.Certificates.P2OriginalLog96',
    'ImbalancedChen.Certificates.P2OriginalP160DirectDivision',
]
NEW_CHECKS = [
    f'{NEW_ROOTS[0]}.logInterval_contains', f'{NEW_ROOTS[0]}.logInterval_eq_source',
    f'{NEW_ROOTS[1]}.directDiv_eq_round160', f'{NEW_ROOTS[1]}.directDiv_contains',
]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def old_reference(assets):
    raw = {name: (assets / name).read_bytes() for name in OLD_PROOFS}
    require({name: digest(data) for name, data in raw.items()} == OLD_PROOFS,
            'old joint/export asset digest mismatch')
    joint = json.loads(raw['joint-receipt.json'])
    export = json.loads(raw['export-manifest.json'])
    inputs = joint['inputs']
    selected = joint['selected_receipts']
    modules = export['object_manifest']
    artifacts = export['files']
    require(joint['status'] == 'JOINT_IMPORT_COMPATIBLE' and joint['inputs_unchanged'] and
            joint['command_result']['exit_code'] == 0 and
            joint['command_result']['log_sha256'] == OLD_PROOFS['joint.log'], 'old joint receipt failed')
    require(len(modules) == 140 and set(modules) == set(selected) == set(joint['project_modules']) ==
            set(export['accepted_modules']) and export['owned_declaration_count'] ==
            export['unique_owned_declaration_count'] == 18581 and not export['duplicate_owned_declarations'],
            'old owner selection differs')
    owners = {}
    for name, obj in modules.items():
        meta = export['accepted_modules'][name]
        receipt, receipt_sha = selected[name]
        declaration_key, = (path for path in meta['artifact_paths'] if path.endswith('/declarations.json'))
        decl = artifacts[declaration_key]
        require(meta['receipt_source'] == receipt and meta['receipt_sha256'] == receipt_sha and
                meta['source_sha256'] == obj['source_sha256'] and
                meta['object_sha256'] == obj['object_sha256'] and
                inputs['objects'][name]['.olean'] == [obj['object'], obj['object_sha256']] and
                joint['frozen_files'][receipt] == receipt_sha and
                joint['frozen_files'][decl['origin']] == decl['sha256'], 'old owner binding differs: ' + name)
        owners[name] = {'source': [str(OLD_ROOT / obj['source']), obj['source_sha256']],
                        'object': [obj['object'], obj['object_sha256']],
                        'receipt': [receipt, receipt_sha], 'declarations': [decl['origin'], decl['sha256']],
                        'count': meta['declaration_count']}

    loaded = {}
    native = {}
    native_prefixes = inputs['lean_path'].split(':')[1:3]
    for line in raw['joint.log'].decode().splitlines():
        if not line.startswith('P21_IMPORT '):
            continue
        row = json.loads(line.removeprefix('P21_IMPORT '))
        name, path = row['module'], row['olean']
        require(name not in loaded, 'duplicate module in original joint log: ' + name)
        resolved = joint['loaded_modules'][name]
        loaded[name] = [path, resolved]
        if any(path.startswith(prefix + '/') for prefix in native_prefixes):
            facets = inputs['objects'][name]
            require(facets['.olean'][0] == resolved, 'native path differs: ' + name)
            native[name] = facets
    require(len(loaded) == 6724 and loaded.keys() == joint['loaded_modules'].keys() and
            len(native) == 489 and sum(row['count'] for row in owners.values()) == 18581,
            'original joint inventory size differs')
    targets = artifacts['worktree/docs/verification/20261125-p2-1/TARGETS.json']
    require(joint['frozen_files'][targets['origin']] == targets['sha256'], 'old frozen targets differ')
    frozen = {targets['origin']: targets['sha256']}
    frozen.update({item['snapshot']: item['snapshot_sha256'] for item in inputs['snapshots']})
    return {'original_assets': OLD_PROOFS, 'owners': owners, 'loaded_modules': loaded,
            'native_modules': native, 'native_search_prefixes': native_prefixes,
            'lean_path': inputs['lean_path'], 'lean_sysroot': inputs['lean_sysroot'],
            'records': str(OLD_ROOT / PRIVATE / 'records.json'),
            'selected_records_sha256': inputs['records_sha256'], 'frozen_files': frozen,
            'roots': joint['roots'], 'checks': joint['public_checks']}


def new_reference(archive, expected_archive, expected_size, expected_summary):
    import io

    raw = archive.read_bytes()
    require(len(raw) == expected_size and digest(raw) == expected_archive,
            'new acceptance archive digest/size mismatch')
    with tarfile.open(fileobj=io.BytesIO(raw), mode='r:xz') as tar:
        def member(path):
            file = tar.getmember(str(path))
            require(file.isfile(), 'expected a regular archived file: ' + str(path))
            return tar.extractfile(file).read()

        summary_path = NEW_ATTEMPT / 'summary.json'
        summary_raw = member(summary_path)
        summary = json.loads(summary_raw)
        require(summary == expected_summary and
                summary['status'] == 'ACCEPTED_ORIGINAL96_INCREMENT' and
                summary['audit']['all_accepted'] and summary['owned_declarations'] ==
                summary['unique_owned_declarations'] == 122 and not summary['duplicate_owned_declarations'],
                'new attempt does not match the accepted summary')
        records_path = PRIVATE / 'records.json'
        records_raw = member(records_path)
        records = json.loads(records_raw)
        owners = {}
        require(set(summary['modules']) == {*NEW_ROOTS, NEW_ROOTS[0] + 'Series'}, 'unexpected new owner set')
        for name in summary['modules']:
            stem = Path(name.replace('.', '/'))
            source = stem.with_suffix('.lean')
            obj = PRIVATE / 'lib' / stem.with_suffix('.olean')
            consumed = summary['proof_inputs']
            receipt = json.loads(member(PRIVATE / 'audit' / name / 'latest.json'))
            declaration, = (p for p in receipt['artifacts'] if p.endswith('/declarations.json'))
            receipt_path = Path(declaration).with_name('receipt.json')
            receipt_raw = member(receipt_path)
            inventory = member(declaration)
            count = len(json.loads(inventory)['declarations'])
            record = records[name]
            require(receipt == json.loads(receipt_raw) and receipt['accepted'] and
                    receipt['source_sha256'] == record['source_sha256'] == consumed[str(source)] ==
                    digest(member(source)) and receipt['object_sha256'] == record['object_sha256'] ==
                    consumed[str(obj)] == digest(member(obj)) and
                    receipt['compile_closure_signature'] == record['closure_signature'] and
                    digest(inventory) == receipt['artifacts'][declaration] and
                    count == summary['audit']['modules'][name]['declarations'], 'new owner binding differs: ' + name)
            owners[name] = {'source': [str(NEW_ROOT / source), consumed[str(source)]],
                            'object': [str(NEW_ROOT / obj), consumed[str(obj)]],
                            'receipt': [str(NEW_ROOT / receipt_path), digest(receipt_raw)],
                            'declarations': [str(NEW_ROOT / declaration), digest(inventory)], 'count': count}
        require(sum(row['count'] for row in owners.values()) == 122, 'new owned declaration count differs')
        frozen = {str(NEW_ROOT / key): value for key, value in summary['reviewed_inputs'].items()}
        frozen.update({str(NEW_ARCHIVE): expected_archive, str(NEW_ROOT / summary_path): digest(summary_raw),
                       str(NEW_ROOT / records_path): digest(records_raw)})
    return {'archive_sha256': expected_archive, 'owners': owners, 'frozen_files': frozen,
            'roots': NEW_ROOTS, 'checks': NEW_CHECKS, 'proof_inputs': summary['proof_inputs']}


def shared_providers(old, new):
    private_inputs = new.pop('proof_inputs')
    for owner in new['owners'].values():
        for field in ('source', 'object'):
            private_inputs.pop(str(Path(owner[field][0]).relative_to(NEW_ROOT)))
    providers = {}
    for name, owner in old['owners'].items():
        source = name.replace('.', '/') + '.lean'
        if source not in private_inputs:
            continue
        obj = str(PRIVATE / 'lib' / (name.replace('.', '/') + '.olean'))
        require(private_inputs.pop(source) == owner['source'][1] and
                private_inputs.pop(obj) == owner['object'][1], 'shared provider differs: ' + name)
        providers[name] = [owner['source'][1], owner['object'][1]]
    require(len(providers) == 6 and not private_inputs, 'unexpected shared provider bindings')
    return providers


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--old-assets', type=Path, required=True)
    parser.add_argument('--new-archive-sha256', required=True)
    parser.add_argument('--new-archive-bytes', required=True, type=int)
    parser.add_argument('--new-summary', type=Path, required=True)
    parser.add_argument('--output', type=Path, default=HERE / 'joint-reference.json.xz')
    args = parser.parse_args()
    old = old_reference(args.old_assets)
    new_archive = {'path': str(NEW_ARCHIVE), 'sha256': args.new_archive_sha256,
                   'bytes': args.new_archive_bytes, 'summary': json.loads(args.new_summary.read_bytes())}
    probe = (HERE / 'Joint.lean').read_bytes()
    lines = probe.decode().splitlines()
    require([line[7:] for line in lines if line.startswith('#check ')] == old['checks'] + NEW_CHECKS and
            [line[7:] for line in lines if line.startswith('import ImbalancedChen.')] == old['roots'] + NEW_ROOTS and
            sum(line.startswith('example ') for line in lines) == 10, 'combined probe shape differs')
    contract = (HERE.parent / 'P160RemainingContract.lean').read_text().split('\n\n', 1)[1]
    require(contract in probe.decode(), 'the ten source-form contracts differ')
    reference = {'schema': 'p21-original96-joint-reference-v1', 'old': old,
                 'new_archive': new_archive, 'probe_sha256': digest(probe), 'source_form_contracts': 10}
    compressed = lzma.compress(json.dumps(reference, separators=(',', ':'), sort_keys=True).encode())
    with args.output.open('xb') as stream:
        stream.write(compressed)
    print(json.dumps({'reference': str(args.output), 'bytes': len(compressed), 'sha256': digest(compressed)}))


if __name__ == '__main__':
    main()
