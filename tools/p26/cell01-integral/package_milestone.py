"""Publish only completed bounded Cell01 scopes, preserving pending scopes."""
import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile

import qualify_suppliers as qualifier

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-cell01-next-20261128')
OUT = ROOT / 'docs/verification/20261128-p26-cell01-continuation'


def pin(path):
    raw = path.read_bytes()
    return {'path': str(path), 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def main():
    runs = {}
    for label, directory in [('qualification', 'qualification'),
                             ('generic', 'generic-transport'), ('core', 'verification-core')]:
        path = STAGE / directory / 'RUN.json'
        run = json.loads(path.read_text())
        assert run['status'] == 'succeeded' and run['formal_acceptance'], label
        for record in run['commands']:
            assert record['exit_code'] == 0
            assert pin(Path(record['log']['path'])) == record['log']
        for key in ['replay_source', 'audit_source', 'verifier_source',
                    'wrapper_source', 'incoming_modules']:
            if key in run:
                assert pin(Path(run[key]['path'])) == run[key]
        if label in {'generic', 'core'}:
            item = run['final_external_readback']
            path = STAGE / directory / 'FINAL_EXTERNAL_READBACK.json'
            assert pin(path) == item
            report = json.loads(path.read_text())
            assert report['status'] == 'matched' and report['problems'] == []
            assert report['unique_physical_files_hashed'] == 54309
            assert pin(Path(report['plan']['path'])) == report['plan']
        runs[label] = run
    assert runs['qualification']['owned_modules'] == 407
    assert runs['qualification']['owned_declarations'] == 26810
    assert runs['generic']['owned_declarations'] == 16
    assert runs['core']['qualification_parent'] == pin(STAGE / 'qualification/RUN.json')
    assert runs['core']['generic_transport_parent'] == pin(STAGE / 'generic-transport/RUN.json')
    context_path = Path(runs['qualification']['recovered_context']['path'])
    assert pin(context_path) == runs['qualification']['recovered_context']
    context = json.loads(context_path.read_text())
    qualifier.validate(context)
    assert runs['generic']['parent'] == context['accepted_parent']
    for info in context['project_closure'].values():
        for key in ['source', 'selected_object']:
            assert pin(Path(info[key]['path'])) == info[key]
    for item in context['native_artifacts'] + list(context['runtime'].values()):
        assert pin(Path(item['path'])) == item
    for key in ['source', 'object', 'audit_source']:
        item = runs['generic'][key]
        assert pin(Path(item['path'])) == item
    for info in runs['core']['project_closure'].values():
        assert pin(Path(info['source']['path'])) == info['source']
        item = info.get('new_object', info.get('reused_object'))
        assert item is not None and pin(Path(item['path'])) == item
    finite_path = STAGE / 'RECOVERED_FINITE17.json'
    finite = json.loads(finite_path.read_text())
    assert finite['formal_acceptance'] is False and finite['P2_6_complete'] is False
    expected = {'ImbalancedChen.P2OriginalSaving19Cell01Row' + f'{n:03d}' + 'Finite'
                for n in [*range(1, 9), *range(98, 107)]}
    assert len(finite['modules']) == len(expected) == 17
    assert {item['module'] for item in finite['modules']} == expected
    for item in finite['modules']:
        assert item['current_P2_import_qualification'] is False
        source = ROOT / (item['module'].replace('.', '/') + '.lean')
        assert pin(source) == item['source']
        assert pin(Path(item['object']['path'])) == item['object']
    host_path = STAGE / 'HOST_INTEGRAL_TARGET.json'
    host = json.loads(host_path.read_text())
    assert host['formal_acceptance'] is False and host['rows'] == 144
    assert pin(Path(host['source']['path'])) == host['source']
    records = json.loads(Path(host['source']['path']).read_text())['records']
    assert [int(row['simplex_id']) for row in records] == list(range(144))
    assert str(sum(int(row['new_floor_Q96']) for row in records)) == host['saved_new_numerator_sum']
    assert host['degree'] == 6 and int(host['Q96_denominator']) == 2**96
    catalog = {}
    for module, info in context['project_closure'].items():
        catalog[module] = {'source': info['source'], 'selected_object': info['selected_object'],
                          'origin': 'accepted-current930' if info['origin'] == 'accepted-current930'
                          else 'qualified-cell01-supplier-join'}
    module = 'ImbalancedChen.P2OriginalSaving19OriginalFloorTransport'
    target = STAGE / 'objects' / (module.replace('.', '/') + '.olean')
    assert pin(target)['sha256'] == runs['generic']['object']['sha256']
    catalog[module] = {'source': runs['generic']['source'], 'selected_object': pin(target),
                       'origin': 'accepted-generic-original-floor-transport'}
    for module, info in runs['core']['project_closure'].items():
        if 'new_object' in info:
            assert module not in catalog
            catalog[module] = {'source': info['source'], 'selected_object': info['new_object'],
                               'origin': 'accepted-cell01-selector-and-sibling-sign-core'}
    assert len(catalog) == 1341
    successor = {'schema': 'p26_current_accepted_project_context_v1',
        'formal_acceptance': True, 'P2_6_complete': False,
        'original_full_snapshot_verified': False,
        'scope': 'Accepted current930 plus407 exact Cell01 suppliers, one generic transport and three selector/sign owners; no Cell01 integral.',
        'accepted_parent': context['accepted_parent'],
        'phase_parents': {label: pin(STAGE / directory / 'RUN.json')
                         for label, directory in [('qualification', 'qualification'),
                             ('generic', 'generic-transport'), ('core', 'verification-core')]},
        'project_closure': catalog, 'native_artifacts': context['native_artifacts'],
        'runtime': context['runtime'], 'lean_path': context['lean_path']}
    successor_path = STAGE / 'CURRENT_ACCEPTED_CONTEXT.json'
    raw = json.dumps(successor, indent=2) + '\n'
    if successor_path.exists(): assert successor_path.read_text() == raw
    else: successor_path.write_text(raw)
    OUT.mkdir(parents=True, exist_ok=True)
    members = {'RECOVERED_BASE_CONTEXT.json': context_path,
               'INCOMING_BASE_MODULES.json': STAGE / 'INCOMING_BASE_MODULES.json',
               'RECOVERED_FINITE17.json': finite_path,
               'HOST_INTEGRAL_TARGET.json': host_path,
               'CURRENT_ACCEPTED_CONTEXT.json': successor_path}
    for label, directory in [('qualification', 'qualification'),
                             ('generic', 'generic-transport'), ('core', 'verification-core')]:
        folder = STAGE / directory
        for path in folder.iterdir():
            if path.is_file() and path.suffix in {'.json', '.log', '.lean'}:
                members[label + '/' + path.name] = path
    object_members = {}
    generic = runs['generic']['object']
    object_members['ImbalancedChen/P2OriginalSaving19OriginalFloorTransport.olean'] = Path(generic['path'])
    for module, info in runs['core']['project_closure'].items():
        if 'new_object' in info:
            object_members[module.replace('.', '/') + '.olean'] = Path(info['new_object']['path'])
    assert len(object_members) == 4
    manifest = {'formal_acceptance': False, 'P2_6_complete': False,
        'members': {n: pin(p) for n, p in members.items()},
        'new_objects': {n: pin(p) for n, p in object_members.items()}}
    archive = OUT / 'evidence.tar.xz'
    payload = {n: p.read_bytes() for n, p in members.items()}
    payload.update({'objects/' + n: p.read_bytes() for n, p in object_members.items()})
    payload['MANIFEST.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
    with tarfile.open(archive, 'w:xz') as tar:
        for name, raw in sorted(payload.items()):
            entry = tarfile.TarInfo(name)
            entry.size, entry.mode = len(raw), 0o644
            tar.addfile(entry, io.BytesIO(raw))
    with tarfile.open(archive) as tar:
        assert len(tar.getmembers()) == len(payload)
        for entry in tar:
            assert tar.extractfile(entry).read() == payload[entry.name]
    for name, item in manifest['members'].items():
        assert pin(members[name]) == item
    for name, item in manifest['new_objects'].items():
        assert pin(object_members[name]) == item
    qualifier.validate(context)
    for label, directory in [('qualification', 'qualification'),
                             ('generic', 'generic-transport'), ('core', 'verification-core')]:
        target = OUT / label
        target.mkdir(exist_ok=True)
        for name in ['RUN.json', 'owned-declarations.json', 'shared-declarations.json',
                     'FINAL_EXTERNAL_READBACK.json']:
            if label == 'qualification' and name == 'owned-declarations.json':
                continue  # The complete large inventory is in the checked archive.
            source = STAGE / directory / name
            if source.exists(): shutil.copyfile(source, target / name)
    shutil.copyfile(STAGE / 'HOST_INTEGRAL_TARGET.json', OUT / 'HOST_INTEGRAL_TARGET.json')
    shutil.copyfile(STAGE / 'RECOVERED_FINITE17.json', OUT / 'RECOVERED_FINITE17.json')
    shutil.copyfile(successor_path, OUT / 'CURRENT_ACCEPTED_CONTEXT.json')
    capsule = {'schema': 'p26_cell01_bounded_continuation_milestone_v1',
        'P2_6_complete': False, 'Cell01_integral_complete': False,
        'original_full_snapshot_verified': False,
        'accepted_scopes': {
            'supplier_join': {'modules': 407, 'canonical_declarations': 26810,
                'shared_serialized_occurrences': runs['qualification']['shared_serialized_occurrences'],
                'selected_project_union': 1337},
            'generic_original_floor_transport': {'modules': 1, 'owned_declarations': 16},
            'cell01_selector_and_sibling_signs': {'modules': 3,
                'owned_declarations': runs['core']['owned_declarations'],
                'original_rows': 144, 'branching_nodes': 123, 'sibling_separators': 165,
                'forms': 102, 'physical_pairwise_disjointness_claimed': False}},
        'first8_P1_checks': {'normal': 8, 'stock_kernel': 8, 'full_owned': 8,
            'owned_declarations': 2336, 'input_files_rechecked': 15863,
            'current_P2_import_join_accepted': False,
            'artifact_commit': 'ddbb0ffb6ef3f22e5b33a65f1db098ec2c48b13f',
            'archive_sha256': 'c8d3f55eca7b5c31bb32e1b21fea639f609095156f500c32706fc3bfa09478fc'},
        'source_materials': {
            'original399': {'commit': 'c14c3cae782837a5a7210940338ebb795d6d89a8',
                'archive_sha256': '5278c2838907db737fd14ee6c5cd34afea609f73d875a5a7f8c3d29dd3239c72'},
            'historical_C9': {'commit': '2968bae70ec4aaa3d0a45161a657190e4bac6574',
                'archive_sha256': '9cf583475d3e45f67e3ba44da270658a916ee1a118986d7f0a671ac232c8007c',
                'current_P2_import_join_accepted': False}},
        'evidence_archive': pin(archive), 'archive_readback_members': len(payload),
        'host_target': pin(host_path), 'recovered_finite17': pin(finite_path),
        'current_accepted_context': pin(successor_path),
        'final_external_readbacks': {label: runs[label]['final_external_readback']
                                    for label in ['generic', 'core']},
        'packager_source': pin(Path(__file__))}
    (OUT / 'CAPSULE.json').write_text(json.dumps(capsule, indent=2) + '\n')
    print(json.dumps({'archive': capsule['evidence_archive'], 'members': len(payload),
        'accepted_supplier_declarations': 26810, 'accepted_core_declarations': runs['core']['owned_declarations'],
        'Cell01_integral_complete': False, 'P2_6_complete': False}), flush=True)


if __name__ == '__main__':
    main()
