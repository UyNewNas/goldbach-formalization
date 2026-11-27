"""Publish a capsule only after the current Cell00 integral checks pass."""
import hashlib
import importlib.util
import io
import json
import lzma
from pathlib import Path
import shutil
import tarfile

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-cell00-next-20261128')
OUT = ROOT / 'docs/verification/20261128-p26-cell00-integral'
PHASES = ['physical', 'separation', 'packing', 'source']
AGGREGATE = 'ImbalancedChen.P2OriginalSaving19Cell00AllRowArithmetic'


def pin(path):
    data = path.read_bytes()
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def checked(item):
    path = Path(item['path'])
    assert pin(path) == {k: item[k] for k in ['bytes', 'sha256']}
    return path


def selected(info):
    checked(info['source'])
    item = info.get('selected_object', info.get('new_object', info.get('reused_object')))
    assert item is not None
    checked(item)
    return item


def copy_checked(path, dest):
    expected = pin(path)
    shutil.copyfile(path, dest)
    assert pin(dest) == expected


def compress_checked(path, dest):
    raw = path.read_bytes()
    dest.write_bytes(lzma.compress(raw, preset=6))
    assert lzma.decompress(dest.read_bytes()) == raw
    return {'original': {'name': path.name, **pin(path)},
            'compressed': {'name': dest.name, **pin(dest)}}


def main():
    qpath = STAGE / 'qualification/RUN.json'
    qualification = json.loads(qpath.read_text())
    assert qualification['status'] == 'succeeded' and qualification['formal_acceptance']
    assert qualification['kernel_join']['kernel_replay_succeeded']
    assert qualification['owned_modules'] == 468 and qualification['owned_declarations'] == 28059
    assert all(x['exit_code'] == 0 for x in qualification['commands'])
    for key in ['audit_source', 'replay_source', 'verifier_source', 'kernel_verifier_source']:
        checked(qualification[key])
    audit_log = checked(next(c['log'] for c in qualification['commands'] if c['label'] == 'owned'))
    logged_owned, logged_shared = [], []
    for line in audit_log.read_text().splitlines():
        if line.startswith('P26_CELL00_SUPPLIER_AUDIT_DECL '):
            logged_owned.append(json.loads(line.split(' ', 1)[1]))
        if line.startswith('P26_CELL00_SUPPLIER_AUDIT_SHARED '):
            logged_shared.append(json.loads(line.split(' ', 1)[1]))
    assert len(logged_owned) == 28059 and len(logged_shared) == 229
    assert logged_owned == json.loads((STAGE / 'qualification/owned-declarations.json').read_text())
    assert logged_shared == json.loads((STAGE / 'qualification/shared-declarations.json').read_text())
    OUT.mkdir(parents=True, exist_ok=True)
    qout = OUT / 'qualification'
    qout.mkdir(exist_ok=True)
    copy_checked(qpath, qout / 'RUN.json')
    compressed = {}
    for command in qualification['commands']:
        source = checked(command['log'])
        if command['label'] == 'owned':
            compressed['owned_log'] = compress_checked(source, qout / 'owned.log.xz')
        else:
            copy_checked(source, qout / source.name)
    compressed['owned_declarations'] = compress_checked(STAGE / 'qualification/owned-declarations.json',
                                                        qout / 'owned-declarations.json.xz')
    assert qualification['shared_serialized_occurrences'] == 229
    assert qualification['different_shared_bodies_rechecked'] == 1
    compressed['shared_declarations'] = compress_checked(STAGE / 'qualification/shared-declarations.json',
                                                         qout / 'shared-declarations.json.xz')
    kernel_parent = checked(qualification['passed_kernel_parent'])
    copy_checked(kernel_parent, qout / 'kernel-parent-owned-failed-RUN.json')
    compressed['previous_owned_failure'] = compress_checked(
        checked(qualification['previous_failed_owned_log']), qout / 'previous-owned-failure.log.xz')
    for name in ['RECOVERED_CONTEXT.json', 'INCOMING_MODULES.json', 'AGGREGATE_BUILD.json']:
        copy_checked(STAGE / name, qout / name)
    aggregate_build = json.loads((STAGE / 'AGGREGATE_BUILD.json').read_text())
    assert aggregate_build['command']['exit_code'] == 0
    aggregate_log = checked(aggregate_build['command']['log'])
    copy_checked(aggregate_log, qout / aggregate_log.name)
    catalog = dict(qualification['project_closure'])
    assert len(catalog) == 907
    for info in catalog.values():
        selected(info)
    modules, declarations, receipts = {}, [], {}
    for phase in PHASES:
        folder = STAGE / ('verification-' + phase)
        run = json.loads((folder / 'RUN.json').read_text())
        assert run['status'] == 'succeeded' and run['formal_acceptance']
        assert run['P2_6_complete'] is False
        assert {k: run['qualification_parent'][k] for k in ['bytes', 'sha256']} == pin(qpath)
        assert all(x['exit_code'] == 0 for x in run['commands'])
        target = OUT / phase
        target.mkdir(exist_ok=True)
        copy_checked(folder / 'RUN.json', target / 'RUN.json')
        copy_checked(folder / 'owned-declarations.json', target / 'owned-declarations.json')
        for command in run['commands']:
            source = checked(command['log'])
            copy_checked(source, target / source.name)
        owned = json.loads((folder / 'owned-declarations.json').read_text())
        assert len(owned) == run['owned_declarations']
        declarations.extend(owned)
        for module, count in run['owned_counts'].items():
            assert module not in modules
            modules[module] = count
        for module, info in run['project_closure'].items():
            obj = selected(info)
            if module in catalog:
                assert info['source'] == catalog[module]['source']
                assert {k: obj[k] for k in ['bytes', 'sha256']} == {k: selected(catalog[module])[k] for k in ['bytes', 'sha256']}
            else:
                catalog[module] = info
        receipts[phase] = pin(target / 'RUN.json')
    assert len(modules) == 19 and len(catalog) == 926
    assert len(declarations) == len({x['name'] for x in declarations})
    for item in declarations:
        assert not (item['unsafe'] or item['partial'] or item['axiom'])
        assert set(item['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
        assert '⋯' not in item['type']
    external_path = ROOT / 'tools/p26/analytic-closure/verify_external_inputs.py'
    spec = importlib.util.spec_from_file_location('p26_final_cell00_external_readback', external_path)
    external = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(external)
    external.OUT = STAGE / 'FINAL_EXTERNAL_READBACK.json'
    external.main()
    readback = json.loads(external.OUT.read_text())
    assert readback['status'] == 'matched' and not readback['problems']
    analytic = json.loads((ROOT / 'docs/verification/20261128-p26-higher-moments/RUN.json').read_text())
    assert readback['plan'] == analytic['external_inputs_after']['plan']
    copy_checked(external.OUT, OUT / external.OUT.name)
    copy_checked(STAGE / 'SEPARATION_PROPOSAL.json', OUT / 'SEPARATION_PROPOSAL.json')
    (OUT / 'owned-declarations.json').write_text(json.dumps(declarations, indent=2) + '\n')
    members = {}
    for module in sorted(set(modules) | {AGGREGATE}):
        members['objects/' + module.replace('.', '/') + '.olean'] = checked(selected(catalog[module]))
    assert len(members) == 20
    archive = OUT / 'project-objects.tar.xz'
    with tarfile.open(archive, 'w:xz', preset=6) as tar:
        for name, path in sorted(members.items()):
            raw = path.read_bytes()
            info = tarfile.TarInfo(name)
            info.size, info.mode, info.mtime = len(raw), 0o644, 0
            tar.addfile(info, io.BytesIO(raw))
    with tarfile.open(archive, 'r:xz') as tar:
        assert len(tar.getmembers()) == 20
        for item in tar:
            assert tar.extractfile(item).read() == members[item.name].read_bytes()
    receipt = {'schema': 'p26_original_cell00_integral_capsule_v1',
               'formal_acceptance': True, 'P2_6_complete': False,
               'original_full_snapshot_verified': False,
               'scope': 'Original Cell00 finite certificates qualified in the accepted current analytic context, actual simplex packing and original source-cell integral lower bound.',
               'exact_bound': '1055527309463438251 / 2^96 <= integral(cell 0, conservativeDensity)',
               'original_rows': 56, 'separated_pairs': 1540,
               'original_vertices': 28, 'source_gates': 97,
               'current_supplier_replayed_modules': 468,
               'current_supplier_owned_declarations': 28059,
               'shared_serialized_equation_occurrences': 229,
               'shared_proof_bodies_independently_kernel_checked': 229,
               'different_shared_proof_bodies_kernel_checked': 1,
               'complete_serialized_occurrences': 28288,
               'current_supplier_normal_rebuilt_modules': 1,
               'leaf_modules': len(modules), 'leaf_owned_declarations': len(declarations),
               'leaf_normal_commands': 19, 'leaf_stock_kernel_commands': 19,
               'leaf_owned_audits': 4, 'project_objects_in_context_union': len(catalog),
               'packaged_project_objects': len(members), 'archive': {'name': archive.name, **pin(archive)},
               'qualification': pin(qout / 'RUN.json'), 'compressed_qualification_evidence': compressed,
               'phases': receipts,
               'parent_capsules': {
                   'cell05_integral': pin(ROOT / 'docs/verification/20261128-p26-cell05-integral/CAPSULE.json'),
                   'analytic': pin(ROOT / 'docs/verification/20261128-p26-higher-moments/CAPSULE.json'),
                   'numeric05': pin(ROOT / 'docs/verification/20261128-p26-cell05-numerics/CAPSULE.json')},
               'original_cell00_suppliers': {
                   'git_commit': 'e70a90d15ca73917cc500f4750bb205074fc2dda',
                   'git_branch': 'artifacts/p26-cell00-suppliers-9518e531726e-20261128',
                   'archive_bytes': 30261756,
                   'archive_sha256': '9518e531726e6c1ca0970e7751424469cedea08e702952d22be49584c48d0df6'},
               'original_floor_bridge_evidence': pin(ROOT / 'docs/verification/20261126-p26/cell00-original-floor/evidence.tar.xz'),
               'owned_inventory': pin(OUT / 'owned-declarations.json'),
               'final_external_readback': pin(OUT / 'FINAL_EXTERNAL_READBACK.json'),
               'packager_source': pin(Path(__file__))}
    (OUT / 'CAPSULE.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'status': 'succeeded', 'leaf_modules': len(modules),
                      'leaf_owned_declarations': len(declarations), 'archive': receipt['archive'],
                      'P2_6_complete': False}), flush=True)


if __name__ == '__main__':
    main()
