"""Qualify Cell01 selectors and exact sibling signs after supplier replay."""
import importlib.util
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-cell01-next-20261128')
NAMES = ['P2OriginalSaving19Cell01OriginalFloorInterface',
         'P2OriginalSaving19Cell01GroupedSeparationData',
         'P2OriginalSaving19Cell01GroupedSeparationSigns']


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    qualifier = load('cell01_supplier_qualifier', ROOT / 'tools/p26/cell01-integral/qualify_suppliers.py')
    verifier = load('cell01_leaf_verifier', ROOT / 'tools/p26/cell05-geometry-certificate/verify.py')
    external = load('cell01_external_verifier', ROOT / 'tools/p26/analytic-closure/verify_external_inputs.py')
    pin = qualifier.pin
    parent_path = STAGE / 'qualification/RUN.json'
    parent_pin, parent = pin(parent_path), json.loads(parent_path.read_text())
    assert parent['status'] == 'succeeded' and parent['formal_acceptance']
    assert parent['owned_modules'] == 407 and parent['kernel_join']['kernel_replay_succeeded']
    context_path = Path(parent['recovered_context']['path'])
    assert pin(context_path) == parent['recovered_context']
    context = json.loads(context_path.read_text())
    qualifier.validate(context)
    generic_path = STAGE / 'generic-transport/RUN.json'
    generic_pin, generic = pin(generic_path), json.loads(generic_path.read_text())
    assert generic['status'] == 'succeeded' and generic['formal_acceptance']
    assert generic['owned_declarations'] == 16
    for key in ['source', 'object', 'audit_source']:
        assert pin(Path(generic[key]['path'])) == generic[key]
    generic_obj = Path(generic['object']['path'])
    target = STAGE / 'objects/ImbalancedChen/P2OriginalSaving19OriginalFloorTransport.olean'
    if not target.exists(): os.link(generic_obj, target)
    assert pin(target)['sha256'] == generic['object']['sha256']
    verifier.OBJECTS = STAGE / 'objects'
    verifier.OUT = STAGE / 'verification-core'
    assert not verifier.OUT.exists(), 'Preserve previous attempts and successful checks.'
    verifier.NAMES = NAMES
    verifier.AUDIT_PATH = 'tools/p26/cell01-integral/CoreOwnedAudit.lean'
    verifier.AUDIT_PREFIX = 'P26_CELL01_CORE_AUDIT'
    verifier.SCOPE = ('Original Fin144 selector/no-fallback interface and all165 rational sibling separators '
        'on the original Cell01 vertices; no full physical separation, cell integral or P2.6 endpoint.')
    verifier.main()
    run_path = verifier.OUT / 'RUN.json'
    run = json.loads(run_path.read_text())
    assert run['status'] == 'succeeded'
    # Independently reconcile every serialized declaration, rather than only counts.
    inventories, declarations, completed = {}, {}, {}
    for line in (verifier.OUT / 'joined-owned.log').read_text().splitlines():
        if not line.startswith(verifier.AUDIT_PREFIX + '_'): continue
        tag, raw = line.split(' ', 1)
        item = json.loads(raw)
        if tag.endswith('_INVENTORY'):
            assert item['module'] not in inventories
            assert sorted(item['serialized']) == sorted(item['environment'])
            assert len(item['serialized']) == len(set(item['serialized']))
            inventories[item['module']] = item
        elif tag.endswith('_DECL'):
            assert '⋯' not in item['type']
            declarations.setdefault(item['module'], []).append(item['name'])
        elif tag.endswith('_COMPLETE'):
            assert item['module'] not in completed
            completed[item['module']] = item['count']
    assert set(inventories) == set(declarations) == set(completed) == {'ImbalancedChen.' + n for n in NAMES}
    for module, inv in inventories.items():
        assert sorted(declarations[module]) == sorted(inv['serialized'])
        assert completed[module] == len(declarations[module])
    external.OUT = verifier.OUT / 'FINAL_EXTERNAL_READBACK.json'
    external.main()
    report = json.loads(external.OUT.read_text())
    assert report['status'] == 'matched' and report['unique_physical_files_hashed'] == 54309
    qualifier.validate(context)
    assert pin(parent_path) == parent_pin and pin(generic_path) == generic_pin
    for key in ['source', 'object', 'audit_source']:
        assert pin(Path(generic[key]['path'])) == generic[key]
    run.update(formal_acceptance=True, qualification_parent=parent_pin,
        generic_transport_parent=generic_pin, original_full_snapshot_verified=False,
        final_external_readback=pin(external.OUT), wrapper_source=pin(Path(__file__)))
    run_path.write_text(json.dumps(run, indent=2) + '\n')


if __name__ == '__main__':
    main()
