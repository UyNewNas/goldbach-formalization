"""Compile original floor and physical owners after the full finite join."""
import argparse
import importlib.util
import json
from pathlib import Path

import prepare_finite_join as preparer
import qualify_finite_join as qualifier

ROOT = Path(__file__).resolve().parents[3]
JOIN = Path('/workspace/p26-cell01-finite-join-20261128')
HERE = Path(__file__).resolve().parent
FLOORS = [f'P2OriginalSaving19Cell01OriginalFloorBlock{a:03d}_{a+15:03d}'
          for a in range(0, 144, 16)] + [
              'P2OriginalSaving19Cell01AllOriginalFloorBridge',
              'P2OriginalSaving19Cell01AllRowArithmetic']
PHASES = {'floors': FLOORS,
          'physical': ['P2OriginalSaving19Cell01PhysicalMomentRow',
                       'P2OriginalSaving19Cell01GroupedSeparationComplete'],
          'packing': ['P2OriginalSaving19Cell01Packing'],
          'source': ['P2OriginalSaving19Cell01SourceAttachment']}
ORDER = list(PHASES)


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check_catalog(catalog):
    for info in catalog.values():
        preparer.check(info['source'])
        obj = info.get('selected_object', info.get('new_object', info.get('reused_object')))
        assert obj is not None
        preparer.check(obj)


def main(phase):
    wrapper_pin = preparer.pin(Path(__file__))
    out = JOIN / ('verification-' + phase)
    assert not out.exists(), 'Preserve every passed step and failed attempt.'
    join_path = JOIN / 'qualification/RUN.json'
    join_pin = preparer.pin(join_path)
    joined = json.loads(join_path.read_text())
    assert joined['status'] == 'succeeded' and joined['formal_acceptance']
    assert joined['owned_modules'] == 143 and joined['owned_declarations'] == 41184
    assert joined['shared_serialized_occurrences'] == 572
    preparer.check(joined['verifier_source'])
    context_path = Path(joined['recovered_context']['path'])
    assert preparer.pin(context_path) == joined['recovered_context']
    context = json.loads(context_path.read_text())
    qualifier.validate(context)
    expected_catalog = dict(joined['project_closure'])
    assert expected_catalog == context['project_closure'] and len(expected_catalog) == 1484
    prior = ORDER[:ORDER.index(phase)]
    prior_pins = []
    previous_context_path = JOIN / 'CURRENT_ACCEPTED_CONTEXT.json'
    for previous in prior:
        previous_run_path = JOIN / ('verification-' + previous) / 'RUN.json'
        previous_pin = preparer.pin(previous_run_path)
        previous_run = json.loads(previous_run_path.read_text())
        assert previous_run['status'] == 'succeeded' and previous_run['formal_acceptance']
        assert previous_run['finite_join_parent'] == join_pin
        assert previous_run['accepted_parent'] == preparer.pin(previous_context_path)
        previous_context = json.loads(previous_context_path.read_text())
        assert previous_context['project_closure'] == expected_catalog
        for key in ['native_artifacts', 'runtime', 'lean_path']:
            assert previous_context[key] == context[key]
        for key in ['wrapper_source', 'audit_source', 'verifier_source']:
            preparer.check(previous_run[key])
        assert previous_run['wrapper_source'] == wrapper_pin
        previous_modules = ['ImbalancedChen.' + name for name in PHASES[previous]]
        assert set(previous_run['project_closure']) <= set(expected_catalog) | set(previous_modules)
        for module, info in previous_run['project_closure'].items():
            if module not in previous_modules:
                assert info['source'] == expected_catalog[module]['source']
                assert info['reused_object'] == expected_catalog[module]['selected_object']
        for module in previous_modules:
            info = previous_run['project_closure'][module]
            expected_catalog[module] = {'source': info['source'], 'selected_object': info['new_object'],
                                       'origin': 'accepted-cell01-' + previous}
        prior_pins.append(previous_pin)
        previous_context_path = previous_run_path.parent / 'CURRENT_ACCEPTED_CONTEXT.json'
    parent_path = previous_context_path
    parent_pin = preparer.pin(parent_path)
    parent = json.loads(parent_path.read_text())
    assert parent['formal_acceptance'] and not parent['P2_6_complete']
    assert parent['project_closure'] == expected_catalog
    for key in ['native_artifacts', 'runtime', 'lean_path']:
        assert parent[key] == context[key]
    if not prior: assert parent['qualification_parent'] == join_pin
    else: assert parent['phase_parent'] == prior_pins[-1]
    check_catalog(parent['project_closure'])
    names = PHASES[phase]
    modules = ['ImbalancedChen.' + name for name in names]
    assert not set(modules) & set(parent['project_closure'])
    imports = preparer.BASE_IMPORTS + [preparer.module_name(r) for r in range(1, 144)]
    for previous in prior: imports += ['ImbalancedChen.' + n for n in PHASES[previous]]
    imports += modules
    source = (HERE / 'OwnedSuppliersAudit.lean').read_text()
    source = ''.join('import ' + n + '\n' for n in imports) + source[source.index('import Lean.Util.CollectAxioms'):]
    start = source.index('  for moduleName in #[')
    end = source.index('] do\n    let some idx', start)
    source = source[:start] + '  for moduleName in #[\n' + ',\n'.join('      `' + n for n in modules) + source[end:]
    prefix = 'P26_CELL01_' + phase.upper() + '_AUDIT'
    source = source.replace('P26_CELL01_SUPPLIER_AUDIT', prefix).replace(
        'p26Cell01SharedProofBodyCheck', 'p26Cell01' + phase.title() + 'SharedProofBodyCheck')
    if phase == 'source':
        source += '''
open MeasureTheory in
example :
    (((282451447802500037895 : ℚ) / (2 : ℚ)^96 : ℚ) : ℝ) ≤
      ∫ t in ImbalancedChen.OriginalAscendingThirteenCellOwnership.cell 1,
        ImbalancedChen.P2OriginalThirdMinorantLogDictionarySourceOnly.conservativeDensity t :=
  ImbalancedChen.P2OriginalSaving19Cell01SourceAttachment.concrete_cell_integral_bound
'''
    audit = HERE / (phase.title() + 'OwnedAudit.lean')
    if audit.exists(): assert audit.read_text() == source
    else: audit.write_text(source)
    audit_pin = preparer.pin(audit)
    helper = ROOT / 'tools/p26/cell05-geometry-certificate/verify.py'
    helper_pin = preparer.pin(helper)
    fixed_parent = json.loads(preparer.PARENT.read_text())
    core_run = json.loads(Path(fixed_parent['phase_parents']['core']['path']).read_text())
    assert helper_pin == core_run['verifier_source']
    verifier = load('cell01_' + phase + '_leaf_verifier', helper)
    verifier.OBJECTS, verifier.OUT = JOIN / 'objects', out
    verifier.NAMES = names
    verifier.AUDIT_PATH = str(audit.relative_to(ROOT))
    verifier.AUDIT_PREFIX = prefix
    verifier.SCOPE = {
        'floors': 'All144 original floor/Q80 transports and all144 original row-data certificates; physical/source integral endpoint remains open.',
        'physical': 'All144 actual simplex saved-Q96 bounds and original hierarchy physical pairwise almost-everywhere disjointness; packing/source integral remains open.',
        'packing': 'All144 actual simplex integrals pack into their union integral with the original saved-Q96 sum; source-cell inclusion remains open.',
        'source': 'All97 original gates at all40 original vertices, proper null walls, actual cell1 inclusion and bound282451447802500037895/2^96. Other original families/globalP2.6 remain open.',
    }[phase]
    verifier.main()
    run_path = out / 'RUN.json'
    run = json.loads(run_path.read_text())
    assert run['status'] == 'succeeded'
    inventories, owned, shared, completes, imported = {}, {}, {}, {}, []
    for line in (out / 'joined-owned.log').read_text().splitlines():
        if not line.startswith(prefix + '_'): continue
        tag, raw = line.split(' ', 1)
        item = json.loads(raw)
        if tag.endswith('_IMPORTS'):
            imported.append(item)
        elif tag.endswith('_INVENTORY'):
            assert item['module'] not in inventories
            inventories[item['module']] = item
        elif tag.endswith('_DECL') or tag.endswith('_SHARED'):
            assert item['module'] in modules
            assert not (item['unsafe'] or item['partial'] or item['axiom'])
            assert set(item['axioms']) <= qualifier.ALLOWED and '⋯' not in item['type']
            records = shared if tag.endswith('_SHARED') else owned
            records.setdefault(item['module'], []).append(item)
            if tag.endswith('_SHARED'):
                assert item['identical_metadata'] and item['proof_body_kernel_checked']
                assert item['canonical_module'] in parent['project_closure'] or item['canonical_module'] in modules
                assert item['canonical_module'] != item['module']
        elif tag.endswith('_COMPLETE'):
            assert item['module'] not in completes
            completes[item['module']] = item
    assert set(inventories) == set(completes) == set(modules)
    assert len(imported) == 1
    assert {m for m in imported[0] if m.startswith('ImbalancedChen.')} == set(expected_catalog) | set(modules)
    assert set(owned) | set(shared) <= set(modules)
    all_names = [item['name'] for entries in owned.values() for item in entries]
    assert len(all_names) == len(set(all_names)) == run['owned_declarations']
    for module, inv in inventories.items():
        canonical = sorted(item['name'] for item in owned.get(module, []))
        aliases = sorted(item['name'] for item in shared.get(module, []))
        assert canonical == sorted(inv['environment']) and aliases == sorted(inv['shared'])
        assert sorted(inv['serialized']) == sorted(canonical + aliases)
        assert len(inv['serialized']) == len(set(inv['serialized']))
        assert not set(canonical) & set(aliases)
        assert completes[module] == {'module': module, 'count': len(canonical),
            'shared_count': len(aliases), 'serialized_count': len(canonical) + len(aliases)}
    external = load('cell01_' + phase + '_external', ROOT / 'tools/p26/analytic-closure/verify_external_inputs.py')
    preparer.check(context['external_verifier_source'])
    external.OUT = out / 'FINAL_EXTERNAL_READBACK.json'
    external.main()
    report = json.loads(external.OUT.read_text())
    assert report['status'] == 'matched' and report['problems'] == []
    assert report['plan'] == context['external_plan'] and report['unique_physical_files_hashed'] == 54309
    qualifier.validate(context)
    check_catalog(parent['project_closure']); check_catalog(run['project_closure'])
    assert preparer.pin(parent_path) == parent_pin and preparer.pin(join_path) == join_pin
    assert preparer.pin(context_path) == joined['recovered_context']
    assert preparer.pin(Path(__file__)) == wrapper_pin
    assert preparer.pin(audit) == audit_pin and preparer.pin(helper) == helper_pin
    for item in prior_pins: preparer.check(item)
    assert set(run['project_closure']) <= set(expected_catalog) | set(modules)
    for module, info in run['project_closure'].items():
        if module not in modules:
            assert info['source'] == expected_catalog[module]['source']
            assert info['reused_object'] == expected_catalog[module]['selected_object']
    run.update(formal_acceptance=True, finite_join_parent=join_pin, accepted_parent=parent_pin,
        wrapper_source=wrapper_pin, original_full_snapshot_verified=False,
        final_external_readback=preparer.pin(external.OUT),
        shared_serialized_occurrences=sum(map(len, shared.values())))
    run_path.write_text(json.dumps(run, indent=2) + '\n')
    catalog = dict(parent['project_closure'])
    for module in modules:
        info = run['project_closure'][module]
        catalog[module] = {'source': info['source'], 'selected_object': info['new_object'],
                           'origin': 'accepted-cell01-' + phase}
    successor = {'formal_acceptance': True, 'P2_6_complete': False,
        'original_full_snapshot_verified': False, 'phase_parent': preparer.pin(run_path),
        'accepted_parent': parent_pin, 'project_closure': catalog,
        'native_artifacts': parent['native_artifacts'], 'runtime': parent['runtime'], 'lean_path': parent['lean_path']}
    (out / 'CURRENT_ACCEPTED_CONTEXT.json').write_text(json.dumps(successor, indent=2) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase', choices=PHASES)
    main(parser.parse_args().phase)
