"""Check Cell00 leaves only after their current supplier join is accepted."""
import argparse
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-cell00-next-20261128')


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


verifier = load('p26_cell00_leaf_verifier', ROOT / 'tools/p26/cell05-geometry-certificate/verify.py')
qualifier = load('p26_cell00_qualification', ROOT / 'tools/p26/cell00-integral/qualify_suppliers.py')
PREFIX = 'P2OriginalSaving19Cell00'
PHASES = {
    'grouped05': {
        'names': ['P2OriginalSaving19Cell05GroupedSeparation' + s for s in ['Data', 'Signs', 'Complete']],
        'parents': ['grouped'],
        'scope': 'All 56 original Cell05 physical simplices are pairwise almost-everywhere disjoint by 61 exact sibling-cone separators composed over 49 branching nodes; no other original family accepted.'},
    'grouped': {
        'names': ['P2OriginalSaving19GroupedSeparation'], 'parents': [],
        'scope': 'Generic sound composition of rational sibling-group separators into pairwise almost-everywhere disjoint actual simplex families; no original pulling-tree data accepted.'},
    'physical': {
        'names': [PREFIX + 'PhysicalMomentRow'], 'parents': [],
        'scope': 'All 56 actual Cell00 affine simplices, their original moments through degree six, and their saved max(old,new) Q96 integral lower bounds.'},
    'separation': {
        'names': [PREFIX + 'SeparationData'] + [PREFIX + f'SeparationBlock{i:03d}' for i in range(14)] + [PREFIX + 'SeparationComplete'],
        'parents': [],
        'scope': 'Proper rational affine separators for all 1540 pairs, with all 18 vertex signs proved on the original parser-bound Cell00 coordinates.'},
    'packing': {
        'names': [PREFIX + 'Packing'], 'parents': ['physical', 'separation'],
        'scope': 'Pairwise almost-everywhere disjointness of all 56 actual Cell00 simplices and the stored Q96 sum bounded by the integral on their union.'},
    'source': {
        'names': [PREFIX + 'SourceAttachment'], 'parents': ['packing'],
        'scope': 'All 97 original gates at all 28 vertices, null proper source walls, almost-everywhere inclusion in cell 0, and the exact cell integral bound 1055527309463438251 / 2^96.'},
}


def validate_project(run):
    for info in run['project_closure'].values():
        assert verifier.pin(Path(info['source']['path'])) == info['source']
        obj = info.get('selected_object', info.get('new_object', info.get('reused_object')))
        assert obj is not None and verifier.pin(Path(obj['path'])) == obj


def main(phase):
    qualification_path = STAGE / 'qualification/RUN.json'
    qualification_pin = verifier.pin(qualification_path)
    qualification = json.loads(qualification_path.read_text())
    assert qualification['status'] == 'succeeded' and qualification['formal_acceptance']
    assert qualification['owned_modules'] == 468 and qualification['owned_declarations'] == 28059
    assert qualification['kernel_join']['kernel_replay_succeeded']
    context_path = Path(qualification['recovered_context']['path'])
    assert verifier.pin(context_path) == qualification['recovered_context']
    context = json.loads(context_path.read_text())
    qualifier.validate(context)
    validate_project(qualification)
    spec = PHASES[phase]
    parents = {}
    for name in spec['parents']:
        path = STAGE / ('verification-' + name) / 'RUN.json'
        parents[name] = verifier.pin(path)
        parent = json.loads(path.read_text())
        assert parent['status'] == 'succeeded' and parent['formal_acceptance']
        assert parent['qualification_parent'] == qualification_pin
        assert parent['runtime'] == qualification['runtime']
        validate_project(parent)
    verifier.OBJECTS = STAGE / 'objects'
    verifier.OUT = STAGE / ('verification-' + phase)
    verifier.NAMES = spec['names']
    verifier.AUDIT_PATH = 'tools/p26/cell00-integral/' + phase.title() + 'OwnedAudit.lean'
    verifier.AUDIT_PREFIX = 'P26_CELL00_' + phase.upper() + '_AUDIT'
    verifier.SCOPE = spec['scope'] + ' No other cell or global P2.6 endpoint acceptance.'
    if verifier.OUT.exists():
        existing = json.loads((verifier.OUT / 'RUN.json').read_text())
        assert existing['status'] != 'succeeded', 'Do not repeat a passed phase.'
        attempt = 1
        while verifier.OUT.with_name(verifier.OUT.name + f'-attempt-{attempt:03d}').exists():
            attempt += 1
        verifier.OUT.rename(verifier.OUT.with_name(verifier.OUT.name + f'-attempt-{attempt:03d}'))
    verifier.main()
    target = verifier.OUT / 'RUN.json'
    run = json.loads(target.read_text())
    assert run['status'] == 'succeeded' and run['runtime'] == qualification['runtime']
    assert run['lean_path'] == qualification['lean_path']
    qualifier.validate(context)
    validate_project(qualification)
    validate_project(run)
    assert verifier.pin(qualification_path) == qualification_pin
    for name, item in parents.items():
        assert verifier.pin(Path(item['path'])) == item
        validate_project(json.loads(Path(item['path']).read_text()))
    run.update(formal_acceptance=True, qualification_parent=qualification_pin,
               phase_parents=parents, wrapper_source=verifier.pin(Path(__file__)),
               original_full_snapshot_verified=False)
    target.write_text(json.dumps(run, indent=2) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase', choices=PHASES)
    main(parser.parse_args().phase)
