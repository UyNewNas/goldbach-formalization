"""Join verified physical rows and finite separating forms for Cell05."""
import importlib.util
import json
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parents[3]
path = ROOT / 'tools/p26/analytic-closure/check_higher_encoding.py'
spec = importlib.util.spec_from_file_location('p26_packing05_parent_verifier', path)
parent_verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent_verifier)
verifier = parent_verifier.verifier
STAGE = parent_verifier.STAGE


def object_pin(info):
    item = info.get('new_object', info.get('reused_object'))
    assert item is not None
    assert verifier.pin(Path(info['source']['path'])) == info['source']
    assert verifier.pin(Path(item['path'])) == item
    return item


def main():
    base = json.loads((STAGE / 'BASE_CONTEXT.json').read_text())
    parent_verifier.validate_base(base)
    paths = [STAGE / 'verification-physical/RUN.json',
             Path('/workspace/p26-separation05-20261128/verification/RUN.json')]
    pins = [verifier.pin(path) for path in paths]
    physical, finite = [json.loads(path.read_text()) for path in paths]
    assert physical['status'] == finite['status'] == 'succeeded'
    assert physical['runtime'] == finite['runtime']
    for info in physical['project_closure'].values():
        object_pin(info)
    added = []
    for module, info in finite['project_closure'].items():
        obj = object_pin(info)
        if module in physical['project_closure']:
            other = physical['project_closure'][module]
            assert info['source'] == other['source']
            prior = object_pin(other)
            assert all(prior[k] == obj[k] for k in ['bytes', 'sha256'])
        else:
            assert module.startswith('ImbalancedChen.P2OriginalSaving19Cell05Separation')
            target = STAGE / 'objects' / (module.replace('.', '/') + '.olean')
            target.parent.mkdir(parents=True, exist_ok=True)
            if target.exists():
                assert all(verifier.pin(target)[k] == obj[k] for k in ['bytes', 'sha256'])
            else:
                shutil.copyfile(obj['path'], target)
            added.append({'module': module, 'selected_object': verifier.pin(target)})
    assert len(added) == 16
    verifier.OBJECTS = STAGE / 'objects'
    verifier.OUT = STAGE / 'verification-packing'
    verifier.NAMES = ['P2OriginalSaving19RationalAffineSeparator',
                      'P2OriginalSaving19Cell05Packing']
    verifier.AUDIT_PATH = 'tools/p26/analytic-closure/Packing05OwnedAudit.lean'
    verifier.AUDIT_PREFIX = 'P26_PACKING05_AUDIT'
    verifier.SCOPE = ('All 56 original Cell05 physical simplices are pairwise disjoint '
                      'up to Lebesgue-null proper affine walls. The sum of their stored '
                      'Q96 floors is bounded by the actual integral over their union. '
                      'No source-domain inclusion or global selected-saving endpoint acceptance.')
    verifier.main()
    parent_verifier.validate_base(base)
    assert [verifier.pin(path) for path in paths] == pins
    target = verifier.OUT / 'RUN.json'
    run = json.loads(target.read_text())
    run.update(physical_parent=pins[0], separation_parent=pins[1],
               added_separation_objects=added, wrapper_source=verifier.pin(Path(__file__)),
               original_full_snapshot_verified=False)
    target.write_text(json.dumps(run, indent=2) + '\n')


if __name__ == '__main__':
    main()
