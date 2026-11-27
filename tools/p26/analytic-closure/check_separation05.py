"""Verify finite original Cell05 separators in the accepted pure context."""
import importlib.util
import json
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-separation05-20261128')
PARENT = ROOT / 'docs/verification/20261128-p26-cell05-numerics/q96/RUN.json'
path = ROOT / 'tools/p26/cell05-geometry-certificate/verify.py'
spec = importlib.util.spec_from_file_location('p26_separation05_verifier', path)
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)


def main():
    parent_pin = verifier.pin(PARENT)
    parent = json.loads(PARENT.read_text())
    assert parent['status'] == 'succeeded'
    objects = STAGE / 'objects'
    selected = {}
    for module, info in parent['project_closure'].items():
        assert verifier.pin(Path(info['source']['path'])) == info['source']
        obj = info.get('new_object', info.get('reused_object'))
        assert obj is not None and verifier.pin(Path(obj['path'])) == obj
        target = objects / (module.replace('.', '/') + '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists():
            assert all(verifier.pin(target)[k] == obj[k] for k in ['bytes', 'sha256'])
        else:
            shutil.copyfile(obj['path'], target)
        selected[module] = {'source': info['source'], 'object': verifier.pin(target)}
    assert len(selected) == 192
    verifier.OBJECTS = objects
    verifier.OUT = STAGE / 'verification'
    prefix = 'P2OriginalSaving19Cell05Separation'
    verifier.NAMES = [prefix + 'Data'] + [prefix + f'Block{i:03d}' for i in range(14)] + [prefix + 'Complete']
    verifier.AUDIT_PATH = 'tools/p26/analytic-closure/Separation05OwnedAudit.lean'
    verifier.AUDIT_PREFIX = 'P26_SEPARATION05_AUDIT'
    verifier.SCOPE = ('Proper affine separating forms for all 1,540 original Cell05 '
                      'simplex pairs, with all 18 vertex signs verified on actual '
                      'parser-bound rational coordinates. No measure or integral claim.')
    verifier.main()
    assert verifier.pin(PARENT) == parent_pin
    for info in selected.values():
        for item in info.values():
            assert verifier.pin(Path(item['path'])) == item
    target = verifier.OUT / 'RUN.json'
    run = json.loads(target.read_text())
    run.update(pure_numeric_parent=parent_pin, wrapper_source=verifier.pin(Path(__file__)),
               original_full_snapshot_verified=False)
    target.write_text(json.dumps(run, indent=2) + '\n')


if __name__ == '__main__':
    main()
