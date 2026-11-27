"""Compose the two matching, independently verified finite project contexts.

Every overlapping source and object must be byte-identical. No P2.5 donor,
native project cache, or unverified alternate project search path is used.
"""
import hashlib
import json
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parents[3]
OUT = Path('/workspace/p26-numeric05-20261128')
PARENTS = [ROOT / 'docs/verification/20261127-p26-first-moment/RUN.json',
           ROOT / 'docs/verification/20261128-p26-moment05/RUN.json']


def pin(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest()}


def main():
    catalog, receipts, overlap = {}, [], []
    runtime = None
    for path in PARENTS:
        run = json.loads(path.read_text())
        assert run['status'] == 'succeeded'
        if runtime is None:
            runtime = run['runtime']
        else:
            assert runtime == run['runtime']
        receipts.append(pin(path))
        for module, info in run['project_closure'].items():
            source = ROOT / (module.replace('.', '/') + '.lean')
            assert pin(source) == info['source']
            obj = info.get('new_object', info.get('reused_object'))
            assert obj is not None and pin(Path(obj['path'])) == obj
            if module in catalog:
                previous = catalog[module]
                assert previous['source'] == info['source']
                assert all(previous['object'][k] == obj[k] for k in ['bytes', 'sha256'])
                overlap.append(module)
            else:
                catalog[module] = {'source': info['source'], 'object': obj}
    assert len(catalog) == 175 and len(overlap) == 7
    for expected in runtime.values():
        assert pin(Path(expected['path'])) == expected
    for module, info in catalog.items():
        target = OUT / 'objects' / (module.replace('.', '/') + '.olean')
        target.parent.mkdir(exist_ok=True, parents=True)
        original = Path(info['object']['path'])
        if target.exists():
            assert all(pin(target)[k] == info['object'][k] for k in ['bytes', 'sha256'])
        else:
            shutil.copyfile(original, target)
        info['selected_object'] = pin(target)
    result = {'schema': 'p26_numeric05_identical_overlap_composition_v1',
              'formal_acceptance': False, 'P2_6_complete': False,
              'parent_receipts': receipts, 'runtime': runtime,
              'objects': str(OUT / 'objects'), 'overlap_modules': overlap,
              'project_closure': catalog}
    (OUT / 'BASE_CONTEXT.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'project_modules': len(catalog), 'identical_overlap': len(overlap),
                      'formal_acceptance': False}))


if __name__ == '__main__':
    main()
