"""Compose accepted analytic and numeric contexts with identical overlap.

Execution is gated on successful from-empty replay of the analytic parent.
Only its byte-verified native artifacts are copied into the joined snapshot.
"""
import hashlib
import json
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parents[3]
PRIMARY = Path('/workspace/p26-analytic-closure-20261127')
NUMERIC = ROOT / 'docs/verification/20261128-p26-cell05-numerics/q96/RUN.json'
OUT = Path('/workspace/p26-joined05-20261128')


def pin(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data),
            'sha256': hashlib.sha256(data).hexdigest()}


def same_bytes(actual, expected):
    return all(actual[key] == expected[key] for key in ['bytes', 'sha256'])


def main():
    parent_path = PRIMARY / 'verification/RUN.json'
    parent = json.loads(parent_path.read_text())
    assert parent['status'] == 'succeeded' and parent['formal_acceptance']
    assert parent['fresh_kernel_import_replay_succeeded']
    normal_path = PRIMARY / 'RUN.json'
    assert pin(normal_path) == parent['normal_build']
    normal = json.loads(normal_path.read_text())
    numeric = json.loads(NUMERIC.read_text())
    assert numeric['status'] == 'succeeded'
    assert parent['runtime'] == numeric['runtime']
    catalog, overlap = {}, []
    for record in normal['commands']:
        assert record['exit_code'] == 0
        catalog[record['module']] = {'source': record['source'], 'object': record['object']}
    for module, info in numeric['project_closure'].items():
        obj = info.get('new_object', info.get('reused_object'))
        assert obj is not None
        if module in catalog:
            assert catalog[module]['source'] == info['source']
            assert same_bytes(catalog[module]['object'], obj)
            overlap.append(module)
        else:
            catalog[module] = {'source': info['source'], 'object': obj}
    assert len(catalog) == 417 and len(overlap) == 3
    objects = OUT / 'objects'

    def copy_checked(source, expected, target):
        assert same_bytes(pin(source), expected)
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists():
            assert same_bytes(pin(target), expected)
        else:
            shutil.copyfile(source, target)
        return pin(target)

    for module, info in catalog.items():
        assert pin(Path(info['source']['path'])) == info['source']
        info['selected_object'] = copy_checked(Path(info['object']['path']), info['object'],
            objects / (module.replace('.', '/') + '.olean'))
    external = parent['external_inputs_after']
    assert external['status'] == 'matched' and not external['problems']
    plan_path = Path(external['plan']['path'])
    assert pin(plan_path) == external['plan']
    plan = json.loads(plan_path.read_text())
    native_root = Path(normal['lean_path'].split(':')[-1])
    native_artifacts = []
    for name, expected in plan['required_files'].items():
        if expected['role'] == 'qualified-native-artifact':
            source = Path(name)
            selected = copy_checked(source, expected, objects / source.relative_to(native_root))
            native_artifacts.append({'original': name, 'selected': selected})
    assert len(native_artifacts) == external['role_counts']['qualified-native-artifact'] == 555
    observed_path = PRIMARY / 'SELECTED_NATIVE_INPUTS.json'
    observed = json.loads(observed_path.read_text())
    for info in observed['nodes'].values():
        assert same_bytes(pin(Path(info['source'])), info['actual_source'])
    result = {'schema': 'p26_joined05_accepted_context_composition_v1',
              'formal_acceptance': False, 'P2_6_complete': False,
              'analytic_parent': pin(parent_path), 'normal_parent': pin(normal_path),
              'numeric_parent': pin(NUMERIC), 'runtime': parent['runtime'],
              'project_closure': catalog, 'identical_overlap': overlap,
              'objects': str(objects), 'native_artifacts': native_artifacts,
              'native_identity_observation': pin(observed_path),
              'original_full_snapshot_verified': False,
              'composer_source': pin(Path(__file__))}
    (OUT / 'BASE_CONTEXT.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'project_modules': len(catalog), 'identical_overlap': len(overlap),
                      'qualified_native_files': len(native_artifacts), 'formal_acceptance': False}))


if __name__ == '__main__':
    main()
