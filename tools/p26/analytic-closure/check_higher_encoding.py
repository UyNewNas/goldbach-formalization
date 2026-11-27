"""Verify Cell05 encoded degree-six moments in accepted joined inputs."""
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-joined05-20261128')
path = ROOT / 'tools/p26/cell05-geometry-certificate/verify.py'
spec = importlib.util.spec_from_file_location('p26_higher_encoding_verifier', path)
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)


def validate_base(base):
    for key in ['analytic_parent', 'normal_parent', 'numeric_parent',
                'native_identity_observation', 'composer_source']:
        item = base[key]
        assert verifier.pin(Path(item['path'])) == item
    analytic = json.loads(Path(base['analytic_parent']['path']).read_text())
    assert analytic['status'] == 'succeeded' and analytic['formal_acceptance']
    assert analytic['fresh_kernel_import_replay_succeeded']
    for info in base['project_closure'].values():
        for key in ['source', 'selected_object']:
            item = info[key]
            assert verifier.pin(Path(item['path'])) == item
    for info in base['native_artifacts']:
        item = info['selected']
        assert verifier.pin(Path(item['path'])) == item
    observed = json.loads(Path(base['native_identity_observation']['path']).read_text())
    for info in observed['nodes'].values():
        actual = verifier.pin(Path(info['source']))
        assert all(actual[k] == info['actual_source'][k] for k in ['bytes', 'sha256'])
    for item in base['runtime'].values():
        assert verifier.pin(Path(item['path'])) == item


def main():
    base_path = STAGE / 'BASE_CONTEXT.json'
    base_pin = verifier.pin(base_path)
    base = json.loads(base_path.read_text())
    validate_base(base)
    verifier.OBJECTS = STAGE / 'objects'
    verifier.OUT = STAGE / 'verification-encoding'
    verifier.NAMES = ['P2OriginalSaving19Cell05HigherMomentEncoding']
    verifier.AUDIT_PATH = 'tools/p26/analytic-closure/HigherEncodingOwnedAudit.lean'
    verifier.AUDIT_PREFIX = 'P26_HIGHER_ENCODING_AUDIT'
    verifier.SCOPE = ('All 56 original Cell05 rows and ten factors: unchanged encoded '
                      'prefix moments equal the original rational moment formula in every '
                      'degree at most six. No physical affine map or integral endpoint acceptance.')
    verifier.main()
    validate_base(base)
    assert verifier.pin(base_path) == base_pin
    target = verifier.OUT / 'RUN.json'
    run = json.loads(target.read_text())
    run.update(joined_base=base_pin, wrapper_source=verifier.pin(Path(__file__)),
               original_full_snapshot_verified=False)
    target.write_text(json.dumps(run, indent=2) + '\n')


if __name__ == '__main__':
    main()
