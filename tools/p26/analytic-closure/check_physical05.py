"""Verify the original Cell05 physical affine and integral attachment."""
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
path = ROOT / 'tools/p26/analytic-closure/check_higher_encoding.py'
spec = importlib.util.spec_from_file_location('p26_encoding_parent_verifier', path)
parent_verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent_verifier)
verifier = parent_verifier.verifier
STAGE = parent_verifier.STAGE


def main():
    base_path = STAGE / 'BASE_CONTEXT.json'
    base = json.loads(base_path.read_text())
    parent_verifier.validate_base(base)
    parent_path = STAGE / 'verification-encoding/RUN.json'
    parent_pin = verifier.pin(parent_path)
    parent = json.loads(parent_path.read_text())
    assert parent['status'] == 'succeeded'
    assert verifier.pin(base_path) == parent['joined_base']
    for info in parent['project_closure'].values():
        assert verifier.pin(Path(info['source']['path'])) == info['source']
        obj = info.get('new_object', info.get('reused_object'))
        assert obj is not None and verifier.pin(Path(obj['path'])) == obj
    verifier.OBJECTS = STAGE / 'objects'
    verifier.OUT = STAGE / 'verification-physical'
    verifier.NAMES = ['P2OriginalSaving19RationalSimplexBridge',
                      'P2OriginalSaving19Cell05PhysicalMomentRow']
    verifier.AUDIT_PATH = 'tools/p26/analytic-closure/Physical05OwnedAudit.lean'
    verifier.AUDIT_PREFIX = 'P26_PHYSICAL05_AUDIT'
    verifier.SCOPE = ('Original Cell05 physical affine maps from the exact nine rational '
                      'vertices, rational finite encodings, degree-two-through-six actual '
                      'moments, and all 56 stored Q96 lower bounds on the actual simplex '
                      'integrals. No disjointness, source-cell coverage or global endpoint acceptance.')
    verifier.main()
    parent_verifier.validate_base(base)
    assert verifier.pin(parent_path) == parent_pin
    target = verifier.OUT / 'RUN.json'
    run = json.loads(target.read_text())
    run.update(encoding_parent=parent_pin, wrapper_source=verifier.pin(Path(__file__)),
               original_full_snapshot_verified=False)
    target.write_text(json.dumps(run, indent=2) + '\n')


if __name__ == '__main__':
    main()
