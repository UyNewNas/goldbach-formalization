"""Verify original Cell05 source gates and the source-cell integral bound."""
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
path = ROOT / 'tools/p26/analytic-closure/check_higher_encoding.py'
spec = importlib.util.spec_from_file_location('p26_source05_parent_verifier', path)
parent_verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parent_verifier)
verifier = parent_verifier.verifier
STAGE = parent_verifier.STAGE


def main():
    base = json.loads((STAGE / 'BASE_CONTEXT.json').read_text())
    parent_verifier.validate_base(base)
    parent_path = STAGE / 'verification-packing/RUN.json'
    parent_pin = verifier.pin(parent_path)
    parent = json.loads(parent_path.read_text())
    assert parent['status'] == 'succeeded'
    for info in parent['project_closure'].values():
        assert verifier.pin(Path(info['source']['path'])) == info['source']
        obj = info.get('new_object', info.get('reused_object'))
        assert obj is not None and verifier.pin(Path(obj['path'])) == obj
    verifier.OBJECTS = STAGE / 'objects'
    verifier.OUT = STAGE / 'verification-source'
    verifier.NAMES = ['P2OriginalSaving19Cell05SourceAttachment']
    verifier.AUDIT_PATH = 'tools/p26/analytic-closure/Source05OwnedAudit.lean'
    verifier.AUDIT_PREFIX = 'P26_SOURCE05_AUDIT'
    verifier.SCOPE = ('All 97 original Cell05 source gates hold at all 28 original '
                      'vertices; all proper source walls are null; the 56 actual '
                      'simplices lie in original cell 5 almost everywhere; the sum '
                      'of its original Q96 floors bounds its actual cell integral '
                      'from below. No other source cell or global endpoint acceptance.')
    verifier.main()
    parent_verifier.validate_base(base)
    assert verifier.pin(parent_path) == parent_pin
    target = verifier.OUT / 'RUN.json'
    run = json.loads(target.read_text())
    run.update(packing_parent=parent_pin, wrapper_source=verifier.pin(Path(__file__)),
               original_full_snapshot_verified=False)
    target.write_text(json.dumps(run, indent=2) + '\n')


if __name__ == '__main__':
    main()
