"""Verify all 560 original Q80 fields using the unchanged finite evaluator."""
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-numeric05-20261128')
path = ROOT / 'tools/p26/cell05-geometry-certificate/verify.py'
spec = importlib.util.spec_from_file_location('p26_q80_complete_verifier', path)
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)


def main():
    base = json.loads((STAGE / 'BASE_CONTEXT.json').read_text())
    pilot_path = STAGE / 'verification-pilot/RUN.json'
    pilot = json.loads(pilot_path.read_text())
    assert pilot['status'] == 'succeeded'
    for receipt in base['parent_receipts']:
        assert verifier.pin(Path(receipt['path'])) == receipt
    for module, info in pilot['project_closure'].items():
        assert verifier.pin(Path(info['source']['path'])) == info['source']
        expected = info.get('new_object', info.get('reused_object'))
        assert expected is not None and verifier.pin(Path(expected['path'])) == expected
    verifier.OBJECTS = STAGE / 'objects'
    verifier.OUT = STAGE / 'verification-complete'
    verifier.NAMES = [f'P2OriginalSaving19Cell05MomentQ80Block{i:03d}' for i in range(14)]
    verifier.NAMES.append('P2OriginalSaving19Cell05MomentQ80Complete')
    verifier.AUDIT_PATH = 'tools/p26/analytic-closure/Q80CompleteOwnedAudit.lean'
    verifier.AUDIT_PREFIX = 'P26_Q80_COMPLETE_AUDIT'
    verifier.SCOPE = ('All 56 original Cell05 rows and all ten stored Q80 factor '
                      'values equal the unchanged prefix evaluator on actual coordinates. '
                      'No stored Q96 or real integral acceptance.')
    verifier.main()
    target = verifier.OUT / 'RUN.json'
    run = json.loads(target.read_text())
    run['composed_base_context'] = verifier.pin(STAGE / 'BASE_CONTEXT.json')
    run['pilot_receipt'] = verifier.pin(pilot_path)
    run['wrapper_source'] = verifier.pin(Path(__file__))
    target.write_text(json.dumps(run, indent=2) + '\n')


if __name__ == '__main__':
    main()
