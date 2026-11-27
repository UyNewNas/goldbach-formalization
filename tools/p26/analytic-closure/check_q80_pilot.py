"""Check one original Q80 equality in the explicitly composed finite context."""
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-numeric05-20261128')
path = ROOT / 'tools/p26/cell05-geometry-certificate/verify.py'
spec = importlib.util.spec_from_file_location('p26_q80_pilot_verifier', path)
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)


def main():
    base = json.loads((STAGE / 'BASE_CONTEXT.json').read_text())
    for receipt in base['parent_receipts']:
        assert verifier.pin(Path(receipt['path'])) == receipt
    for info in base['project_closure'].values():
        for field in ['source', 'selected_object']:
            expected = info[field]
            assert verifier.pin(Path(expected['path'])) == expected
    verifier.OBJECTS = STAGE / 'objects'
    verifier.OUT = STAGE / 'verification-pilot'
    verifier.NAMES = ['P2OriginalSaving19Cell05MomentQ80Pilot']
    verifier.AUDIT_PATH = 'tools/p26/analytic-closure/Q80PilotOwnedAudit.lean'
    verifier.AUDIT_PREFIX = 'P26_Q80_PILOT_AUDIT'
    verifier.SCOPE = ('Original Cell05 row 0 factor 0 stored Q80 equals the unchanged '
                      'prefix evaluator on actual parser-bound coordinates. '
                      'No other factor, complete row, or real integral acceptance.')
    verifier.main()
    target = verifier.OUT / 'RUN.json'
    run = json.loads(target.read_text())
    run['composed_base_context'] = verifier.pin(STAGE / 'BASE_CONTEXT.json')
    run['wrapper_source'] = verifier.pin(Path(__file__))
    target.write_text(json.dumps(run, indent=2) + '\n')


if __name__ == '__main__':
    main()
