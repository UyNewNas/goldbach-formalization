"""Verify all original Cell05 Q96 records after the complete Q80 certificate."""
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-numeric05-20261128')
path = ROOT / 'tools/p26/cell05-geometry-certificate/verify.py'
spec = importlib.util.spec_from_file_location('p26_q96_record_verifier', path)
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)


def main():
    parent_path = STAGE / 'verification-complete/RUN.json'
    parent = json.loads(parent_path.read_text())
    assert parent['status'] == 'succeeded'
    for info in parent['project_closure'].values():
        assert verifier.pin(Path(info['source']['path'])) == info['source']
        expected = info.get('new_object', info.get('reused_object'))
        assert expected is not None and verifier.pin(Path(expected['path'])) == expected
    verifier.OBJECTS = STAGE / 'objects'
    verifier.OUT = STAGE / 'verification-q96'
    verifier.NAMES = ['P2OriginalSaving19Cell05MomentQ96RecordChecks']
    verifier.AUDIT_PATH = 'tools/p26/analytic-closure/Q96RecordOwnedAudit.lean'
    verifier.AUDIT_PREFIX = 'P26_Q96_RECORD_AUDIT'
    verifier.SCOPE = ('All 56 original Cell05 new Q96 records equal the unchanged '
                      'evaluator on actual coordinates, using the 560 original Q80 equalities; '
                      'old Q96 geometry alignment and saved monotonicity. No integral endpoint acceptance.')
    verifier.main()
    target = verifier.OUT / 'RUN.json'
    run = json.loads(target.read_text())
    run['complete_Q80_receipt'] = verifier.pin(parent_path)
    run['wrapper_source'] = verifier.pin(Path(__file__))
    target.write_text(json.dumps(run, indent=2) + '\n')


if __name__ == '__main__':
    main()
