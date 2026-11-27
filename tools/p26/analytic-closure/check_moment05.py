"""Run normal/kernel/full-owned checks of the complete original Cell05 input."""
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-moment05-20261128')
path = ROOT / 'tools/p26/cell05-geometry-certificate/verify.py'
spec = importlib.util.spec_from_file_location('p26_cell_verifier', path)
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)


def main():
    normal = json.loads((STAGE / 'RUN.json').read_text())
    assert normal['status'] == 'normal_build_succeeded_not_formally_accepted'
    assert len(normal['nodes']) == len(normal['commands']) == 43
    raw = normal['original_raw_input']
    assert verifier.pin(Path(raw['path'])) == raw
    for command in normal['commands']:
        assert command['exit_code'] == 0
        for key in ['source', 'object']:
            assert verifier.pin(Path(command[key]['path'])) == command[key]
    verifier.OUT = STAGE / 'verification'
    verifier.OBJECTS = STAGE / 'objects'
    verifier.NAMES = [module.removeprefix('ImbalancedChen.')
                      for module in normal['topological_order']
                      if module.startswith('ImbalancedChen.P2OriginalSaving19Moment05')
                      or module == 'ImbalancedChen.P2OriginalSaving19ArchiveMomentData05']
    assert len(verifier.NAMES) == 36
    verifier.AUDIT_PATH = 'tools/p26/analytic-closure/Moment05OwnedAudit.lean'
    verifier.AUDIT_PREFIX = 'P26_MOMENT05_AUDIT'
    verifier.SCOPE = ('Byte-bound original Cell05 moment input: complete pure JSON parse, '
                      'original typed decode, all 56 row IDs and ten Q80 fields per row; '
                      'no saved floor inequality or integral bound acceptance')
    verifier.main()
    assert verifier.pin(Path(raw['path'])) == raw
    receipt = verifier.OUT / 'RUN.json'
    run = json.loads(receipt.read_text())
    run['original_raw_input'] = raw
    run['fresh_normal_build'] = verifier.pin(STAGE / 'RUN.json')
    run['wrapper_source'] = verifier.pin(Path(__file__))
    receipt.write_text(json.dumps(run, indent=2) + '\n')


if __name__ == '__main__':
    main()
