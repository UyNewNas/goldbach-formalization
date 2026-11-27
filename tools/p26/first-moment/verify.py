"""Reuse the normal/kernel/full-owned verifier with this task's exact owners."""
import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True

path = Path(__file__).resolve().parents[1] / 'cell05-geometry-certificate/verify.py'
spec = importlib.util.spec_from_file_location('p26_join_verifier', path)
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)
verifier.OUT = verifier.ROOT / 'docs/verification/20261127-p26-first-moment'
verifier.AUDIT_PATH = 'tools/p26/first-moment/OwnedAudit.lean'
verifier.SCOPE = ('Cell05 quantitative factor mean/deviation bounds and exact existing prefix '
                  'algorithm degrees zero/one on actual rational coordinates; '
                  'no higher-moment integral or original stored new-floor acceptance')
verifier.NAMES = [
    'P2Winner9HomogeneousRecurrence',
    'P2OriginalSaving19PrefixInterface',
    'P2OriginalSaving19PrefixMoments',
    'P2OriginalSaving19FiniteWeightedMean',
    'P2OriginalSaving19NonnegativeRationalEncoding',
    'P2OriginalSaving19PrefixFirstMoment',
    'P2OriginalSaving19Cell05MomentBounds',
]

if __name__ == '__main__':
    verifier.main()
