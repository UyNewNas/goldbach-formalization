"""Verify the original common completed-variable weight in finite dyadic assembly."""
import sys

sys.dont_write_bytecode = True
from verify_p34_cusp_normalization import ROOT, main

MODULES = tuple("ImbalancedChen." + name for name in (
    "Part3FourierModeIndex",
    "Part3CoprimePacketCore",
    "Part3CuspPhaseCore",
    "Part3CoprimePacketCoefficients",
    "Part3PrimaryPrimeSupport",
    "Part3LiteralReciprocalSource",
    "Part3FixedRhoPrimaryFiniteCore",
    "Part3PrimaryDyadicShortEndpoint",
    "Part3PrimaryDyadicAssembly",
    "Part3CommonCompletedVariableCore",
    "Part3PrimaryDyadicCommonAssembly",
))


if __name__ == "__main__":
    main(modules=MODULES, audit="verification/P34CommonPhaseAudit.lean",
         baseline="b945f39a1e355ff4fcca9865ab59ffc97f2172c0", description=__doc__,
         scope="Common completed-variable phase in exact finite dyadic source and beta assembly "
               "and the short primary packet.",
         output_dir=ROOT / ".lake/p34-common-phase-acceptance",
         extra_sources=("verification/verify_p34_common_phase.py",
                        "docs/part3-distribution/p34-common-phase-20261126/DECLARATION_MOVES.json"))
