"""Verify the installed actual source and common phase in finite dyadic assembly."""
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
    "Part3MediumAtomCore",
    "Part3ActualNonzeroSourceCore",
    "Part3PrimaryDyadicActualMode",
))


if __name__ == "__main__":
    main(modules=MODULES, audit="verification/P34PrimaryActualModeAudit.lean",
         baseline="b945f39a1e355ff4fcca9865ab59ffc97f2172c0", description=__doc__,
         scope="Actual finite-source short endpoints and beta energy, with the common "
               "completed-variable finite dyadic phase.",
         output_dir=ROOT / ".lake/p34-primary-actual-mode-acceptance",
         extra_sources=("verification/verify_p34_primary_actual_mode.py",
                        "docs/part3-distribution/p34-common-phase-20261126/ACTUAL_DECLARATION_MOVES.json",
                        "docs/part3-distribution/p34-common-phase-20261126/DECLARATION_MOVES.json"))
