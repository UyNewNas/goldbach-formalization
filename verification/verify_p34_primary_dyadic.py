"""Verify the exact finite dyadic assembly and short primary endpoint."""
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
))


if __name__ == "__main__":
    main(modules=MODULES, audit="verification/P34PrimaryDyadicAudit.lean",
         baseline="2b284342fce23962a1b431d8003cb5cdffac8128", description=__doc__,
         scope="Exact computed output-key source and beta-energy assembly and the short coprime index endpoint.",
         output_dir=ROOT / ".lake/p34-primary-dyadic-acceptance",
         extra_sources=("verification/verify_p34_primary_dyadic.py",
                        "docs/part3-distribution/p34-20261126/DYADIC_DECLARATION_MOVES.json"))
