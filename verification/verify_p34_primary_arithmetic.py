"""Verify the finite primary arithmetic of the literal signed reciprocal source."""
import sys

sys.dont_write_bytecode = True
from verify_p34_cusp_normalization import ROOT, main

MODULES = tuple("ImbalancedChen." + name for name in (
    "Part3PrimaryPrimeSupport",
    "Part3LiteralReciprocalSource",
    "Part3FixedRhoPrimaryFiniteCore",
    "Part3LiteralPrimaryOldformArithmetic",
))


if __name__ == "__main__":
    main(modules=MODULES, audit="verification/P34PrimaryArithmeticAudit.lean",
         baseline="145be87ff0a88914b607baa2a330bc88105a08d6", description=__doc__,
         scope="Literal signed primary fibres and nonzero grouped beta, with ABL coprimality and integer K=1.",
         output_dir=ROOT / ".lake/p34-primary-arithmetic-acceptance",
         extra_sources=("verification/verify_p34_primary_arithmetic.py",
                        "docs/part3-distribution/p34-20261126/PRIMARY_DECLARATION_MOVES.json"))
