"""Verify the literal coprime packet, its fixed-height cusp pairing and the scalar oldform phase."""
import sys

sys.dont_write_bytecode = True
from verify_p34_cusp_normalization import ROOT, main

MODULES = tuple("ImbalancedChen." + name for name in (
    "Part3FourierModeIndex",
    "Part3CoprimePacketCore",
    "Part3CuspPhaseCore",
    "Part3Gamma0ActualCusps",
    "Part3CuspScalingMatrices",
    "Part3ActualCuspWidthNormalization",
    "Part3CuspTranslationFourierPhase",
    "Part3ActualCuspFourierSection",
    "Part3SignedCuspFourierSection",
    "Part3CoprimePacketCoefficients",
    "Part3ActualCuspScalingSourceOnly",
    "Part3ActualCuspPacketPairing",
    "Part3OldformCuspPhase",
))


if __name__ == "__main__":
    main(modules=MODULES, audit="verification/P34CuspPacketAudit.lean",
         baseline="f3bea5b5ffde5f7d8a3ecef3e6759121abaab92e", description=__doc__,
         scope="Literal coprime packet and fixed-height cusp pairing, including scalar oldform phases. P3.4 remains incomplete.",
         output_dir=ROOT / ".lake/p34-packet-acceptance",
         extra_sources=("verification/verify_p34_cusp_packet.py",
                        "docs/part3-distribution/p34-20261126/DECLARATION_MOVES.json"))
