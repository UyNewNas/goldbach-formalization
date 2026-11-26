"""Verify the original normalized cusp-one chart and its literal Fricke Fourier phase."""
import sys

sys.dont_write_bytecode = True
from verify_p34_cusp_normalization import ROOT, main

MODULES = tuple("ImbalancedChen." + name for name in (
    "Part3CuspPhaseCore",
    "Part3Gamma0ActualCusps",
    "Part3CuspScalingMatrices",
    "Part3ActualCuspWidthNormalization",
    "Part3CuspTranslationFourierPhase",
    "Part3ActualCuspFourierSection",
    "Part3FrickeNormalizer",
    "Part3Gamma0GeneralCuspWidth",
    "Part3Gamma0GeneralCuspUnitPeriod",
    "Part3ActualFrickeCuspPhase",
))


if __name__ == "__main__":
    main(modules=MODULES, audit="verification/P34FrickePhaseAudit.lean",
         baseline="da576de2c91df467d1865baee9c1b1b84ddc529b", description=__doc__,
         scope="Original width-normalized cusp-one chart and literal Fricke phase at fixed height. "
               "P3.4 and historical D20 remain incomplete.",
         output_dir=ROOT / ".lake/p34-fricke-phase-acceptance",
         extra_sources=("verification/verify_p34_fricke_phase.py",
                        "docs/part3-distribution/p34-fricke-phase-20261126/SOURCE_INTAKE.json"))
