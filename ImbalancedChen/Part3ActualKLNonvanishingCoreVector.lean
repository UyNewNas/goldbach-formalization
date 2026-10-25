import ImbalancedChen.Part3ActualKLCoreTransform
import ImbalancedChen.Part3ActualKLNonvanishingTest

/-!
CODE_ONLY / SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The actual compact bump whose literal K transform is entire and nonzero
almost everywhere is bound here to the genuine raw KL L² quotient and
the actual physical-core linear transform. Both the weighted-measure
nonvanishing statement and membership in the exact actual core-map range
are derived, rather than assumed. No isometry extension, invariant range,
Plancherel identity or surjectivity is supplied by this module.
-/

namespace ImbalancedChen.Part3.ActualKLNonvanishingCoreVector20261025a

noncomputable section
open MeasureTheory
open ActualKLCoreTransform20261025a ActualKLCoordinateMeasures20261025a
open ActualKLNonvanishingTest20261025a

/-- A concrete actual L² vector, from the fixed compact smooth bump. -/
def rawKLNonvanishingVector : RawTauL2 := rawKLTestTransform nonvanishingTest

theorem rawKLNonvanishingVector_coe_ae :
    (rawKLNonvanishingVector : ℝ → ℂ) =ᵐ[tauMeasure]
      ActualKLCompactTestIntegrationByParts20261025a.actualKtransform nonvanishingTest.function :=
  rawKLTestTransform_ae nonvanishingTest

/-- Nonvanishing for the genuine raw tauMeasure quotient, using the
proved entire-transform zero theorem and the literal density equality. -/
theorem rawKLNonvanishingVector_nonzero_ae :
    ∀ᵐ tau : ℝ ∂tauMeasure, rawKLNonvanishingVector tau ≠ 0 := by
  have hactual : ∀ᵐ tau : ℝ ∂tauMeasure,
      ActualKLCompactTestIntegrationByParts20261025a.actualKtransform nonvanishingTest.function tau ≠ 0 := by
    simpa only [tauMeasure, positiveDensityMeasure, tauDensity] using
      actualKtransform_test_nonzero_rawKL_ae
  filter_upwards [rawKLNonvanishingVector_coe_ae, hactual] with tau hrep hnonzero
  rwa [hrep]

/-- The same explicit vector belongs to the range of the actual raw KL
core linear map, with the physical compact-bump vector as its witness. -/
theorem rawKLNonvanishingVector_mem_coreRange :
    rawKLNonvanishingVector ∈ LinearMap.range actualCoreKLTransform :=
  ⟨physicalCoreVector nonvanishingTest, actualCoreKLTransform_on_test nonvanishingTest⟩

theorem actualCoreKLTransform_nonvanishingTest :
    actualCoreKLTransform (physicalCoreVector nonvanishingTest) = rawKLNonvanishingVector :=
  actualCoreKLTransform_on_test nonvanishingTest

end
end ImbalancedChen.Part3.ActualKLNonvanishingCoreVector20261025a
