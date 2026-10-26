import ImbalancedChen.Part3ActualKLL2IsometryExtension
import ImbalancedChen.Part3ActualKLExtendedGreenIntertwining
import ImbalancedChen.Part3ActualKLNonvanishingCoreVector
import ImbalancedChen.Part3ActualKLCoordinateIndicatorBridge

/-!
CODE_ONLY / SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The actual raw KL transform is surjective. Its independently constructed
native isometry has closed range. Actual half-shift Green intertwining
makes that range stable under multiplication by (1/4+tau²)^(-1).
The actual-coordinate measurable-inverse theorem then supplies EVERY
measurable indicator truncation. The genuine compact-bump image is in
the range and is nonzero tauMeasure-almost everywhere, so the proved L²
indicator-cyclicity theorem makes this actual range the full raw space.

Every ingredient refers to the same actual compact K integral, actual
physical L²(dr), and literal density (2/pi²)tau*sinh(pi*tau) on tau>0.
There are no norm, isometry, invariant-range, density or onto premises.
This concerns the raw one-dimensional KL model, not an automorphic
spectral decomposition or a Gamma0 normalization.
-/

namespace ImbalancedChen.Part3.ActualKLOntoUnitary20261025a

noncomputable section
open Set MeasureTheory
open RadialSchrodingerL2Form20261025a
open ActualKLCoreTransform20261025a ActualKLCoordinateMeasures20261025a
open ActualKLL2IsometryExtension20261025a ActualKLExtendedGreenIntertwining20261025a
open ActualKLNonvanishingTest20261025a ActualKLNonvanishingCoreVector20261025a
open ActualKLResolventMultiplier20261025a ActualKLCoordinateIndicatorBridge20261025a
open IndicatorInvariantCyclicDensity20261025a

def actualTransformRange : Submodule ℂ RawTauL2 := actualKLIsometry.toLinearMap.range

theorem actualTransformRange_closed : IsClosed (actualTransformRange : Set RawTauL2) := by
  change IsClosed (Set.range actualKLIsometry)
  exact actualKLRange_closed

theorem rawKLNonvanishingVector_mem_actualTransformRange :
    rawKLNonvanishingVector ∈ actualTransformRange :=
  ⟨radialCoreL2 nonvanishingTest, actualKLIsometry_on_test nonvanishingTest⟩

/-- Stability is derived from the actual full-L² Green intertwining,
with the native half-shift inverse providing a physical preimage. -/
theorem actualTransformRange_coordinate_invariant (u : RawTauL2)
    (hu : u ∈ actualTransformRange) : rawKLResolventMultiplier u ∈ actualTransformRange := by
  obtain ⟨F, rfl⟩ := hu
  exact ⟨halfGreenOperator F, actualKL_halfGreen_intertwine F⟩

/-- Actual range indicator invariance; no such property is a hypothesis. -/
theorem actualTransformRange_indicator_invariant
    (B : Set ℝ) (hB : MeasurableSet B) (u : RawTauL2) (hu : u ∈ actualTransformRange) :
    indicatorMultiplier tauMeasure B hB u ∈ actualTransformRange :=
  rawTau_indicatorMultiplier_mem actualTransformRange actualTransformRange_closed
    actualTransformRange_coordinate_invariant B hB u hu

theorem actualTransformRange_eq_top : actualTransformRange = ⊤ :=
  closed_indicator_invariant_eq_top tauMeasure actualTransformRange actualTransformRange_closed
    actualTransformRange_indicator_invariant rawKLNonvanishingVector
    rawKLNonvanishingVector_mem_actualTransformRange rawKLNonvanishingVector_nonzero_ae

/-- Genuine actual raw-KL surjectivity, with no caller-supplied target
range, density, integral norm or spectral-measure premise. -/
theorem actualKLIsometry_surjective : Function.Surjective actualKLIsometry := by
  intro u
  have hu : u ∈ actualTransformRange := by
    rw [actualTransformRange_eq_top]
    trivial
  exact hu

/-- The native unitary packages the proved onto actual KL isometry. -/
def actualKLUnitary : RadialL2 ≃ₗᵢ[ℂ] RawTauL2 :=
  LinearIsometryEquiv.ofSurjective actualKLIsometry actualKLIsometry_surjective

theorem actualKLUnitary_eq_actualKLIsometry (F : RadialL2) :
    actualKLUnitary F = actualKLIsometry F := rfl

/-- On every actual compact smooth test this remains the literal K_i*tau
integral quotient, rather than a separately chosen abstract unitary. -/
theorem actualKLUnitary_on_test (T : RadialTest) :
    actualKLUnitary (radialCoreL2 T) = rawKLTestTransform T :=
  actualKLIsometry_on_test T

theorem actualKLUnitary_on_test_ae (T : RadialTest) :
    (actualKLUnitary (radialCoreL2 T) : ℝ → ℂ) =ᵐ[tauMeasure]
      ActualKLCompactTestIntegrationByParts20261025a.actualKtransform T.function :=
  actualKLIsometry_on_test_ae T

theorem actualKLUnitary_inverse_on_test (T : RadialTest) :
    actualKLUnitary.symm (rawKLTestTransform T) = radialCoreL2 T := by
  apply actualKLUnitary.injective
  rw [actualKLUnitary.apply_symm_apply, actualKLUnitary_on_test]

theorem actualKLUnitary_halfGreen_intertwine (F : RadialL2) :
    actualKLUnitary (halfGreenOperator F) = rawKLResolventMultiplier (actualKLUnitary F) :=
  actualKL_halfGreen_intertwine F

/-- Native continuous-linear-map conjugacy with the true half-shift
radial Green operator follows from the proved actual unitary. -/
theorem actualKLUnitary_halfGreen_conjugacy :
    actualKLUnitary.toContinuousLinearEquiv.toContinuousLinearMap.comp halfGreenOperator =
      rawKLResolventMultiplier.comp actualKLUnitary.toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  exact actualKLUnitary_halfGreen_intertwine

end
end ImbalancedChen.Part3.ActualKLOntoUnitary20261025a
