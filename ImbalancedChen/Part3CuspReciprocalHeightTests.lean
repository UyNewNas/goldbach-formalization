import ImbalancedChen.Part3CuspWidthWeakGraphTail
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Changing between raw dy and hyperbolic dy/y² horizontal weak tests uses
actual compact smooth tests β/y². Smoothness at zero is proved from the
positive compact support of β, rather than a false global smoothness
claim for reciprocal height. The literal product-with-density measure
identity gives an exact Bochner integral change of measure.
-/
namespace ImbalancedChen.Part3.CuspReciprocalHeightTests20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a

attribute [local instance] Measure.Subtype.measureSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : LocallyCompactSpace PositiveHeight := isOpen_Ioi.locallyCompactSpace
local instance : IsFiniteMeasureOnCompacts (volume : Measure PositiveHeight) :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
local instance : IsLocallyFiniteMeasure (volume : Measure PositiveHeight) := inferInstance
local instance : SigmaFinite (volume : Measure PositiveHeight) := inferInstance

def reciprocalSquareTest (β : ℝ → ℝ) (t : ℝ) : ℝ := β t / t^2
def squareHeightTest (β : ℝ → ℝ) (t : ℝ) : ℝ := β t * t^2

theorem reciprocalSquareTest_tsupport_subset (β : ℝ → ℝ) :
    tsupport (reciprocalSquareTest β) ⊆ tsupport β := by
  apply closure_minimal _ isClosed_tsupport
  intro t ht
  apply subset_closure
  intro hz
  exact ht (by simp [reciprocalSquareTest, hz])

theorem squareHeightTest_tsupport_subset (β : ℝ → ℝ) :
    tsupport (squareHeightTest β) ⊆ tsupport β := by
  apply closure_minimal _ isClosed_tsupport
  intro t ht
  apply subset_closure
  intro hz
  exact ht (by simp [squareHeightTest, hz])

/-- Reciprocal weighting is genuinely smooth at zero because β vanishes
on an actual neighbourhood of zero. -/
theorem reciprocalSquareTest_smooth {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hs : tsupport β ⊆ Ioi (0 : ℝ)) : ContDiff ℝ ∞ (reciprocalSquareTest β) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    have hz : (0 : ℝ) ∉ tsupport β := by
      intro h
      exact (lt_irrefl (0 : ℝ)) (hs h)
    have he : β =ᶠ[𝓝 (0 : ℝ)] 0 := notMem_tsupport_iff_eventuallyEq.mp hz
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [he] with s hs
    simp [reciprocalSquareTest, hs]
  · exact hβ.contDiffAt.div (contDiffAt_id.pow 2) (pow_ne_zero 2 ht)

theorem reciprocalSquareTest_compact {β : ℝ → ℝ} (hc : HasCompactSupport β) :
    HasCompactSupport (reciprocalSquareTest β) :=
  hc.of_isClosed_subset isClosed_tsupport (reciprocalSquareTest_tsupport_subset β)

theorem squareHeightTest_smooth {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (squareHeightTest β) := hβ.mul (contDiff_id.pow 2)

theorem squareHeightTest_compact {β : ℝ → ℝ} (hc : HasCompactSupport β) :
    HasCompactSupport (squareHeightTest β) :=
  hc.of_isClosed_subset isClosed_tsupport (squareHeightTest_tsupport_subset β)

/-- Literal density identity on the physical tail. No chart Jacobian or
unidentified measure is assumed. -/
theorem functionMeasure_eq_raw_withDensity (a : ℝ) :
    functionMeasure a = (derivativeMeasure a).withDensity
      (fun z : CuspCylinder => (heightDensity z.2 : ℝ≥0∞)) := by
  have hprod : cylinderMeasure = rawCylinderMeasure.withDensity
      (fun z : CuspCylinder => (heightDensity z.2 : ℝ≥0∞)) :=
    Measure.prod_withDensity_right heightDensity_continuous.measurable.coe_nnreal_ennreal
  rw [functionMeasure, hprod, restrict_withDensity (strictCylinderTail_measurable a)]
  rfl

theorem density_times_test (β : ℝ → ℝ) (y : PositiveHeight) :
    (heightDensity y : ℝ) * β (y : ℝ) = reciprocalSquareTest β (y : ℝ) := by
  rw [heightDensity_coe, reciprocalSquareTest]
  rw [div_pow, one_pow]
  ring

theorem density_times_squareHeightTest (β : ℝ → ℝ) (y : PositiveHeight) :
    (heightDensity y : ℝ) * squareHeightTest β (y : ℝ) = β (y : ℝ) := by
  rw [heightDensity_coe, squareHeightTest]
  have hy : (y : ℝ) ≠ 0 := y.property.ne'
  field_simp [hy] <;> ring

/-- Exact conversion of one actual weighted-cylinder tensor integral to
a raw-cylinder integral with the genuine reciprocal-square height test. -/
theorem weighted_tensor_integral_eq_raw (a : ℝ) (β : ℝ → ℝ)
    (φ : UnitAddCircle → ℂ) (H : CuspCylinder → ℂ) :
    (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * H z ∂functionMeasure a) =
      ∫ z : CuspCylinder, (reciprocalSquareTest β (z.2 : ℝ) : ℂ) * φ z.1 * H z
        ∂derivativeMeasure a := by
  rw [functionMeasure_eq_raw_withDensity,
    integral_withDensity_eq_integral_smul
      (heightDensity_continuous.measurable.comp measurable_snd)]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    calc
      heightDensity z.2 • ((β (z.2 : ℝ) : ℂ) * φ z.1 * H z) =
          (((heightDensity z.2 : ℝ) * β (z.2 : ℝ) : ℝ) : ℂ) * φ z.1 * H z := by
        simp only [NNReal.smul_def, Complex.real_smul, Complex.ofReal_mul]
        ring
      _ = _ := by rw [density_times_test]

/-- The inverse conversion uses the polynomial test β*y², so no
singularity at zero enters this direction. -/
theorem raw_tensor_integral_eq_weighted (a : ℝ) (β : ℝ → ℝ)
    (φ : UnitAddCircle → ℂ) (H : CuspCylinder → ℂ) :
    (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * H z ∂derivativeMeasure a) =
      ∫ z : CuspCylinder, (squareHeightTest β (z.2 : ℝ) : ℂ) * φ z.1 * H z
        ∂functionMeasure a := by
  rw [weighted_tensor_integral_eq_raw]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    have h := density_times_squareHeightTest β z.2
    rw [density_times_test] at h
    rw [h]

end
end ImbalancedChen.Part3.CuspReciprocalHeightTests20261026b
