import ImbalancedChen.Part3CuspWeakCylinderFourierModes
import ImbalancedChen.Part3ClosedHorizontalCuspTail

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Physical mixed-measure cusp-tail vectors have an actual common weighted
cylinder realization: the value is in Haar×dy/y² and the derivative in
Haar×dy. On y>a>0 the latter embeds into weighted L² with the explicit
bound a⁻² on measures. Zero extension introduces no horizontal boundary
term. Genuine tensor weak tests on this physical tail therefore imply
the all-integer Fourier derivative equation on one common AE height set.

The distributional convention below uses the actual weighted measure on
the tail, independent of the horizontal variable. It does not assert a
conversion from a separately supplied raw-dy distributional convention,
nor a global quotient-to-cusp graph theorem.
-/
namespace ImbalancedChen.Part3.CuspPhysicalWeakTailModes20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal NNReal
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open ClosedHorizontalCuspTail20261026a ActualCylinderModeEmbeddings20261026a
open ActualCylinderFourierCoefficients20261026a
open CuspWeakCylinderFourierModes20261026b

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
attribute [local instance] Measure.Subtype.measureSpace

local instance : LocallyCompactSpace PositiveHeight := isOpen_Ioi.locallyCompactSpace
local instance : IsFiniteMeasureOnCompacts (volume : Measure PositiveHeight) :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
local instance : IsLocallyFiniteMeasure (volume : Measure PositiveHeight) := inferInstance
local instance : SigmaFinite (volume : Measure PositiveHeight) := inferInstance

def tailWeightBound (a : ℝ) : ℝ≥0 := ⟨(1 / a)^2, sq_nonneg _⟩

/-- The explicit mixed-measure comparison on a genuinely positive tail. -/
theorem weighted_height_tail_le_raw {a : ℝ} (ha : 0 < a) :
    heightMeasure.restrict (strictHeightTail a) ≤
      (tailWeightBound a : ℝ≥0∞) •
        (volume : Measure PositiveHeight).restrict (strictHeightTail a) := by
  rw [heightMeasure, restrict_withDensity (strictHeightTail_measurable a)]
  calc
    _ ≤ ((volume : Measure PositiveHeight).restrict (strictHeightTail a)).withDensity
        (fun _ => (tailWeightBound a : ℝ≥0∞)) := by
      apply withDensity_mono
      filter_upwards [ae_restrict_mem (strictHeightTail_measurable a)] with y hy
      apply ENNReal.coe_le_coe.mpr
      change heightDensity y ≤ tailWeightBound a
      change (heightDensity y : ℝ) ≤ (tailWeightBound a : ℝ)
      rw [heightDensity_coe]
      exact pow_le_pow_left₀ (by positivity)
        (one_div_le_one_div_of_le ha (le_of_lt hy)) 2
    _ = _ := withDensity_const _

theorem functionMeasure_le_derivativeMeasure {a : ℝ} (ha : 0 < a) :
    functionMeasure a ≤ (tailWeightBound a : ℝ≥0∞) • derivativeMeasure a := by
  have h := Measure.prod_mono (μ := AddCircle.haarAddCircle)
    (μ' := AddCircle.haarAddCircle) le_rfl (weighted_height_tail_le_raw ha)
  rw [Measure.prod_smul_right] at h
  simpa only [functionMeasure, derivativeMeasure, rawCylinderMeasure,
    ← Measure.prod_restrict, Measure.restrict_univ, strictCylinderTail, cylinderMeasure] using h

def tailValue (a : ℝ) (u : FunctionL2 a) : CylinderL2 :=
  ((memLp_indicator_iff_restrict (strictCylinderTail_measurable a)).mpr (Lp.memLp u)).toLp
    ((strictCylinderTail a).indicator u)

def tailDerivative (a : ℝ) (ha : 0 < a) (d : DerivativeL2 a) : CylinderL2 :=
  ((memLp_indicator_iff_restrict (strictCylinderTail_measurable a)).mpr
    ((Lp.memLp d).of_measure_le_smul (by simp)
      (functionMeasure_le_derivativeMeasure ha))).toLp ((strictCylinderTail a).indicator d)

theorem tailValue_ae (a : ℝ) (u : FunctionL2 a) :
    (tailValue a u : CuspCylinder → ℂ) =ᵐ[cylinderMeasure]
      (strictCylinderTail a).indicator u :=
  ((memLp_indicator_iff_restrict (strictCylinderTail_measurable a)).mpr (Lp.memLp u)).coeFn_toLp

theorem tailDerivative_ae (a : ℝ) (ha : 0 < a) (d : DerivativeL2 a) :
    (tailDerivative a ha d : CuspCylinder → ℂ) =ᵐ[cylinderMeasure]
      (strictCylinderTail a).indicator d :=
  ((memLp_indicator_iff_restrict (strictCylinderTail_measurable a)).mpr
    ((Lp.memLp d).of_measure_le_smul (by simp)
      (functionMeasure_le_derivativeMeasure ha))).coeFn_toLp

private theorem zero_extension_test_integral (a : ℝ)
    (H : CylinderL2) (h : CuspCylinder → ℂ)
    (hH : (H : CuspCylinder → ℂ) =ᵐ[cylinderMeasure] (strictCylinderTail a).indicator h)
    (k : CuspCylinder → ℂ) :
    (∫ z, k z * H z ∂cylinderMeasure) = ∫ z, k z * h z ∂functionMeasure a := by
  calc
    _ = ∫ z, (strictCylinderTail a).indicator (fun z => k z * h z) z
        ∂cylinderMeasure := by
      apply integral_congr_ae
      filter_upwards [hH] with z hz
      rw [hz]
      by_cases hzt : z ∈ strictCylinderTail a <;> simp [hzt]
    _ = _ := integral_indicator (strictCylinderTail_measurable a)

/-- Width-normalized physical distributional derivative. For width w,
the derivative in the unit circle coordinate is w times the physical one. -/
def HasWeakPhysicalTailDerivative (w a : ℝ) (u : FunctionL2 a) (d : DerivativeL2 a) : Prop :=
  ∀ φ ψ : C(UnitAddCircle, ℂ),
    ContDiff ℝ ∞ (fun t : ℝ => φ (t : UnitAddCircle)) →
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => φ (s : UnitAddCircle))
      (ψ (t : UnitAddCircle)) t) →
    ∀ β : ℝ → ℝ, ContDiff ℝ ∞ β → HasCompactSupport β →
      tsupport β ⊆ Ioi (0 : ℝ) →
      (∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * φ z.1 * ((w : ℂ) * d z)
        ∂functionMeasure a) =
      -(∫ z : CuspCylinder, (β (z.2 : ℝ) : ℂ) * ψ z.1 * u z ∂functionMeasure a)

theorem physical_tail_native_weak {w a : ℝ} (ha : 0 < a)
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (hweak : HasWeakPhysicalTailDerivative w a u d) :
    HasWeakWeightedCylinderDerivative (tailValue a u)
      ((w : ℂ) • tailDerivative a ha d) := by
  intro φ ψ hφ hd β hβ hc hs
  have hDa : (((w : ℂ) • tailDerivative a ha d : CylinderL2) : CuspCylinder → ℂ)
      =ᵐ[cylinderMeasure] (strictCylinderTail a).indicator (fun z => (w : ℂ) * d z) := by
    filter_upwards [Lp.coeFn_smul (w : ℂ) (tailDerivative a ha d),
      tailDerivative_ae a ha d] with z hz hdz
    simp only [hz, Pi.smul_apply, smul_eq_mul, hdz]
    by_cases hzt : z ∈ strictCylinderTail a <;> simp [hzt]
  rw [zero_extension_test_integral a _ _ hDa,
    zero_extension_test_integral a _ _ (tailValue_ae a u)]
  exact hweak φ ψ hφ hd β hβ hc hs

theorem physical_tail_all_modes_ae {w a : ℝ} (ha : 0 < a)
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (hweak : HasWeakPhysicalTailDerivative w a u d) :
    ∀ᵐ y ∂heightMeasure, ∀ n : ℤ,
      sliceCoefficient n ((w : ℂ) • tailDerivative a ha d) y =
        modeFrequency n * sliceCoefficient n (tailValue a u) y :=
  weak_cylinder_all_modes_ae (physical_tail_native_weak ha hweak)

/-- Positive density makes the SAME all-frequency assertion true for raw
dy-almost every height; no uncountable intersection is used. -/
theorem heightMeasure_ae_iff_volume {P : PositiveHeight → Prop} :
    (∀ᵐ y ∂heightMeasure, P y) ↔ ∀ᵐ y ∂(volume : Measure PositiveHeight), P y := by
  rw [heightMeasure, ae_withDensity_iff
    heightDensity_continuous.measurable.coe_nnreal_ennreal]
  constructor
  · intro h
    filter_upwards [h] with y hy
    exact hy (ENNReal.coe_ne_zero.mpr (heightDensity_pos y).ne')
  · intro h
    filter_upwards [h] with y hy
    intro _
    exact hy

theorem physical_tail_all_modes_raw_ae {w a : ℝ} (ha : 0 < a)
    {u : FunctionL2 a} {d : DerivativeL2 a}
    (hweak : HasWeakPhysicalTailDerivative w a u d) :
    ∀ᵐ y ∂(volume : Measure PositiveHeight), ∀ n : ℤ,
      sliceCoefficient n ((w : ℂ) • tailDerivative a ha d) y =
        modeFrequency n * sliceCoefficient n (tailValue a u) y :=
  heightMeasure_ae_iff_volume.mp (physical_tail_all_modes_ae ha hweak)

end
end ImbalancedChen.Part3.CuspPhysicalWeakTailModes20261026b
