import ImbalancedChen.Part3CuspCylinderMeasure
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Tactic

/-!
# Actual positive-height measure in scaled logarithmic coordinates

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

This uses the existing PositiveHeight subtype and literal native height
measure dy/y^2.  The full nonnegative-integral Jacobian is established,
not just an identity for compact smooth test functions.  Positivity of
the radial density then gives the two nonsingular coordinate maps needed
for arbitrary Lp quotient representatives.
-/

namespace ImbalancedChen.Part3.WeightedHeightLogMeasure20261026a

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
open CuspCylinderMeasure20261024z
attribute [local instance] Measure.Subtype.measureSpace

def scaledHeightEquiv (a : ℝ) (ha : 0 < a) : ℝ ≃ᵐ PositiveHeight where
  toFun r := ⟨Real.exp r / a, div_pos (Real.exp_pos r) ha⟩
  invFun y := Real.log (a * (y : ℝ))
  left_inv r := by
    change Real.log (a * (Real.exp r / a)) = r
    have h : a * (Real.exp r / a) = Real.exp r := by field_simp [ha.ne']; ring
    rw [h, Real.log_exp]
  right_inv y := by
    apply Subtype.ext
    change Real.exp (Real.log (a * (y : ℝ))) / a = y
    rw [Real.exp_log (mul_pos ha y.property)]
    field_simp [ha.ne']
  measurable_toFun := ((Real.continuous_exp.div_const a).subtype_mk _).measurable
  measurable_invFun := Real.measurable_log.comp (measurable_const.mul measurable_subtype_coe)

@[simp] theorem scaledHeightEquiv_coe (a : ℝ) (ha : 0 < a) (r : ℝ) :
    (scaledHeightEquiv a ha r : ℝ) = Real.exp r / a := rfl

@[simp] theorem scaledHeightEquiv_symm (a : ℝ) (ha : 0 < a) (y : PositiveHeight) :
    (scaledHeightEquiv a ha).symm y = Real.log (a * (y : ℝ)) := rfl

def radialHeightDensity (a r : ℝ) : ℝ := a * Real.exp (-r)

theorem radialHeightDensity_pos {a : ℝ} (ha : 0 < a) (r : ℝ) :
    0 < radialHeightDensity a r := mul_pos ha (Real.exp_pos _)

theorem radialHeightDensity_continuous (a : ℝ) : Continuous (radialHeightDensity a) := by
  unfold radialHeightDensity
  fun_prop

def radialHeightMeasure (a : ℝ) : Measure ℝ :=
  volume.withDensity (fun r => ENNReal.ofReal (radialHeightDensity a r))

private def heightExtension (q : PositiveHeight → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  if hy : 0 < y then q ⟨y, hy⟩ else 0

private theorem height_lintegral_as_positive_axis (q : PositiveHeight → ℝ≥0∞) :
    (∫⁻ y, q y ∂heightMeasure) = ∫⁻ y in Ioi (0 : ℝ),
      ENNReal.ofReal ((1 / y) ^ 2) * heightExtension q y := by
  unfold heightMeasure
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _
    heightDensity_continuous.measurable.coe_nnreal_ennreal
    (Eventually.of_forall (fun _ => ENNReal.coe_lt_top))]
  calc
    _ = ∫⁻ y : PositiveHeight,
        ENNReal.ofReal ((1 / (y : ℝ)) ^ 2) * heightExtension q y := by
      apply lintegral_congr
      intro y
      simp only [heightExtension, dif_pos y.property]
      rw [← heightDensity_coe]
      simp
    _ = _ := lintegral_subtype_comap measurableSet_Ioi _

/-- Exact arbitrary-nonnegative-function change of variables for the
original subtype dy/y^2 measure. No integrability assumption is required. -/
theorem height_lintegral_scaled_exp (a : ℝ) (ha : 0 < a)
    (q : PositiveHeight → ℝ≥0∞) :
    (∫⁻ y, q y ∂heightMeasure) = ∫⁻ r : ℝ,
      ENNReal.ofReal (radialHeightDensity a r) * q (scaledHeightEquiv a ha r) := by
  let phi : ℝ → ℝ := fun r => Real.exp r / a
  have hphi (r : ℝ) : 0 < phi r := div_pos (Real.exp_pos r) ha
  have hderiv (r : ℝ) : HasDerivAt phi (phi r) r := (Real.hasDerivAt_exp r).div_const a
  have hinj : InjOn phi univ := by
    intro r _ s _ hrs
    apply Real.exp_injective
    have hh := congrArg (fun x : ℝ => x * a) hrs
    simpa only [phi, div_mul_cancel₀ _ ha.ne'] using hh
  have himage : phi '' univ = Ioi (0 : ℝ) := by
    ext y
    constructor
    · rintro ⟨r, _, rfl⟩
      exact hphi r
    · intro hy
      refine ⟨Real.log (a * y), mem_univ _, ?_⟩
      dsimp only [phi]
      rw [Real.exp_log (mul_pos ha hy)]
      field_simp [ha.ne']
  have hj := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_univ
    (fun r _ => (hderiv r).hasDerivWithinAt) hinj
    (fun y : ℝ => ENNReal.ofReal ((1 / y) ^ 2) * heightExtension q y)
  rw [himage, Measure.restrict_univ] at hj
  rw [height_lintegral_as_positive_axis, hj]
  apply lintegral_congr
  intro r
  have hweight : phi r * (1 / phi r) ^ 2 = radialHeightDensity a r := by
    unfold radialHeightDensity phi
    rw [Real.exp_neg]
    field_simp [ha.ne', (Real.exp_pos r).ne']
    <;> ring
  simp only [heightExtension, dif_pos (hphi r), abs_of_pos (hphi r)]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (hphi r).le, hweight]
  rfl

theorem scaledHeightEquiv_map_radialHeightMeasure (a : ℝ) (ha : 0 < a) :
    Measure.map (scaledHeightEquiv a ha) (radialHeightMeasure a) = heightMeasure := by
  apply Measure.ext_of_lintegral
  intro q hq
  rw [lintegral_map hq (scaledHeightEquiv a ha).measurable]
  unfold radialHeightMeasure
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (radialHeightDensity_continuous a).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  exact (height_lintegral_scaled_exp a ha q).symm

theorem scaledHeightEquiv_measurePreserving (a : ℝ) (ha : 0 < a) :
    MeasurePreserving (scaledHeightEquiv a ha) (radialHeightMeasure a) heightMeasure :=
  ⟨(scaledHeightEquiv a ha).measurable, scaledHeightEquiv_map_radialHeightMeasure a ha⟩

theorem radial_volume_absolutelyContinuous_height (a : ℝ) (ha : 0 < a) :
    (volume : Measure ℝ) ≪ radialHeightMeasure a := by
  apply withDensity_absolutelyContinuous'
    (radialHeightDensity_continuous a).measurable.ennreal_ofReal.aemeasurable
  exact Eventually.of_forall (fun r => (ENNReal.ofReal_pos.mpr (radialHeightDensity_pos ha r)).ne')

/-- Nonsingularity for arbitrary HEIGHT Lp representatives pulled to r. -/
theorem scaledHeightEquiv_quasiMeasurePreserving (a : ℝ) (ha : 0 < a) :
    Measure.QuasiMeasurePreserving (scaledHeightEquiv a ha) volume heightMeasure :=
  (scaledHeightEquiv_measurePreserving a ha).quasiMeasurePreserving.mono_left
    (radial_volume_absolutelyContinuous_height a ha)

/-- Nonsingularity for arbitrary RADIAL Lp representatives pulled to y. -/
theorem scaledHeightEquiv_symm_quasiMeasurePreserving (a : ℝ) (ha : 0 < a) :
    Measure.QuasiMeasurePreserving (scaledHeightEquiv a ha).symm heightMeasure volume :=
  (MeasurePreserving.symm (scaledHeightEquiv a ha)
    (scaledHeightEquiv_measurePreserving a ha)).quasiMeasurePreserving.mono_right
      (withDensity_absolutelyContinuous _ _)

end
end ImbalancedChen.Part3.WeightedHeightLogMeasure20261026a
