import ImbalancedChen.Part3ShiftOneEulerClassification
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The literal physical tail L2(dy/y^2), y>1, selects the decaying member of
the independently proved shift-one Euler basis. The exact pure-power
tail L2 criterion a<1/2 is proved from the actual density and the primary
improper-rpow integrability theorem. Subtracting the genuinely integrable
decaying mode forces the growing coefficient to vanish.

No small-y admissibility or quotient-vector conclusion is asserted.
No old CuspConstantMode/HOLD source is imported.
-/

namespace ImbalancedChen.Part3.ShiftOneEulerTailSelection20261026b
noncomputable section
open Set MeasureTheory Filter
open ShiftOneEulerClassification20261026b

def tailDensity (y : ℝ) : ℝ≥0 := ⟨(y⁻¹) ^ 2, sq_nonneg _⟩

/-- Literal dy/y^2 restricted to y>1, on the real height carrier. -/
def physicalTailMeasure : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Ioi (1 : ℝ))).withDensity
    (fun y => (tailDensity y : ℝ≥0∞))

theorem tailDensity_measurable : Measurable tailDensity := by unfold tailDensity; fun_prop

theorem physicalTailMeasure_height_gt_one : ∀ᵐ y : ℝ ∂physicalTailMeasure, 1 < y := by
  change ∀ᵐ y : ℝ ∂((volume : Measure ℝ).restrict (Ioi (1 : ℝ))).withDensity
    (fun y => (tailDensity y : ℝ≥0∞)), 1 < y
  rw [ae_withDensity_iff tailDensity_measurable.coe_nnreal_ennreal]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact fun _ => hy

theorem eulerPower_tail_density (a : ℝ) {y : ℝ} (hy : 1 < y) :
    (y⁻¹) ^ 2 * ‖eulerPower a y‖ ^ 2 = y ^ (2 * a - 2) := by
  have hy0 : 0 < y := zero_lt_one.trans hy
  rw [eulerPower_eq_rpow a hy0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hy0 a)]
  have hp : y ^ (2 * a) = (y ^ a) ^ 2 := by
    rw [mul_comm 2 a, Real.rpow_mul hy0.le, Real.rpow_natCast]
  rw [Real.rpow_sub hy0, Real.rpow_natCast, hp]
  field_simp [hy0.ne']
  <;> ring

/-- Exact tail physical L2 test for the ACTUAL power function. -/
theorem eulerPower_tail_memLp_iff (a : ℝ) :
    MemLp (eulerPower a) 2 physicalTailMeasure ↔ a < 1 / 2 := by
  have hAS : AEStronglyMeasurable (eulerPower a) physicalTailMeasure := by
    have hm : Measurable (eulerPower a) := by unfold eulerPower; fun_prop
    exact hm.aestronglyMeasurable
  have hm : MemLp (eulerPower a) 2 physicalTailMeasure ↔
      IntegrableOn (fun y : ℝ => y ^ (2 * a - 2)) (Ioi (1 : ℝ)) := by
    rw [memLp_two_iff_integrable_sq_norm hAS]
    change Integrable (fun y : ℝ => ‖eulerPower a y‖ ^ 2)
      (((volume : Measure ℝ).restrict (Ioi (1 : ℝ))).withDensity
        (fun y => (tailDensity y : ℝ≥0∞))) ↔ _
    rw [integrable_withDensity_iff_integrable_smul₀ tailDensity_measurable.aemeasurable]
    change IntegrableOn (fun y : ℝ => (y⁻¹) ^ 2 * ‖eulerPower a y‖ ^ 2) (Ioi (1 : ℝ)) ↔ _
    apply integrable_congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact eulerPower_tail_density a hy
  rw [hm, integrableOn_Ioi_rpow_iff zero_lt_one]
  constructor <;> intro h <;> linarith

theorem alphaMinus_tail_memLp : MemLp (eulerPower alphaMinus) 2 physicalTailMeasure :=
  (eulerPower_tail_memLp_iff alphaMinus).mpr (by linarith [alphaMinus_lt_negHalf])

theorem alphaPlus_not_tail_memLp : ¬ MemLp (eulerPower alphaPlus) 2 physicalTailMeasure := by
  intro h
  have hp := (eulerPower_tail_memLp_iff alphaPlus).mp h
  linarith [alphaPlus_gt_threeHalves]

/-- Tail physical L2 kills the growing coefficient, using the actual
independent Euler classification and true decaying-power integrability. -/
theorem growingCoefficient_zero {f : ℝ → ℂ} {A B : ℂ}
    (hclass : ∀ y : ℝ, 0 < y → f y =
      A * eulerPower alphaPlus y + B * eulerPower alphaMinus y)
    (hL2 : MemLp f 2 physicalTailMeasure) : A = 0 := by
  have hB : MemLp (fun y => B * eulerPower alphaMinus y) 2 physicalTailMeasure := by
    simpa only [Pi.smul_apply, smul_eq_mul] using alphaMinus_tail_memLp.const_smul B
  have hEq : (fun y => f y - B * eulerPower alphaMinus y) =ᵐ[physicalTailMeasure]
      (fun y => A * eulerPower alphaPlus y) := by
    filter_upwards [physicalTailMeasure_height_gt_one] with y hy
    rw [hclass y (zero_lt_one.trans hy)]
    ring
  have hA : MemLp (fun y => A * eulerPower alphaPlus y) 2 physicalTailMeasure :=
    (hL2.sub hB).congr hEq
  by_contra hne
  apply alphaPlus_not_tail_memLp
  have h := hA.const_smul A⁻¹
  simpa only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul] using h

theorem shiftOneEuler_tail_selection (f : ℝ → ℂ)
    (hC2 : ContDiffOn ℝ 2 f (Ioi (0 : ℝ)))
    (hODE : ∀ y : ℝ, 0 < y → deriv (deriv f) y = f y / (y : ℂ) ^ 2)
    (hL2 : MemLp f 2 physicalTailMeasure) :
    ∃ B : ℂ, ∀ y : ℝ, 0 < y → f y = B * eulerPower alphaMinus y := by
  obtain ⟨A, B, hclass⟩ := shiftOneEuler_classification f hC2 hODE
  have hA := growingCoefficient_zero hclass hL2
  refine ⟨B, ?_⟩
  intro y hy
  simpa only [hA, zero_mul, zero_add] using hclass y hy

end
end ImbalancedChen.Part3.ShiftOneEulerTailSelection20261026b
