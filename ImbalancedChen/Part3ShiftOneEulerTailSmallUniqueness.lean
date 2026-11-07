import ImbalancedChen.Part3ShiftOneEulerTailSelection
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Exact shift-one physical Euler deficiency uniqueness. Genuine C2 plus
f''=f/y^2, actual tail L2(dy/y^2) on y>1, and the literal small-height
condition sqrt(y)*f(y)->0 force f=0 on y>0. Tail L2 selects the actual
decaying root using the independently proved classification. Since
alphaMinus<-1/2, its reciprocal small-height weight has positive exponent;
the native limit calculation kills the remaining coefficient.

This is EXACT shift 1. It does not generalize the same small-height
condition to every positive shift. The geometric derivation of that
small-height condition for an actual quotient mean REMAINS OPEN; no
quotient deficiency uniqueness or range-density conclusion is claimed.
No CuspConstantMode/HOLD supplier is imported.
-/

namespace ImbalancedChen.Part3.ShiftOneEulerTailSmallUniqueness20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open ShiftOneEulerClassification20261026b ShiftOneEulerTailSelection20261026b

theorem decayingCoefficient_zero {f : ℝ → ℂ} {B : ℂ}
    (hclass : ∀ y : ℝ, 0 < y → f y = B * eulerPower alphaMinus y)
    (hsmall : Tendsto (fun y : ℝ => (Real.sqrt y : ℂ) * f y) (𝓝[>] 0) (𝓝 0)) : B = 0 := by
  let r : ℝ := -alphaMinus - 1 / 2
  have hr : 0 < r := by dsimp [r]; linarith [alphaMinus_lt_negHalf]
  have hreal : Tendsto (fun y : ℝ => y ^ r) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa only [Real.zero_rpow hr.ne'] using
      ((Real.continuous_rpow_const hr.le).tendsto (0 : ℝ)).mono_left inf_le_left
  have hcomplex : Tendsto (fun y : ℝ => ((y ^ r : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    simpa only [Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
  have hprod : Tendsto (fun y : ℝ => ((y ^ r : ℝ) : ℂ) * ((Real.sqrt y : ℂ) * f y))
      (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    simpa only [zero_mul] using hcomplex.mul hsmall
  have hweights : ∀ y : ℝ, 0 < y →
      ((y ^ r : ℝ) : ℂ) * ((Real.sqrt y : ℂ) * f y) = B := by
    intro y hy
    rw [hclass y hy, eulerPower_eq_rpow alphaMinus hy]
    have hw : (y ^ r) * Real.sqrt y * y ^ alphaMinus = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hy, ← Real.rpow_add hy]
      rw [show r + 1 / 2 + alphaMinus = 0 by dsimp [r]; ring, Real.rpow_zero]
    have hwC : ((y ^ r : ℝ) : ℂ) * (Real.sqrt y : ℂ) * (y ^ alphaMinus : ℝ) = 1 := by
      exact_mod_cast hw
    calc
      _ = (((y ^ r : ℝ) : ℂ) * (Real.sqrt y : ℂ) * (y ^ alphaMinus : ℝ)) * B := by ring
      _ = B := by rw [hwC, one_mul]
  have hconst : Tendsto (fun _ : ℝ => B) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    apply hprod.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hweights y hy
  exact tendsto_nhds_unique tendsto_const_nhds hconst

/-- The needed scalar uniqueness theorem: actual C2 equation, actual
physical tail L2, and an EXPLICIT small-height hypothesis. -/
theorem shiftOneEuler_tail_small_unique (f : ℝ → ℂ)
    (hC2 : ContDiffOn ℝ 2 f (Ioi (0 : ℝ)))
    (hODE : ∀ y : ℝ, 0 < y → deriv (deriv f) y = f y / (y : ℂ) ^ 2)
    (hL2 : MemLp f 2 physicalTailMeasure)
    (hsmall : Tendsto (fun y : ℝ => (Real.sqrt y : ℂ) * f y) (𝓝[>] 0) (𝓝 0)) :
    ∀ y : ℝ, 0 < y → f y = 0 := by
  obtain ⟨B, hclass⟩ := shiftOneEuler_tail_selection f hC2 hODE hL2
  have hB := decayingCoefficient_zero hclass hsmall
  intro y hy
  simpa only [hB, zero_mul] using hclass y hy

/-- The original physical deficiency expression has the same exact
scalar conclusion, with division by y^2 derived only for positive y. -/
theorem physical_shiftOne_deficiency_tail_small_unique (f : ℝ → ℂ)
    (hC2 : ContDiffOn ℝ 2 f (Ioi (0 : ℝ)))
    (hODE : ∀ y : ℝ, 0 < y →
      -((y : ℂ) ^ 2) * deriv (deriv f) y + f y = 0)
    (hL2 : MemLp f 2 physicalTailMeasure)
    (hsmall : Tendsto (fun y : ℝ => (Real.sqrt y : ℂ) * f y) (𝓝[>] 0) (𝓝 0)) :
    ∀ y : ℝ, 0 < y → f y = 0 := by
  apply shiftOneEuler_tail_small_unique f hC2 _ hL2 hsmall
  intro y hy
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  apply (eq_div_iff (pow_ne_zero 2 hyC)).mpr
  linear_combination -(hODE y hy)

end
end ImbalancedChen.Part3.ShiftOneEulerTailSmallUniqueness20261026b
