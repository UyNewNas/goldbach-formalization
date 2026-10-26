import ImbalancedChen.Part3WeakHalfLineClassicalDerivative

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The actual inverse-square Euler right side preserves local L2 on every
strictly positive finite interval, and it is continuous when the numerator
has a continuous representative. Positivity is used locally; Y=0 is allowed
for the open half-line, with no endpoint trace assumption.
-/

namespace ImbalancedChen.Part3.WeakEulerInverseSquareLocalL220261026b
noncomputable section
open MeasureTheory Set Filter

def inverseSquareRhs (M : ℝ → ℂ) (y : ℝ) : ℂ := M y / (y : ℂ) ^ 2

theorem local_memLp_inverseSquareRhs {a b : ℝ} (ha : 0 < a) {M : ℝ → ℂ}
    (hM : MemLp M 2 (volume.restrict (Ioo a b))) :
    MemLp (inverseSquareRhs M) 2 (volume.restrict (Ioo a b)) := by
  have hmeas : AEStronglyMeasurable (inverseSquareRhs M)
      (volume.restrict (Ioo a b)) := by
    have hm := hM.aestronglyMeasurable.aemeasurable.div
      ((Complex.continuous_ofReal.pow 2).measurable.aemeasurable)
    exact hm.aestronglyMeasurable
  apply (hM.norm.const_mul (a ^ 2)⁻¹).mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have hypos : 0 < y := ha.trans hy.1
  have hs : a ^ 2 ≤ y ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hy.1.le)
      (add_nonneg hypos.le ha.le)]
  have hdiv : ‖M y‖ / y ^ 2 ≤ ‖M y‖ / a ^ 2 :=
    div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos ha) hs
  simpa only [inverseSquareRhs, norm_div, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hypos, div_eq_mul_inv, mul_comm] using hdiv

theorem continuousOn_inverseSquareRhs {Y : ℝ} (hY : 0 ≤ Y) {M : ℝ → ℂ}
    (hM : ContinuousOn M (Ioi Y)) : ContinuousOn (inverseSquareRhs M) (Ioi Y) := by
  apply hM.div (Complex.continuous_ofReal.pow 2).continuousOn
  intro y hy
  exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_le_of_lt hY hy)))

theorem inverseSquareRhs_ae_of_value_ae {Y : ℝ} {M m : ℝ → ℂ}
    (hMm : ∀ᵐ y, y ∈ Ioi Y → M y = m y) :
    ∀ᵐ y, y ∈ Ioi Y → inverseSquareRhs M y = inverseSquareRhs m y := by
  filter_upwards [hMm] with y hy hym
  simp only [inverseSquareRhs, hy hym]

end
end ImbalancedChen.Part3.WeakEulerInverseSquareLocalL220261026b
