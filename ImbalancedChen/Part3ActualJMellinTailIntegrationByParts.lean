import ImbalancedChen.Part3ActualJFirstLargeQBound
import ImbalancedChen.Part3ActualRealOrderJMellinL1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Literal finite-interval integration by parts for ordinary J. The actual
native Bessel equation gives the identity, with no assumed antiderivative
or tail convergence. All functions integrated here live on [1,R].
-/

namespace ImbalancedChen.Part3.ActualJMellinTailIntegrationByParts20261026b

noncomputable section
open Complex Set MeasureTheory
open ActualGeneralJBesselSourceOnly ActualJSecondOrderJet20261026b
open ActualRealOrderJRadialJet20261026b ActualRealOrderJMellinL120261026b
open ActualJFirstLargeQBound20261026b

theorem positive_cpow_hasDerivAt (a : ℂ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ a) (a * (q : ℂ) ^ (a - 1)) q := by
  by_cases ha : a = 0
  · subst a
    simpa using (hasDerivAt_const q (1 : ℂ))
  · exact Complex.hasDerivAt_ofReal_cpow_const hq.ne' ha

theorem generalJSecond_continuousOn_positive {nu : ℝ} (hnu : |nu| ≤ 1 / 2) :
    ContinuousOn (generalJSecond (nu : ℂ)) (Ioi 0) := by
  have hF : ContinuousOn (generalJFirst (nu : ℂ)) (Ioi 0) :=
    fun q hq => (generalJFirst_hasDerivAt (real_order_lower hnu) hq).continuousAt.continuousWithinAt
  have hJ : ContinuousOn (generalJ (nu : ℂ)) (Ioi 0) :=
    fun q hq => (generalJ_hasDerivAt (real_order_lower hnu) hq).continuousAt.continuousWithinAt
  have hx : ContinuousOn (fun q : ℝ => (q : ℂ)) (Ioi 0) := Complex.continuous_ofReal.continuousOn
  have hn : ∀ q ∈ Ioi (0 : ℝ), (q : ℂ) ≠ 0 := fun q hq => Complex.ofReal_ne_zero.mpr hq.ne'
  have hc := ((hF.neg.div hx hn).sub
    ((continuousOn_const.sub (continuousOn_const.div (hx.pow 2)
      (fun q hq => pow_ne_zero 2 (hn q hq)))).mul hJ))
  exact hc.congr (fun q hq => generalJSecond_eq_jetFormula (real_order_lower hnu) hq)

theorem realOrderJMellin_integrable_interval {nu : ℝ} (hnu : |nu| ≤ 1 / 2)
    (s : ℂ) {R : ℝ} (hR : 1 ≤ R) :
    IntervalIntegrable (realOrderJMellinIntegrand s nu) volume 1 R := by
  apply ContinuousOn.intervalIntegrable
  intro q hq
  rw [uIcc_of_le hR] at hq
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq.1
  exact ((positive_cpow_hasDerivAt (s - 1) hq0).continuousAt.mul
    (generalJ_hasDerivAt (real_order_lower hnu) hq0).continuousAt).continuousWithinAt

theorem derivativeMellinRemainder_integrable_interval {nu : ℝ} (hnu : |nu| ≤ 1 / 2)
    (s : ℂ) {R : ℝ} (hR : 1 ≤ R) :
    IntervalIntegrable (derivativeMellinRemainder s nu) volume 1 R := by
  apply ContinuousOn.intervalIntegrable
  intro q hq
  rw [uIcc_of_le hR] at hq
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq.1
  exact ((positive_cpow_hasDerivAt (s - 2) hq0).continuousAt.mul
    (generalJFirst_hasDerivAt (real_order_lower hnu) hq0).continuousAt).continuousWithinAt

private theorem cpow_shift_one (s : ℂ) {q : ℝ} (hq : 0 < q) :
    (q : ℂ) ^ (s - 2) = (q : ℂ) ^ (s - 1) / (q : ℂ) := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have he : s - 2 = (s - 1) - 1 := by ring
  rw [he, Complex.cpow_sub _ _ hqC, Complex.cpow_one]

private theorem cpow_shift_two (s : ℂ) {q : ℝ} (hq : 0 < q) :
    (q : ℂ) ^ (s - 3) = (q : ℂ) ^ (s - 1) / (q : ℂ) ^ (2 : ℕ) := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have he : s - 3 = (s - 1) - 2 := by ring
  rw [he, Complex.cpow_sub _ _ hqC]
  simp only [Complex.cpow_natCast]

/-- Exact identity on finite intervals. It does not assert Bochner
integrability on the half-line beyond the absolute-convergence strip. -/
theorem realOrderJMellin_interval_integration_by_parts {nu : ℝ}
    (hnu : |nu| ≤ 1 / 2) (s : ℂ) {R : ℝ} (hR : 1 ≤ R) :
    (∫ q in (1 : ℝ)..R, realOrderJMellinIntegrand s nu q) =
      generalJFirst (nu : ℂ) 1 - (R : ℂ) ^ (s - 1) * generalJFirst (nu : ℂ) R +
        (s - 2) * (∫ q in (1 : ℝ)..R, derivativeMellinRemainder s nu q) +
        (nu : ℂ) ^ 2 * (∫ q in (1 : ℝ)..R, realOrderJMellinIntegrand (s - 2) nu q) := by
  have hpos : ∀ q ∈ uIcc (1 : ℝ) R, 0 < q := by
    intro q hq
    rw [uIcc_of_le hR] at hq
    linarith [hq.1]
  have hP : IntervalIntegrable (fun q : ℝ => (q : ℂ) ^ (s - 1)) volume 1 R :=
    ContinuousOn.intervalIntegrable (fun q hq =>
      (positive_cpow_hasDerivAt (s - 1) (hpos q hq)).continuousAt.continuousWithinAt)
  have hP' : IntervalIntegrable (fun q : ℝ => (s - 1) * (q : ℂ) ^ (s - 2)) volume 1 R := by
    apply ContinuousOn.intervalIntegrable
    intro q hq
    exact (continuousAt_const.mul (positive_cpow_hasDerivAt (s - 2) (hpos q hq)).continuousAt).continuousWithinAt
  have hS : IntervalIntegrable (generalJSecond (nu : ℂ)) volume 1 R :=
    ContinuousOn.intervalIntegrable ((generalJSecond_continuousOn_positive hnu).mono (fun q hq => hpos q hq))
  have hPS : IntervalIntegrable (fun q : ℝ => (q : ℂ) ^ (s - 1) * generalJSecond (nu : ℂ) q) volume 1 R := by
    apply ContinuousOn.intervalIntegrable
    have hp : ContinuousOn (fun q : ℝ => (q : ℂ) ^ (s - 1)) (uIcc 1 R) :=
      fun q hq => (positive_cpow_hasDerivAt (s - 1) (hpos q hq)).continuousAt.continuousWithinAt
    exact hp.mul
      ((generalJSecond_continuousOn_positive hnu).mono (fun q hq => hpos q hq))
  have hD := derivativeMellinRemainder_integrable_interval hnu s hR
  have hL := realOrderJMellin_integrable_interval hnu (s - 2) hR
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun q : ℝ => (q : ℂ) ^ (s - 1))
    (u' := fun q : ℝ => (s - 1) * (q : ℂ) ^ (s - 2))
    (v := generalJFirst (nu : ℂ)) (v' := generalJSecond (nu : ℂ))
    (fun q hq => by
      convert positive_cpow_hasDerivAt (s - 1) (hpos q hq) using 1 <;> congr 1 <;> ring)
    (fun q hq => generalJFirst_hasDerivAt (real_order_lower hnu) (hpos q hq)) hP' hS
  have hIBP' : (∫ q in (1 : ℝ)..R, (q : ℂ) ^ (s - 1) * generalJSecond (nu : ℂ) q) =
      (R : ℂ) ^ (s - 1) * generalJFirst (nu : ℂ) R - generalJFirst (nu : ℂ) 1 -
        (s - 1) * (∫ q in (1 : ℝ)..R, derivativeMellinRemainder s nu q) := by
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul] at hIBP
    have he : (fun q : ℝ => ((s - 1) * (q : ℂ) ^ (s - 2)) * generalJFirst (nu : ℂ) q) =
        (fun q : ℝ => (s - 1) * derivativeMellinRemainder s nu q) := by
      funext q
      unfold derivativeMellinRemainder
      ring
    rw [he, intervalIntegral.integral_const_mul] at hIBP
    exact hIBP
  have hODE : (∫ q in (1 : ℝ)..R, realOrderJMellinIntegrand s nu q) =
      -(∫ q in (1 : ℝ)..R, (q : ℂ) ^ (s - 1) * generalJSecond (nu : ℂ) q) -
        (∫ q in (1 : ℝ)..R, derivativeMellinRemainder s nu q) +
        (nu : ℂ) ^ 2 * (∫ q in (1 : ℝ)..R, realOrderJMellinIntegrand (s - 2) nu q) := by
    rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_sub hPS.neg hD,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hPS.neg.sub hD) (hL.const_mul ((nu : ℂ) ^ 2))]
    apply intervalIntegral.integral_congr
    intro q hq
    have hq0 := hpos q hq
    have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq0.ne'
    rw [realOrderJMellinIntegrand, derivativeMellinRemainder,
      realOrderJMellinIntegrand, show (s - 2) - 1 = s - 3 by ring,
      cpow_shift_one s hq0, cpow_shift_two s hq0,
      generalJSecond_eq_jetFormula (real_order_lower hnu) hq0]
    field_simp [hqC]
    ring
  rw [hODE, hIBP']
  ring

end
end ImbalancedChen.Part3.ActualJMellinTailIntegrationByParts20261026b
