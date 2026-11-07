import ImbalancedChen.Part3RealOrderKExceptional
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# A global logarithmic bound for the actual zero-order K integral

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
This is proved directly from the literal cosh-Laplace integral. The head
has length max(0,log(2/q)); on the tail, cosh u >= exp(u)/2 and
exp(u-L) >= 1+u-L give an integrable exponential with mass exp(-1).
No K asymptotic or integral bound is assumed.
-/

namespace ImbalancedChen.Part3.ActualKZeroGlobalLogBound20261025a

noncomputable section
open Set MeasureTheory
open RealOrderKExceptionalSourceOnly

def zeroOrderCutoff (q : ℝ) : ℝ := max 0 (Real.log (2 / q))

theorem zeroOrderCutoff_nonneg (q : ℝ) : 0 ≤ zeroOrderCutoff q := le_max_left _ _

theorem two_le_mul_exp_zeroOrderCutoff {q : ℝ} (hq : 0 < q) :
    2 ≤ q * Real.exp (zeroOrderCutoff q) := by
  have hlog : Real.log (2 / q) ≤ zeroOrderCutoff q := le_max_right _ _
  have hexp : 2 / q ≤ Real.exp (zeroOrderCutoff q) := by
    simpa only [Real.exp_log (div_pos (by norm_num) hq)] using
      Real.exp_le_exp.mpr hlog
  have hm := mul_le_mul_of_nonneg_left hexp hq.le
  have he : q * (2 / q) = 2 := by field_simp [ne_of_gt hq]
  simpa only [he] using hm

/-- The actual zero-order integrand has an elementary tail majorant. -/
theorem zeroOrderIntegrand_le_tail {q u : ℝ} (hq : 0 < q) :
    realOrderIntegrand 0 q u ≤
      Real.exp (zeroOrderCutoff q - 1) * Real.exp (-u) := by
  let L := zeroOrderCutoff q
  have hL : 2 ≤ q * Real.exp L := two_le_mul_exp_zeroOrderCutoff hq
  have hu : Real.exp u = Real.exp L * Real.exp (u - L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hc : Real.exp u / 2 ≤ Real.cosh u := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-u)]
  have hm := mul_le_mul_of_nonneg_right hL (Real.exp_nonneg (u - L))
  have hqc := mul_le_mul_of_nonneg_left hc hq.le
  have hlin : 1 + u - L ≤ q * Real.cosh u := by
    rw [hu] at hqc
    nlinarith [Real.add_one_le_exp (u - L)]
  simp only [realOrderIntegrand, zero_mul, Real.cosh_zero, mul_one]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change -q * Real.cosh u ≤ L - 1 + -u
  linarith

/-- A global upper bound, valid for every positive argument, including
arguments tending to zero along an order-dependent contour. -/
theorem realOrderK_zero_le_log {q : ℝ} (hq : 0 < q) :
    realOrderK 0 q ≤ max 0 (Real.log (2 / q)) + Real.exp (-1) := by
  let L := zeroOrderCutoff q
  have hL : 0 ≤ L := zeroOrderCutoff_nonneg q
  have hf := realOrderIntegrand_integrable 0 hq (by norm_num)
  have hft := hf.mono_set (Ioi_subset_Ioi hL)
  have hgt := (integrableOn_exp_neg_Ioi L).const_mul (Real.exp (L - 1))
  have htail : (∫ u in Ioi L, realOrderIntegrand 0 q u) ≤ Real.exp (-1) := by
    calc
      _ ≤ ∫ u in Ioi L, Real.exp (L - 1) * Real.exp (-u) := by
        apply integral_mono_ae hft hgt
        exact Filter.Eventually.of_forall fun u => zeroOrderIntegrand_le_tail hq
      _ = Real.exp (-1) := by
        rw [integral_const_mul, integral_exp_neg_Ioi, ← Real.exp_add]
        congr 1
        ring
  have hc : Continuous (realOrderIntegrand 0 q) := by
    unfold realOrderIntegrand
    fun_prop
  have hhead : (∫ u in (0 : ℝ)..L, realOrderIntegrand 0 q u) ≤ L := by
    calc
      _ ≤ ∫ _u in (0 : ℝ)..L, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on hL hc.intervalIntegrable
          continuous_const.intervalIntegrable
        intro u hu
        simp only [realOrderIntegrand, zero_mul, Real.cosh_zero, mul_one]
        exact Real.exp_le_one_iff.mpr (by nlinarith [Real.cosh_pos u])
      _ = L := by simp
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hf hL
  change (∫ u in Ioi (0 : ℝ), realOrderIntegrand 0 q u) ≤ L + Real.exp (-1)
  linarith

end
end ImbalancedChen.Part3.ActualKZeroGlobalLogBound20261025a
