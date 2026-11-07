import ImbalancedChen.Part3ActualKAbelSmallArgumentBound
import ImbalancedChen.Part3GeneralKRightEndpoint
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# A uniform power/log budget for the actual exceptional K integral

Source-only J candidate. The small-argument Abel estimate and the actual
right-endpoint moment estimate are reused, not assumed or reproved. The new
step removes the Abel normalizer, makes its constant uniform for
|alpha| <= 7/32, and supplies one global budget suitable for the physical
packet. No spectral mean, automorphic identity, or Eq24 premise occurs.
-/

namespace ImbalancedChen.Part3.ActualExceptionalKGlobalBudget20261102

noncomputable section
open Set MeasureTheory
open RealOrderKExceptionalSourceOnly ComplexOrderKBridgeSourceOnly
open ComplexOrderKQCalculus GeneralKRightEndpoint20261025a
open ActualKAbelSmallArgumentBound20261026b

def theta : ℝ := 7 / 32

def logBudget (q : ℝ) : ℝ := 1 + Real.log 2 + max 0 (-Real.log q)

def kernelBudget (q alpha : ℝ) : ℝ :=
  2 * (2 : ℝ) ^ theta * logBudget q * (1 + 1 / q) ^ |alpha| / (1 + q)

theorem logBudget_pos (q : ℝ) : 0 < logBudget q := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  unfold logBudget
  linarith [le_max_left (0 : ℝ) (-Real.log q)]

theorem kernelBudget_nonneg {q : ℝ} (hq : 0 < q) (alpha : ℝ) :
    0 ≤ kernelBudget q alpha := by
  unfold kernelBudget
  exact div_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (Real.rpow_nonneg (by norm_num) _)) (logBudget_pos q).le)
      (Real.rpow_nonneg (by positivity) _)) (by positivity)

theorem realOrderK_abs_order (alpha q : ℝ) :
    realOrderK |alpha| q = realOrderK alpha q := by
  by_cases ha : 0 ≤ alpha
  · rw [abs_of_nonneg ha]
  · rw [abs_of_neg (lt_of_not_ge ha), realOrderK_even]

/-- The literal real-order K integral consumes the existing complex Abel
bound. The inverse real power is derived, including alpha=0. -/
theorem realOrderK_small_argument {alpha q : ℝ}
    (hq : 0 < q) (hqu : q ≤ 1) (halpha : |alpha| ≤ theta) :
    |realOrderK alpha q| ≤ (2 / q) ^ |alpha| * (1 - Real.log (q / 2)) := by
  have ha1 : |alpha| ≤ (1 : ℝ) := by unfold theta at halpha; linarith
  have hb := actual_normalized_K_small_argument_bound
    (ν := (|alpha| : ℂ)) (by simpa using abs_nonneg alpha)
    (by simpa using ha1) hq hqu
  simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (half_pos hq),
    Complex.ofReal_re, complexOrderK_real, Complex.norm_real, Real.norm_eq_abs,
    realOrderK_abs_order] at hb
  have hinverse : (2 / q) ^ |alpha| * (q / 2) ^ |alpha| = 1 := by
    rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 / q)
      (half_pos hq).le]
    have hc : (2 / q) * (q / 2) = 1 := by field_simp [hq.ne']
    rw [hc, Real.one_rpow]
  calc
    |realOrderK alpha q| =
        ((2 / q) ^ |alpha| * (q / 2) ^ |alpha|) * |realOrderK alpha q| := by
      rw [hinverse, one_mul]
    _ = (2 / q) ^ |alpha| * ((q / 2) ^ |alpha| * |realOrderK alpha q|) := by ring
    _ ≤ (2 / q) ^ |alpha| * (1 - Real.log (q / 2)) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (by positivity) _)

/-- The q=1 moment mass in the existing general-order exponential bound
is exactly the positive real-order K integral, rather than a new constant. -/
theorem momentMass_zero_real (alpha : ℝ) :
    momentMass 0 (alpha : ℂ) = realOrderK alpha 1 := by
  unfold momentMass realOrderK
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  have he : qMomentIntegrand 0 (alpha : ℂ) 1 u =
      (realOrderIntegrand alpha 1 u : ℂ) := by
    simp only [qMomentIntegrand, pow_zero, one_mul, ← Complex.ofReal_mul,
      ← Complex.ofReal_cosh, realOrderIntegrand]
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le)

theorem realOrderK_large_argument {alpha q : ℝ} (hq : 1 ≤ q) :
    |realOrderK alpha q| ≤ Real.exp (1 - q) * realOrderK alpha 1 := by
  have h := complexOrderK_norm_exp_bound (alpha : ℂ) hq
  simpa only [complexOrderK_real, Complex.norm_real, Real.norm_eq_abs,
    momentMass_zero_real] using h

theorem exp_decay_le_two_div {q : ℝ} (hq : 1 ≤ q) :
    Real.exp (1 - q) ≤ 2 / (1 + q) := by
  have hlin : q ≤ Real.exp (q - 1) := by
    have h := Real.add_one_le_exp (q - 1)
    linarith
  have hprod : q * Real.exp (1 - q) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (1 - q)).le
    have he : Real.exp (q - 1) * Real.exp (1 - q) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    simpa only [he] using h
  have hsmall : Real.exp (1 - q) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  apply (le_div_iff₀ (by linarith : 0 < 1 + q)).mpr
  nlinarith only [hprod, hsmall]

theorem logBudget_of_small {q : ℝ} (hq : 0 < q) (hqu : q ≤ 1) :
    1 - Real.log (q / 2) = logBudget q := by
  have hl : Real.log q ≤ 0 := Real.log_nonpos hq.le hqu
  rw [Real.log_div hq.ne' (by norm_num), logBudget,
    max_eq_right (neg_nonneg.mpr hl)]
  ring

theorem logBudget_of_large {q : ℝ} (hq : 1 ≤ q) :
    logBudget q = 1 + Real.log 2 := by
  rw [logBudget, max_eq_left (neg_nonpos.mpr (Real.log_nonneg hq)), add_zero]

/-- One bound for every positive q. Its only q-growth at zero is the
actual order |alpha|, with a logarithmic factor uniform through alpha=0. -/
theorem realOrderK_global_budget {alpha q : ℝ}
    (hq : 0 < q) (halpha : |alpha| ≤ theta) :
    |realOrderK alpha q| ≤ kernelBudget q alpha := by
  have htwo : 0 ≤ (2 : ℝ) ^ theta := Real.rpow_nonneg (by norm_num) _
  have hlog : 0 ≤ logBudget q := (logBudget_pos q).le
  have hp : 0 ≤ (1 + 1 / q) ^ |alpha| := Real.rpow_nonneg (by positivity) _
  have hden : 0 < 1 + q := by positivity
  by_cases hqu : q ≤ 1
  · have hpower : (2 / q) ^ |alpha| ≤
        (2 : ℝ) ^ theta * (1 + 1 / q) ^ |alpha| := by
      calc
        (2 / q) ^ |alpha| ≤ (2 * (1 + 1 / q)) ^ |alpha| :=
          Real.rpow_le_rpow (by positivity) (by linarith) (abs_nonneg _)
        _ = (2 : ℝ) ^ |alpha| * (1 + 1 / q) ^ |alpha| :=
          Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ (2 : ℝ) ^ theta * (1 + 1 / q) ^ |alpha| :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) halpha) hp
    have hb : |realOrderK alpha q| ≤
        (2 : ℝ) ^ theta * logBudget q * (1 + 1 / q) ^ |alpha| := by
      calc
        _ ≤ (2 / q) ^ |alpha| * logBudget q := by
          simpa only [logBudget_of_small hq hqu] using
            realOrderK_small_argument hq hqu halpha
        _ ≤ ((2 : ℝ) ^ theta * (1 + 1 / q) ^ |alpha|) * logBudget q :=
          mul_le_mul_of_nonneg_right hpower hlog
        _ = _ := by ring
    apply hb.trans
    unfold kernelBudget
    apply (le_div_iff₀ hden).mpr
    have hn : 0 ≤ (2 : ℝ) ^ theta * logBudget q * (1 + 1 / q) ^ |alpha| :=
      mul_nonneg (mul_nonneg htwo hlog) hp
    nlinarith only [mul_le_mul_of_nonneg_left hqu hn]
  · have hq1 : 1 ≤ q := (lt_of_not_ge hqu).le
    have hb1 : realOrderK alpha 1 ≤ (2 : ℝ) ^ theta * (1 + Real.log 2) := by
      have hb := realOrderK_small_argument (q := (1 : ℝ)) (by norm_num) le_rfl halpha
      have hl : 1 - Real.log ((1 : ℝ) / 2) = 1 + Real.log 2 := by
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
        ring
      rw [hl, div_one] at hb
      exact (le_abs_self _).trans (hb.trans
        (mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) halpha)
          (by have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); linarith)))
    have hp1 : 1 ≤ (1 + 1 / q) ^ |alpha| :=
      Real.one_le_rpow (by have h : 0 ≤ 1 / q := by positivity; linarith)
        (abs_nonneg _)
    calc
      |realOrderK alpha q| ≤ Real.exp (1 - q) * realOrderK alpha 1 :=
        realOrderK_large_argument hq1
      _ ≤ Real.exp (1 - q) * ((2 : ℝ) ^ theta * (1 + Real.log 2)) :=
        mul_le_mul_of_nonneg_left hb1 (Real.exp_pos _).le
      _ ≤ (2 / (1 + q)) * ((2 : ℝ) ^ theta * (1 + Real.log 2)) :=
        mul_le_mul_of_nonneg_right (exp_decay_le_two_div hq1)
          (by rw [← logBudget_of_large hq1]; exact mul_nonneg htwo hlog)
      _ = 2 * (2 : ℝ) ^ theta * logBudget q / (1 + q) := by
        rw [logBudget_of_large hq1]
        ring
      _ ≤ kernelBudget q alpha := by
        unfold kernelBudget
        apply (div_le_div_iff₀ hden hden).mpr
        have hh := mul_le_mul_of_nonneg_left hp1
          (mul_nonneg (mul_nonneg (by norm_num) htwo) hlog)
        nlinarith only [mul_le_mul_of_nonneg_right hh hden.le]

theorem logBudget_antitone {a q : ℝ} (ha : 0 < a) (haq : a ≤ q) :
    logBudget q ≤ logBudget a := by
  unfold logBudget
  exact add_le_add_left
    (max_le_max le_rfl (neg_le_neg (Real.log_le_log ha haq))) _

theorem kernelBudget_antitone {a q : ℝ} (ha : 0 < a) (haq : a ≤ q)
    (alpha : ℝ) : kernelBudget q alpha ≤ kernelBudget a alpha := by
  have hq := ha.trans_le haq
  have hl := logBudget_antitone ha haq
  have hp : (1 + 1 / q) ^ |alpha| ≤ (1 + 1 / a) ^ |alpha| := by
    apply Real.rpow_le_rpow (by positivity) _ (abs_nonneg _)
    have hh : 1 / q ≤ 1 / a := one_div_le_one_div_of_le ha haq
    linarith
  have hn : 2 * (2 : ℝ) ^ theta * logBudget q * (1 + 1 / q) ^ |alpha| ≤
      2 * (2 : ℝ) ^ theta * logBudget a * (1 + 1 / a) ^ |alpha| := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hl (by positivity)) hp (by positivity)
      (by have h := logBudget_pos a; positivity)
  unfold kernelBudget
  calc
    _ ≤ (2 * (2 : ℝ) ^ theta * logBudget a * (1 + 1 / a) ^ |alpha|) / (1 + q) :=
      div_le_div_of_nonneg_right hn (by positivity)
    _ ≤ _ := by
      have h := logBudget_pos a
      gcongr

end
end ImbalancedChen.Part3.ActualExceptionalKGlobalBudget20261102
