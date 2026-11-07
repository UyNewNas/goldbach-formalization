import ImbalancedChen.P2EnhancedTwentyOneSameQWeighted

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original Theta_Q lower comparison is extended from the existing
natural convolution coefficients to the actual given nonnegative real
sigma(d). Its lower constant is the existing proved universal singular
series product. No lower bound for a sieve count or correction function
is assumed. This preserves the reciprocal mass needed to cancel the
weighted collision error, including for zero weights or empty supports.
-/

namespace ImbalancedChen.P2EnhancedThetaReciprocalMass

noncomputable section

open Finset Wu2008DoubleSieve
open P2EnhancedTwentyOneSameQWeighted
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.SingularSeries
open scoped Classical

/-- Scalar original mean-kernel comparison, with the actual singular series. -/
theorem mean_kernel_lower {N d : ℕ} {Q : ℝ}
    (hN : 4 ≤ N) (hd : 0 < d) (hQ : 1 < Q / (d : ℝ) ∧ Q / (d : ℝ) ≤ N) :
    liuUniversalProduct / ((d : ℝ) * Real.log N) ≤
      wuSingularSeries (d * N) / ((Nat.totient d : ℝ) * Real.log (Q / d)) := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hdreal : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have htpos : (0 : ℝ) < Nat.totient d := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd)
  have ht : (Nat.totient d : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
  have hlogR : 0 < Real.log (Q / d) := Real.log_pos hQ.1
  have hlogRN : Real.log (Q / d) ≤ Real.log N :=
    Real.log_le_log (zero_lt_one.trans hQ.1) hQ.2
  have hC : liuUniversalProduct ≤ wuSingularSeries (d * N) := by
    rw [wuSingularSeries_eq_liu _ (mul_pos hd (by omega : 0 < N))]
    exact liuUniversalProduct_le_liuSingularSeries _
  have hCpos : 0 < wuSingularSeries (d * N) := liuUniversalProduct_pos.trans_le hC
  calc
    _ ≤ wuSingularSeries (d * N) / ((d : ℝ) * Real.log N) :=
      div_le_div_of_nonneg_right hC (mul_pos hdreal hlog).le
    _ ≤ _ := div_le_div_of_nonneg_left hCpos.le (mul_pos htpos hlogR)
      (mul_le_mul ht hlogRN hlogR.le hdreal.le)

/-- Same-Q normalization dominates the original sigma reciprocal mass. -/
theorem Theta_lower {N : ℕ} (hN : 4 ≤ N) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (hd : ∀ d ∈ D, 0 < d) (hsigma : ∀ d ∈ D, 0 ≤ sigma d)
    (hQ : ∀ d ∈ D, 1 < Q / (d : ℝ) ∧ Q / (d : ℝ) ≤ N) :
    (2 * liuUniversalProduct * (N : ℝ) / Real.log N ^ 2) *
      (∑ d ∈ D, sigma d / (d : ℝ)) ≤ Theta N Q D sigma := by
  have hU := liuUniversalProduct_pos
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hmass : 0 ≤ ∑ d ∈ D, sigma d / (d : ℝ) :=
    sum_nonneg (fun d hmem => div_nonneg (hsigma d hmem) (Nat.cast_nonneg d))
  have hli := box_trueLi_lower hN
  have hli0 : 0 ≤ logarithmicIntegral N :=
    (by positivity : (0 : ℝ) ≤ N / (2 * Real.log N)).trans hli
  have hsum :
      liuUniversalProduct / Real.log N * (∑ d ∈ D, sigma d / (d : ℝ)) ≤
      ∑ d ∈ D, sigma d * wuSingularSeries (d * N) /
        ((Nat.totient d : ℝ) * Real.log (Q / d)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro d hmem
    have h := mul_le_mul_of_nonneg_left (mean_kernel_lower hN (hd d hmem) (hQ d hmem))
      (hsigma d hmem)
    convert h using 1 <;> ring
  calc
    _ = 4 * ((N : ℝ) / (2 * Real.log N)) *
        (liuUniversalProduct / Real.log N * (∑ d ∈ D, sigma d / (d : ℝ))) := by ring
    _ ≤ 4 * logarithmicIntegral N *
        (liuUniversalProduct / Real.log N * (∑ d ∈ D, sigma d / (d : ℝ))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hli (by norm_num))
        (mul_nonneg (div_nonneg hU.le hlog.le) hmass)
    _ ≤ Theta N Q D sigma :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hli0)

end
end ImbalancedChen.P2EnhancedThetaReciprocalMass
