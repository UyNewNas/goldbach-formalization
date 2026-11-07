import ImbalancedChen.P5U7OriginalUniformLogTail
import ImbalancedChen.P5U7OriginalBuchstabLipschitz

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual width of the finite directed scalar coefficients used by the U7
rational cells. This pays the interval dependency of the two directed
log queries as well as the true uniform Taylor remainder. Kernel
Lipschitz regularity alone does not establish this coefficient estimate.
-/

namespace ImbalancedChen.P5U7OriginalScalarCoefficientWidth

noncomputable section

open P2ContinuousSieveRational P5U7OriginalUniformLogTail

theorem first_width (L U : ℚ) (hL : 1 ≤ L) (hLU : L ≤ U) :
    0 ≤ 1 / L - 1 / U ∧ 1 / L - 1 / U ≤ U - L := by
  have hL0 : 0 < L := by linarith
  have hU0 : 0 < U := by linarith
  have hprod : 1 ≤ L * U := by
    have hU : 1 ≤ U := hL.trans hLU
    simpa only [one_mul] using mul_le_mul hL hU zero_le_one (zero_le_one.trans hL)
  have heq : 1 / L - 1 / U = (U - L) / (L * U) := by
    field_simp [hL0.ne', hU0.ne']
    <;> ring
  rw [heq]
  exact ⟨div_nonneg (sub_nonneg.mpr hLU) (mul_pos hL0 hU0).le,
    div_le_self (sub_nonneg.mpr hLU) hprod⟩

/-- The exact genuine second-piece coefficient width is at most the
query-interval width plus the proved query-independent Taylor rate. -/
theorem second_width (n : ℕ) (L U : ℚ)
    (hL : 2 ≤ L) (hLU : L ≤ U) (hU : U ≤ 132 / 59) :
    0 ≤ (1 + logUpper n U) / L - (1 + logLower n L) / U ∧
      (1 + logUpper n U) / L - (1 + logLower n L) / U ≤ U - L + rate n := by
  have hLr : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hLUr : (L : ℝ) ≤ U := by exact_mod_cast hLU
  have hUr : (U : ℝ) ≤ 132 / 59 := by exact_mod_cast hU
  have hU2 : 2 ≤ U := hL.trans hLU
  have hLM : L ≤ 132 / 59 := hLU.trans hU
  have hL0 : (0 : ℝ) < L := by linarith
  have hU0 : (0 : ℝ) < U := by linarith
  have hLo := log_bounds n L hL
  have hUp := log_bounds n U hU2
  have hEL := real_log_errors_le_rate n L hL hLM
  have hEU := real_log_errors_le_rate n U hU2 hU
  have hLog : |Real.log ((U : ℝ) - 1) - Real.log ((L : ℝ) - 1)| ≤ (U : ℝ) - L := by
    have h := p5U7_abs_log_sub_log_le
      (show 1 ≤ (U : ℝ) - 1 by linarith)
      (show 1 ≤ (L : ℝ) - 1 by linarith)
    have heq : ((U : ℝ) - 1) - ((L : ℝ) - 1) = (U : ℝ) - L := by ring
    simpa only [heq, abs_of_nonneg (sub_nonneg.mpr hLUr)] using h
  have hLogMono := Real.log_le_log (show 0 < (L : ℝ) - 1 by linarith)
    (show (L : ℝ) - 1 ≤ (U : ℝ) - 1 by linarith)
  have hDiff0 : 0 ≤ (logUpper n U : ℝ) - (logLower n L : ℝ) := by
    linarith only [hLo.1, hUp.2, hLogMono]
  have hDiff : (logUpper n U : ℝ) - (logLower n L : ℝ) ≤
      (U : ℝ) - L + 2 * (rate n : ℝ) := by
    have hLog' := (le_abs_self _).trans hLog
    linarith only [hEL.2.1, hEU.2.2.2, hLog']
  have hn0 : 0 ≤ (1 : ℝ) + (logLower n L : ℝ) := by
    have hh : (0 : ℝ) ≤ (logLower n L : ℝ) := by
      exact_mod_cast p5U7_logLower_nonneg n L hL
    linarith only [hh]
  have hn2 : (1 : ℝ) + (logLower n L : ℝ) ≤ 2 := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < (L : ℝ) - 1 by linarith)
    linarith only [hLo.1, hh, hLUr, hUr]
  have hInv0 : 0 ≤ 1 / (L : ℝ) - 1 / (U : ℝ) :=
    sub_nonneg.mpr (one_div_le_one_div_of_le hL0 hLUr)
  have hInv : 1 / (L : ℝ) - 1 / (U : ℝ) ≤ ((U : ℝ) - L) / 4 := by
    have hh := p5U7_abs_reciprocal_sub_le (a := 2) (by norm_num) hLr
      (show (2 : ℝ) ≤ U by linarith)
    rw [abs_of_nonneg hInv0, abs_of_nonpos (sub_nonpos.mpr hLUr)] at hh
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hh
    linarith only [hh]
  have heq :
      ((1 : ℝ) + (logUpper n U : ℝ)) / (L : ℝ) -
        ((1 : ℝ) + (logLower n L : ℝ)) / (U : ℝ) =
      ((logUpper n U : ℝ) - (logLower n L : ℝ)) / (L : ℝ) +
        (1 + (logLower n L : ℝ)) * (1 / (L : ℝ) - 1 / (U : ℝ)) := by
    field_simp [hL0.ne', hU0.ne']
    <;> ring
  have hTerm1 : ((logUpper n U : ℝ) - (logLower n L : ℝ)) / (L : ℝ) ≤
      (((U : ℝ) - L) + 2 * (rate n : ℝ)) / 2 := by
    exact (div_le_div_of_nonneg_left hDiff0 (by norm_num) hLr).trans
      (div_le_div_of_nonneg_right hDiff (by norm_num))
  have hTerm2 : (1 + (logLower n L : ℝ)) * (1 / (L : ℝ) - 1 / (U : ℝ)) ≤
      2 * (((U : ℝ) - L) / 4) :=
    mul_le_mul hn2 hInv hInv0 (by norm_num)
  have hLowR : (0 : ℝ) ≤
      ((1 : ℝ) + (logUpper n U : ℝ)) / (L : ℝ) -
        ((1 : ℝ) + (logLower n L : ℝ)) / (U : ℝ) := by
    rw [heq]
    exact add_nonneg (div_nonneg hDiff0 hL0.le) (mul_nonneg hn0 hInv0)
  have hHighR :
      ((1 : ℝ) + (logUpper n U : ℝ)) / (L : ℝ) -
        ((1 : ℝ) + (logLower n L : ℝ)) / (U : ℝ) ≤
      (U : ℝ) - L + (rate n : ℝ) := by
    rw [heq]
    linarith only [hTerm1, hTerm2]
  exact ⟨by exact_mod_cast hLowR, by exact_mod_cast hHighR⟩

end

end ImbalancedChen.P5U7OriginalScalarCoefficientWidth
