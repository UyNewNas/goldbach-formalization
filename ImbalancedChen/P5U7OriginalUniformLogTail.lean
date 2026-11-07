import ImbalancedChen.P5U7OriginalRationalCellBounds
import Mathlib.Analysis.SpecificLimits.Basic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Uniform directed rational Taylor error on the exact original second
Buchstab interval. The true P2 rational upper-minus-lower expression is
bounded by 4*(7/66)^(2*n+1), and this explicit sequence tends to zero.
No numeric evaluation, integral certificate or supplied tail bound.
-/

namespace ImbalancedChen.P5U7OriginalUniformLogTail

noncomputable section

open Filter Topology P2ContinuousSieveRational

def rate (n : ℕ) : ℚ := 4 * (7 / 66 : ℚ) ^ (2 * n + 1)

theorem ratio_bounds (q : ℚ) (hq : 2 ≤ q) (hM : q ≤ 132 / 59) :
    0 ≤ (q - 2) / q ∧ (q - 2) / q ≤ 7 / 66 := by
  have hq0 : 0 < q := by linarith
  refine ⟨div_nonneg (by linarith) hq0.le, ?_⟩
  apply (div_le_iff₀ hq0).mpr
  linarith only [hM]

theorem rate_nonneg (n : ℕ) : 0 ≤ rate n := by unfold rate; positivity

/-- The exact actual rational Taylor gap, uniform in its real query band. -/
theorem rational_gap_le_rate (n : ℕ) (q : ℚ)
    (hq : 2 ≤ q) (hM : q ≤ 132 / 59) :
    0 ≤ logUpper n q - logLower n q ∧
      logUpper n q - logLower n q ≤ rate n := by
  let z : ℚ := (q - 2) / q
  obtain ⟨hz0, hzr⟩ := ratio_bounds q hq hM
  have hzhalf : z ≤ 1 / 2 := hzr.trans (by norm_num)
  have hzsq : z ^ 2 ≤ (1 / 2 : ℚ) ^ 2 := pow_le_pow_left₀ hz0 hzhalf 2
  have hden : (1 / 2 : ℚ) ≤ 1 - z ^ 2 := by nlinarith only [hzsq]
  have hden0 : 0 < 1 - z ^ 2 := lt_of_lt_of_le (by norm_num) hden
  have hpow : z ^ (2 * n + 1) ≤ (7 / 66 : ℚ) ^ (2 * n + 1) :=
    pow_le_pow_left₀ hz0 hzr _
  have heq : logUpper n q - logLower n q = 2 * z ^ (2 * n + 1) / (1 - z ^ 2) := by
    unfold logUpper
    dsimp [z]
    ring
  rw [heq]
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hz0 _)) hden0.le
  · calc
      _ ≤ (2 * (7 / 66 : ℚ) ^ (2 * n + 1)) / (1 - z ^ 2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) hden0.le
      _ ≤ (2 * (7 / 66 : ℚ) ^ (2 * n + 1)) / (1 / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
      _ = rate n := by unfold rate; ring

/-- Both directed errors of the actual real logarithm are paid by the
same query-independent rational rate, including the lower endpoint q=2. -/
theorem real_log_errors_le_rate (n : ℕ) (q : ℚ)
    (hq : 2 ≤ q) (hM : q ≤ 132 / 59) :
    0 ≤ Real.log ((q : ℝ) - 1) - (logLower n q : ℝ) ∧
      Real.log ((q : ℝ) - 1) - (logLower n q : ℝ) ≤ (rate n : ℝ) ∧
      0 ≤ (logUpper n q : ℝ) - Real.log ((q : ℝ) - 1) ∧
      (logUpper n q : ℝ) - Real.log ((q : ℝ) - 1) ≤ (rate n : ℝ) := by
  have hlog := log_bounds n q hq
  have hgapQ := (rational_gap_le_rate n q hq hM).2
  have hgap : (logUpper n q : ℝ) - (logLower n q : ℝ) ≤ (rate n : ℝ) := by
    exact_mod_cast hgapQ
  exact ⟨sub_nonneg.mpr hlog.1, (by linarith only [hlog.2, hgap]),
    sub_nonneg.mpr hlog.2, (by linarith only [hlog.1, hgap])⟩

theorem tendsto_rate : Tendsto (fun n : ℕ => (rate n : ℝ)) atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 7 / 66 by norm_num) (show (7 / 66 : ℝ) < 1 by norm_num)
  have h := (hp.pow 2).const_mul (4 * (7 / 66 : ℝ))
  have heq (n : ℕ) : (rate n : ℝ) =
      (4 * (7 / 66 : ℝ)) * ((7 / 66 : ℝ) ^ n) ^ 2 := by
    simp only [rate, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat]
    rw [show 2 * n + 1 = n * 2 + 1 by omega, pow_succ, pow_mul]
    ring
  have h' : Tendsto
      (fun n : ℕ => (4 * (7 / 66 : ℝ)) * ((7 / 66 : ℝ) ^ n) ^ 2)
      atTop (𝓝 0) := by simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] using h
  apply h'.congr'
  exact Filter.Eventually.of_forall (fun n => (heq n).symm)

end

end ImbalancedChen.P5U7OriginalUniformLogTail
