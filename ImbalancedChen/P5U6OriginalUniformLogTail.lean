import ImbalancedChen.P5U6OriginalRationalBoxBounds
import Mathlib.Analysis.SpecificLimits.Basic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The true U6 profile band [2,1323/417] gives exactly z<=(163/441).
The actual P2 rational Taylor upper/lower gap is uniformly paid by
4*(163/441)^(2*n+1), tending to zero. The real geometric remainder has
the same bound, even for a varying real query in the actual profile band.
No computed integration, saved endpoint or assumed analytic tail bound.
-/

namespace ImbalancedChen.P5U6OriginalUniformLogTail

noncomputable section

open Set Filter Topology
open P2ContinuousSieveRational

def ratio : ℚ := 163 / 441
def rate (n : ℕ) : ℚ := 4 * ratio ^ (2 * n + 1)
def realTail (n : ℕ) (s : ℝ) : ℝ :=
  2 * ((s - 2) / s) ^ (2 * n + 1) / (1 - ((s - 2) / s) ^ 2)

/-- Derived from the original exact upper profile, with no larger
substitute interval. (1323-834)/1323=163/441. -/
theorem ratio_bounds {s : ℝ} (hs : s ∈ Icc (2 : ℝ) (1323 / 417)) :
    0 ≤ (s - 2) / s ∧ (s - 2) / s ≤ (ratio : ℝ) := by
  have hs0 : 0 < s := by linarith [hs.1]
  refine ⟨div_nonneg (by linarith [hs.1]) hs0.le, ?_⟩
  apply (div_le_iff₀ hs0).mpr
  norm_num [ratio]
  linarith only [hs.2]

theorem actual_profile_ratio_bounds {x : Fin 2 → ℝ}
    (hx : x ∈ currentChenUpsilon6LogDomain 0) :
    0 ≤ (currentChenUpsilon6OrdinaryProfile x - 2) / currentChenUpsilon6OrdinaryProfile x ∧
      (currentChenUpsilon6OrdinaryProfile x - 2) / currentChenUpsilon6OrdinaryProfile x ≤
        (163 / 441 : ℝ) := by
  simpa only [ratio, Rat.cast_div, Rat.cast_ofNat] using ratio_bounds
    (P5U6RunboEnhancedFloorInterfaceSourceOnly.profile_range (by norm_num) hx)

theorem rate_nonneg (n : ℕ) : 0 ≤ rate n := by unfold rate ratio; positivity

theorem realTail_bounds (n : ℕ) {s : ℝ}
    (hs : s ∈ Icc (2 : ℝ) (1323 / 417)) :
    0 ≤ realTail n s ∧ realTail n s ≤ (rate n : ℝ) := by
  let z : ℝ := (s - 2) / s
  obtain ⟨hz0, hzr⟩ := ratio_bounds hs
  have hzhalf : z ≤ 1 / 2 := hzr.trans (by norm_num [ratio])
  have hzsq : z ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hz0 hzhalf 2
  have hden : (1 / 2 : ℝ) ≤ 1 - z ^ 2 := by nlinarith only [hzsq]
  have hden0 : 0 < 1 - z ^ 2 := lt_of_lt_of_le (by norm_num) hden
  have hpow : z ^ (2 * n + 1) ≤ (ratio : ℝ) ^ (2 * n + 1) :=
    pow_le_pow_left₀ hz0 hzr _
  change 0 ≤ 2 * z ^ (2 * n + 1) / (1 - z ^ 2) ∧
    2 * z ^ (2 * n + 1) / (1 - z ^ 2) ≤ (rate n : ℝ)
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hz0 _)) hden0.le
  · calc
      _ ≤ (2 * (ratio : ℝ) ^ (2 * n + 1)) / (1 - z ^ 2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) hden0.le
      _ ≤ (2 * (ratio : ℝ) ^ (2 * n + 1)) / (1 / 2) :=
        div_le_div_of_nonneg_left
          (mul_nonneg (by norm_num) (pow_nonneg (by norm_num [ratio]) _)) (by norm_num) hden
      _ = (rate n : ℝ) := by
        simp only [rate, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow]
        ring

theorem rational_gap_eq_realTail (n : ℕ) (q : ℚ) :
    ((logUpper n q - logLower n q : ℚ) : ℝ) = realTail n (q : ℝ) := by
  unfold logUpper realTail
  push_cast
  ring

theorem rational_gap_le_rate (n : ℕ) (q : ℚ)
    (hq : 2 ≤ q) (hM : q ≤ 1323 / 417) :
    0 ≤ logUpper n q - logLower n q ∧ logUpper n q - logLower n q ≤ rate n := by
  have h := realTail_bounds n (s := (q : ℝ))
    ⟨by exact_mod_cast hq, by exact_mod_cast hM⟩
  rw [← rational_gap_eq_realTail] at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- Both directed errors for the actual REAL logarithm share one
query-independent rate, including the original s=2 endpoint. -/
theorem real_log_errors_le_rate (n : ℕ) (q : ℚ)
    (hq : 2 ≤ q) (hM : q ≤ 1323 / 417) :
    0 ≤ Real.log ((q : ℝ) - 1) - (logLower n q : ℝ) ∧
      Real.log ((q : ℝ) - 1) - (logLower n q : ℝ) ≤ (rate n : ℝ) ∧
      0 ≤ (logUpper n q : ℝ) - Real.log ((q : ℝ) - 1) ∧
      (logUpper n q : ℝ) - Real.log ((q : ℝ) - 1) ≤ (rate n : ℝ) := by
  have hlog := log_bounds n q hq
  have hgap : (logUpper n q : ℝ) - (logLower n q : ℝ) ≤ (rate n : ℝ) := by
    exact_mod_cast (rational_gap_le_rate n q hq hM).2
  exact ⟨sub_nonneg.mpr hlog.1, (by linarith only [hlog.2, hgap]),
    sub_nonneg.mpr hlog.2, (by linarith only [hlog.1, hgap])⟩

theorem tendsto_rate : Tendsto (fun n : ℕ => (rate n : ℝ)) atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ (ratio : ℝ) by norm_num [ratio])
    (show (ratio : ℝ) < 1 by norm_num [ratio])
  have h := (hp.pow 2).const_mul (4 * (ratio : ℝ))
  have heq (n : ℕ) : (rate n : ℝ) = (4 * (ratio : ℝ)) * ((ratio : ℝ) ^ n) ^ 2 := by
    simp only [rate, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
    rw [show 2 * n + 1 = n * 2 + 1 by omega, pow_succ, pow_mul]
    ring
  have h' : Tendsto (fun n : ℕ => (4 * (ratio : ℝ)) * ((ratio : ℝ) ^ n) ^ 2)
      atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] using h
  apply h'.congr'
  exact Filter.Eventually.of_forall (fun n => (heq n).symm)

/-- Uniform payment for an arbitrary varying REAL query in the genuine
profile band, rather than only fixed rational query nodes. -/
theorem tendsto_realTail (s : ℕ → ℝ)
    (hs : ∀ n, s n ∈ Icc (2 : ℝ) (1323 / 417)) :
    Tendsto (fun n => realTail n (s n)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds tendsto_rate
  · intro n
    exact (realTail_bounds n (hs n)).1
  · intro n
    exact (realTail_bounds n (hs n)).2

end

end ImbalancedChen.P5U6OriginalUniformLogTail
