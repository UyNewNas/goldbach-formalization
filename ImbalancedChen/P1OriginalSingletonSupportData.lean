import ImbalancedChen.P1OriginalSingletonPointwiseData

/-!
Four original pointwise support declarations for the same singleton profile.
Declaration names, attached documentation and proof bytes are copied unchanged
from the pinned historical LogCollarFamily. No profile definition is duplicated.
Source intervals and the combined future-provider postimage are recorded in
p15-original-atlas-rough-prime/EXTRACTION_MANIFEST.json. Source-only adoption.
-/

namespace ImbalancedChen.P5Z.ActualSingletonLogCollarFamily
noncomputable section
open Classical Set Filter Topology
open scoped BigOperators
open ActualEtaPsiOccurrenceBudget ActualSingletonPrimeTestFamily

/-- Exact real support, with a genuinely narrow logarithmic upper collar. -/
theorem profile_support (beta : ℝ) {delta : ℝ} (hdelta : 0 < delta)
    {N : ℕ} {u : Fin 1 → ℝ} (hu : profile beta delta N u ≠ 0) :
    2 ≤ N ∧ (N : ℝ)^beta < u 0 ∧
      u 0 < (N : ℝ) * Real.exp (delta * Real.log 2) := by
  have hN : 2 ≤ N := by
    by_contra h
    exact hu (by simp [profile, h])
  have hp : 0 < u 0 := by
    by_contra h
    exact hu (by simp [profile, hN, h])
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  refine ⟨hN, ?_, ?_⟩
  · by_contra h
    exact hu (profile_zero_below beta delta hN u (le_of_not_gt h))
  · have harg : (Real.log (u 0) - Real.log (N : ℝ)) / delta < Real.log 2 := by
      by_contra h
      have htwo : 2 ≤ Real.exp ((Real.log (u 0) - Real.log (N : ℝ)) / delta) := by
        calc
          (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
          _ ≤ _ := Real.exp_le_exp.mpr (le_of_not_gt h)
      exact hu (by simp [profile, hN, hp, scaledChi, chiLog, chi_zero htwo])
    have hlog : Real.log (u 0) < Real.log (N : ℝ) + delta * Real.log 2 := by
      have h := (div_lt_iff₀ hdelta).mp harg
      nlinarith
    calc
      u 0 = Real.exp (Real.log (u 0)) := (Real.exp_log hp).symm
      _ < Real.exp (Real.log (N : ℝ) + delta * Real.log 2) := Real.exp_lt_exp.mpr hlog
      _ = _ := by rw [Real.exp_add, Real.exp_log hNr]

/-- Convexity of the exponential between 0 and log2 gives an exact
linear collar bound, with no numerical exponential evaluation. -/
theorem exp_log_two_chord {delta : ℝ} (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    Real.exp (delta * Real.log 2) ≤ 1 + delta := by
  have h : Real.exp ((1 - delta) • (0 : ℝ) + delta • Real.log 2) ≤
      (1 - delta) • Real.exp 0 + delta • Real.exp (Real.log 2) :=
    _root_.convexOn_exp.2 (by trivial) (by trivial)
      (by linarith) hdelta (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  nlinarith

theorem profile_support_short (beta : ℝ) {delta : ℝ} (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) {N : ℕ} {u : Fin 1 → ℝ}
    (hu : profile beta delta N u ≠ 0) :
    2 ≤ N ∧ (N : ℝ)^beta < u 0 ∧ u 0 < (N : ℝ) * (1 + delta) := by
  have h := profile_support beta hdelta hu
  exact ⟨h.1, h.2.1, h.2.2.trans_le
    (mul_le_mul_of_nonneg_left (exp_log_two_chord hdelta.le hdelta1) (by positivity))⟩

theorem logWidth_bounds (B : ℕ) {N : ℕ} (hN : 2 ≤ N) :
    0 < logWidth B N ∧ logWidth B N ≤ 1 := by
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hN2 : (2 : ℝ) ≤ (N : ℝ) + 2 := le_add_of_nonneg_left (Nat.cast_nonneg N)
  have hlog : Real.log 2 ≤ Real.log ((N : ℝ) + 2) := Real.log_le_log (by norm_num) hN2
  have hlogpos : 0 < Real.log ((N : ℝ) + 2) := h2.trans_le hlog
  exact ⟨pow_pos (div_pos h2 hlogpos) _, pow_le_one₀ (div_nonneg h2.le hlogpos.le)
    ((div_le_one hlogpos).mpr hlog)⟩


end
end ImbalancedChen.P5Z.ActualSingletonLogCollarFamily
