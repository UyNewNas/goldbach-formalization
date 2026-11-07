import ImbalancedChen.CurrentNumericalTransfer

/-!
# Strict threshold for the original current coefficient

SOURCE ONLY: this draft has not been compiled. The constants and logarithmic
margins are imported unchanged from `CurrentNumericalTransfer`.
-/

namespace ImbalancedChen.P6

noncomputable section

/-- The coefficient of the original current-manuscript transfer. -/
def currentCoefficient (b : ℝ) : ℝ :=
  currentC - currentK * Real.log (1 / b)

theorem currentC_pos : 0 < currentC := by
  norm_num [currentC]

theorem currentK_pos : 0 < currentK := by
  norm_num [currentK]

theorem current_constants_pos : 0 < currentC ∧ 0 < currentK := by
  exact ⟨currentC_pos, currentK_pos⟩

/-- Rewriting the reciprocal logarithm does not require a sign hypothesis. -/
theorem currentCoefficient_eq (b : ℝ) :
    currentCoefficient b = currentC + currentK * Real.log b := by
  simp only [currentCoefficient, one_div, Real.log_inv, mul_neg, sub_neg_eq_add]

/-- The exact strict endpoint comparison; no approximation of the exponential. -/
theorem currentCoefficient_pos_iff {b : ℝ} (hb : 0 < b) :
    0 < currentCoefficient b ↔ Real.exp (-currentC / currentK) < b := by
  rw [currentCoefficient_eq]
  constructor
  · intro h
    apply (Real.log_lt_log_iff (Real.exp_pos _) hb).mp
    rw [Real.log_exp]
    apply (div_lt_iff₀ currentK_pos).mpr
    nlinarith only [h]
  · intro h
    have hlog := (Real.log_lt_log_iff (Real.exp_pos _) hb).mpr h
    rw [Real.log_exp] at hlog
    have hmul := (div_lt_iff₀ currentK_pos).mp hlog
    nlinarith only [hmul]

/-- The same equivalence displayed with the original coefficient expression. -/
theorem current_original_coefficient_pos_iff {b : ℝ} (hb : 0 < b) :
    0 < currentC - currentK * Real.log (1 / b) ↔
      Real.exp (-currentC / currentK) < b := by
  exact currentCoefficient_pos_iff hb

theorem currentCoefficient_strictMonoOn :
    StrictMonoOn currentCoefficient (Set.Ioi 0) := by
  intro a ha b hb hab
  have hlog := (Real.log_lt_log_iff ha hb).mpr hab
  have hmul := mul_lt_mul_of_pos_left hlog currentK_pos
  simp only [currentCoefficient_eq]
  linarith only [hmul]

theorem currentCoefficient_monotoneOn :
    MonotoneOn currentCoefficient (Set.Ioi 0) := by
  exact currentCoefficient_strictMonoOn.monotoneOn

theorem currentCoefficient_lt_of_pos_of_lt {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a < b) :
    currentCoefficient a < currentCoefficient b := by
  exact currentCoefficient_strictMonoOn ha hb hab

theorem currentCoefficient_le_of_pos_of_le {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    currentCoefficient a ≤ currentCoefficient b := by
  exact currentCoefficient_monotoneOn ha hb hab

/-- An existing positive coefficient stays positive at every larger exponent. -/
theorem currentCoefficient_pos_of_le {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hpos : 0 < currentCoefficient a) :
    0 < currentCoefficient b := by
  exact lt_of_lt_of_le hpos
    (currentCoefficient_le_of_pos_of_le ha (lt_of_lt_of_le ha hab) hab)

/-- Exact rational-domain check for the primary corollary exponent. -/
theorem current_exponent_74816964_domain :
    (1 : ℝ) / 2 < 18704241 / 25000000 ∧
      (18704241 : ℝ) / 25000000 < 1 := by
  norm_num

/-- Exact rational-domain check for the secondary corollary exponent. -/
theorem current_exponent_74816865_domain :
    (1 : ℝ) / 2 < 14963373 / 20000000 ∧
      (14963373 : ℝ) / 20000000 < 1 := by
  norm_num

/-- Exact rational-domain check for the final corollary exponent. -/
theorem current_exponent_09_domain :
    (1 : ℝ) / 2 < 9 / 10 ∧ (9 : ℝ) / 10 < 1 := by
  norm_num

/-- The original primary gap, reused after exact reciprocal normalization. -/
theorem currentCoefficient_gap_74816964 :
    (1 : ℝ) / 100000 < currentCoefficient (18704241 / 25000000) := by
  unfold currentCoefficient
  have hrecip : (1 : ℝ) / (18704241 / 25000000) =
      25000000 / 18704241 := by norm_num
  rw [hrecip]
  exact current_gap_74816964

/-- The original secondary gap, reused after exact reciprocal normalization. -/
theorem currentCoefficient_gap_74816865 :
    (1 : ℝ) / 1000000 < currentCoefficient (14963373 / 20000000) := by
  unfold currentCoefficient
  have hrecip : (1 : ℝ) / (14963373 / 20000000) =
      20000000 / 14963373 := by norm_num
  rw [hrecip]
  exact current_gap_74816865

/-- The original final gap, reused after exact reciprocal normalization. -/
theorem currentCoefficient_gap_09 :
    (124889 : ℝ) / 100000 < currentCoefficient (9 / 10) := by
  unfold currentCoefficient
  have hrecip : (1 : ℝ) / (9 / 10) = 10 / 9 := by norm_num
  rw [hrecip]
  exact current_gap_09

theorem current_threshold_lt_74816964 :
    Real.exp (-currentC / currentK) < (18704241 : ℝ) / 25000000 := by
  apply (currentCoefficient_pos_iff (by norm_num)).mp
  have h := currentCoefficient_gap_74816964
  linarith only [h]

theorem current_threshold_lt_74816865 :
    Real.exp (-currentC / currentK) < (14963373 : ℝ) / 20000000 := by
  apply (currentCoefficient_pos_iff (by norm_num)).mp
  have h := currentCoefficient_gap_74816865
  linarith only [h]

theorem current_threshold_lt_09 :
    Real.exp (-currentC / currentK) < (9 : ℝ) / 10 := by
  apply (currentCoefficient_pos_iff (by norm_num)).mp
  have h := currentCoefficient_gap_09
  linarith only [h]

/-- The exact exponential threshold is positive and less than one. -/
theorem current_threshold_domain :
    0 < Real.exp (-currentC / currentK) ∧
      Real.exp (-currentC / currentK) < 1 := by
  exact ⟨Real.exp_pos _, lt_trans current_threshold_lt_09 current_exponent_09_domain.2⟩

/-- All three published rational exponents satisfy the strict analytic threshold. -/
theorem current_corollary_exponents_above_threshold :
    Real.exp (-currentC / currentK) < (18704241 : ℝ) / 25000000 ∧
    Real.exp (-currentC / currentK) < (14963373 : ℝ) / 20000000 ∧
    Real.exp (-currentC / currentK) < (9 : ℝ) / 10 := by
  exact ⟨current_threshold_lt_74816964,
    current_threshold_lt_74816865, current_threshold_lt_09⟩

end

end ImbalancedChen.P6
