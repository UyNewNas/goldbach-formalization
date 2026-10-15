import ImbalancedChen.ActualExtendedThirdCompactUpperRho

/-!
# The initial dyadic first stop is an exact prime cutoff

The union of the actual owned first-coordinate bins is the half-open
interval ending at step times floor((rho-4e)/step). This exponent can be
zero on a coarse grid. The corresponding strict prime cutoff is retained
literally, including equality at an endpoint.

Splitting the original decreasing prime universe at that cutoff removes
only a high segment whose first selections all fail. The low segment has
the same ordinary full tests: after the first selection, the extra initial
first-stop implication is vacuous. The root is therefore the actual
ordinary plus density on this precise truncated carrier, at its unchanged
old level. No density estimate or comparison by nonnegativity is assumed.
-/

namespace ImbalancedChen

noncomputable section

open Set
open scoped Classical

def actualExtendedThirdInitialStopExponent (e : ℝ) (m : ℕ) : ℝ :=
  actualExtendedThirdDyadicStep m *
    (⌊(thirdPrefixRho - 4 * e) / actualExtendedThirdDyadicStep m⌋₊ : ℝ)

theorem actualExtendedThirdInitialStopExponent_bounds {e : ℝ}
    (he0 : 0 < e) (he : e ≤ 1 / 384) (m : ℕ) :
    0 ≤ actualExtendedThirdInitialStopExponent e m ∧
      actualExtendedThirdInitialStopExponent e m ≤ thirdPrefixRho - 4 * e ∧
        thirdPrefixRho - 4 * e - actualExtendedThirdDyadicStep m <
          actualExtendedThirdInitialStopExponent e m ∧
            actualExtendedThirdInitialStopExponent e m < thirdPrefixRho := by
  have hd := actualExtendedThirdDyadicStep_pos m
  have hw : 0 ≤ thirdPrefixRho - 4 * e := by
    dsimp [thirdPrefixRho]
    linarith
  have hdiv : 0 ≤ (thirdPrefixRho - 4 * e) / actualExtendedThirdDyadicStep m :=
    div_nonneg hw hd.le
  have hcancel : actualExtendedThirdDyadicStep m *
      ((thirdPrefixRho - 4 * e) / actualExtendedThirdDyadicStep m) = thirdPrefixRho - 4 * e := by
    simpa only [mul_comm] using div_mul_cancel₀ (thirdPrefixRho - 4 * e) hd.ne'
  have hupper : actualExtendedThirdInitialStopExponent e m ≤ thirdPrefixRho - 4 * e := by
    unfold actualExtendedThirdInitialStopExponent
    exact (mul_le_mul_of_nonneg_left (Nat.floor_le hdiv) hd.le).trans_eq hcancel
  have hnext := mul_lt_mul_of_pos_left
    (Nat.lt_floor_add_one ((thirdPrefixRho - 4 * e) / actualExtendedThirdDyadicStep m)) hd
  rw [hcancel] at hnext
  refine ⟨mul_nonneg hd.le (Nat.cast_nonneg _), hupper, ?_, ?_⟩
  · unfold actualExtendedThirdInitialStopExponent
    nlinarith only [hnext]
  · exact hupper.trans_lt (by linarith)

private theorem initialDyadicLo_step (m : ℕ) (i : Fin (2 ^ m)) :
    actualExtendedThirdDyadicLo m (fun _ => i) 0 =
      actualExtendedThirdDyadicStep m * (i.val : ℝ) := by
  unfold actualExtendedThirdDyadicLo actualExtendedThirdDyadicStep
  ring

private theorem initialDyadicHi_step (m : ℕ) (i : Fin (2 ^ m)) :
    actualExtendedThirdDyadicHi m (fun _ => i) 0 =
      actualExtendedThirdDyadicStep m * ((i.val + 1 : ℕ) : ℝ) := by
  unfold actualExtendedThirdDyadicHi actualExtendedThirdDyadicStep
  ring

private theorem initialDyadicStep_full (m : ℕ) :
    actualExtendedThirdDyadicStep m * ((2 ^ m : ℕ) : ℝ) = thirdPrefixRho := by
  simp only [actualExtendedThirdDyadicStep, Nat.cast_pow, Nat.cast_ofNat]
  exact div_mul_cancel₀ _ (by positivity)

private theorem compactFirstStop_iff_log {e : ℝ} (he0 : 0 < e)
    (he : e ≤ 1 / 384) (m N : ℕ) (history : List ℕ)
    (hx : 0 ≤ primeHistoryLogCoordinates (N : ℝ) 1 history 0) :
    actualExtendedThirdCompactFirstStop e m N history ↔
      primeHistoryLogCoordinates (N : ℝ) 1 history 0 <
        actualExtendedThirdInitialStopExponent e m := by
  let d := actualExtendedThirdDyadicStep m
  let wall := thirdPrefixRho - 4 * e
  let x := primeHistoryLogCoordinates (N : ℝ) 1 history 0
  let k := ⌊wall / d⌋₊
  have hd : 0 < d := actualExtendedThirdDyadicStep_pos m
  have hw : 0 ≤ wall := by
    dsimp [wall, thirdPrefixRho]
    linarith
  have hwdiv : 0 ≤ wall / d := div_nonneg hw hd.le
  have hxd : 0 ≤ x / d := div_nonneg hx hd.le
  have hkn : k < 2 ^ m := by
    apply (Nat.floor_lt hwdiv).mpr
    apply (div_lt_iff₀ hd).mpr
    calc
      wall < thirdPrefixRho := by dsimp [wall]; linarith
      _ = ((2 ^ m : ℕ) : ℝ) * d := by
        simpa only [mul_comm] using (initialDyadicStep_full m).symm
  constructor
  · rintro ⟨i, _hlo, hhi, hwall⟩
    rw [initialDyadicHi_step] at hhi hwall
    have hik : i.val + 1 ≤ k := (Nat.le_floor_iff hwdiv).mpr
      ((le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hwall))
    change x < d * (k : ℝ)
    exact hhi.trans_le (mul_le_mul_of_nonneg_left (by exact_mod_cast hik) hd.le)
  · intro hcut
    change x < d * (k : ℝ) at hcut
    let a := ⌊x / d⌋₊
    have hak : a < k := (Nat.floor_lt hxd).mpr
      ((div_lt_iff₀ hd).mpr (by simpa only [mul_comm] using hcut))
    let i : Fin (2 ^ m) := ⟨a, hak.trans hkn⟩
    refine ⟨i, ?_, ?_, ?_⟩
    · rw [initialDyadicLo_step]
      simpa only [i, mul_comm] using (le_div_iff₀ hd).mp (Nat.floor_le hxd)
    · rw [initialDyadicHi_step]
      have hnext := (div_lt_iff₀ hd).mp (Nat.lt_floor_add_one (x / d))
      simpa only [i, Nat.cast_add, Nat.cast_one, mul_comm] using hnext
    · rw [initialDyadicHi_step]
      have ha : a + 1 ≤ k := Nat.succ_le_of_lt hak
      have hbound : d * ((a + 1 : ℕ) : ℝ) ≤ d * (k : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast ha) hd.le
      exact hbound.trans (actualExtendedThirdInitialStopExponent_bounds he0 he m).2.1

/-- This is the original strict prime endpoint, including a zero stop
exponent on coarse grids. No first-cube test is discarded. -/
theorem actualExtendedThirdCompactFirstStop_iff_prime {e : ℝ}
    (he0 : 0 < e) (he : e ≤ 1 / 384) {N : ℕ} (hN : 1 < N)
    (m p : ℕ) (hp : 0 < p) :
    actualExtendedThirdCompactFirstStop e m N [p] ↔
      (p : ℝ) < (N : ℝ) ^ actualExtendedThirdInitialStopExponent e m := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hx : 0 ≤ primeHistoryLogCoordinates (N : ℝ) 1 [p] 0 := by
    simpa [primeHistoryLogCoordinates, primeHistoryTuple] using
      div_nonneg (Real.log_nonneg hp1) (Real.log_pos hNr).le
  have hpow : (N : ℝ) ^ primeHistoryLogCoordinates (N : ℝ) 1 [p] 0 = (p : ℝ) := by
    simpa [primeHistoryLogCoordinates, primeHistoryTuple, actualPrimeTupleLog] using
      actualPrimeTupleLog_rpow hN (fun _ : Fin 1 => p) (fun _ => hp) 0
  rw [compactFirstStop_iff_log he0 he m N [p] hx,
    ← Real.rpow_lt_rpow_left_iff hNr, hpow]

/-- The original target N itself covers the precise first-stop cutoff. -/
theorem actualExtendedThirdInitialStop_cutoff_le_target {e : ℝ}
    (he0 : 0 < e) (he : e ≤ 1 / 384) {N : ℕ} (hN : 1 < N) (m : ℕ) :
    (N : ℝ) ^ actualExtendedThirdInitialStopExponent e m ≤ (N : ℝ) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNr.le
      ((actualExtendedThirdInitialStopExponent_bounds he0 he m).2.2.2.le.trans
        (by norm_num [thirdPrefixRho]))
    _ = _ := Real.rpow_one _

private theorem initial_next_eq_ordinary (e : ℝ) (m N : ℕ)
    (positive : Bool) (q : ℕ) (history : List ℕ) (hne : history ≠ []) :
    actualExtendedThirdCompactInitialPolicy e m N positive (q :: history) =
      ordinaryParityRosserPolicy false ((N : ℝ) ^ (thirdPrefixTheta - 2 * e))
        positive (q :: history) := by
  have hlen : (q :: history).length ≠ 1 := by
    intro hh
    apply hne
    apply List.length_eq_zero_iff.mp
    simp only [List.length_cons] at hh
    omega
  simp [actualExtendedThirdCompactInitialPolicy, ordinaryParityRosserPolicy,
    oddFirstExitPolicy, hlen]

private theorem initial_nonempty_continuation (e : ℝ) (m N : ℕ)
    (weight : ℕ → ℝ) (remaining history : List ℕ) (positive : Bool) (mass : ℝ)
    (hne : history ≠ []) :
    firstExitRetainedPolynomial (actualExtendedThirdCompactInitialPolicy e m N)
        weight history positive mass remaining =
      firstExitRetainedPolynomial
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (thirdPrefixTheta - 2 * e)))
        weight history positive mass remaining := by
  induction remaining generalizing history positive mass with
  | nil => rfl
  | cons q qs ih =>
      simp only [firstExitRetainedPolynomial,
        initial_next_eq_ordinary e m N (!positive) q history hne]
      rw [ih history positive mass hne]
      by_cases hq : ordinaryParityRosserPolicy false ((N : ℝ) ^ (thirdPrefixTheta - 2 * e))
          (!positive) (q :: history) = true
      · rw [if_pos hq, if_pos hq, ih (q :: history) (!positive) (mass * weight q) (by simp)]
      · rw [if_neg hq, if_neg hq]

private theorem initial_root_on_low (e : ℝ) (m N : ℕ) (weight : ℕ → ℝ)
    (carrier : List ℕ)
    (hstop : ∀ p ∈ carrier, actualExtendedThirdCompactFirstStop e m N [p]) :
    firstExitRetainedPolynomial (actualExtendedThirdCompactInitialPolicy e m N)
        weight [] true 1 carrier =
      firstExitRetainedPolynomial
        (ordinaryParityRosserPolicy false ((N : ℝ) ^ (thirdPrefixTheta - 2 * e)))
        weight [] true 1 carrier := by
  revert hstop
  induction carrier with
  | nil => intro _; rfl
  | cons p ps ih =>
      intro hstop
      have hp := hstop p (by simp)
      have hps := fun q hq => hstop q (List.mem_cons_of_mem p hq)
      have htest : actualExtendedThirdCompactInitialPolicy e m N false [p] =
          ordinaryParityRosserPolicy false ((N : ℝ) ^ (thirdPrefixTheta - 2 * e)) false [p] := by
        simp [actualExtendedThirdCompactInitialPolicy, ordinaryParityRosserPolicy,
          oddFirstExitPolicy, hp]
      simp only [firstExitRetainedPolynomial, htest]
      rw [ih hps]
      by_cases ht : ordinaryParityRosserPolicy false ((N : ℝ) ^ (thirdPrefixTheta - 2 * e))
          false [p] = true
      · rw [if_pos ht, if_pos ht,
          initial_nonempty_continuation e m N weight ps [p] false (1 * weight p) (by simp)]
      · rw [if_neg ht, if_neg ht]

private theorem initial_root_skip_high (e : ℝ) (m N : ℕ) (weight : ℕ → ℝ)
    (high low : List ℕ)
    (hfail : ∀ p ∈ high, actualExtendedThirdCompactInitialPolicy e m N false [p] = false) :
    firstExitRetainedPolynomial (actualExtendedThirdCompactInitialPolicy e m N)
        weight [] true 1 (high ++ low) =
      firstExitRetainedPolynomial (actualExtendedThirdCompactInitialPolicy e m N)
        weight [] true 1 low := by
  revert hfail
  induction high with
  | nil => intro _; rfl
  | cons p ps ih =>
      intro hfail
      have hp := hfail p (by simp)
      simpa only [List.cons_append, firstExitRetainedPolynomial, hp,
        Bool.false_eq_true, if_false, add_zero] using
        ih (fun q hq => hfail q (List.mem_cons_of_mem p hq))

/-- The same initial policy has exactly the ordinary plus density at its
true dyadic cutoff. The original cap is N and the full polynomial has w=0.
The old level retains both total-product and every inherited cubic test. -/
theorem actualExtendedThirdInitialPolicy_eq_actualPlus {e : ℝ}
    (he0 : 0 < e) (he : e ≤ 1 / 384) {N : ℕ} (hN : 1 < N) (m : ℕ) :
    firstExitRetainedPolynomial (actualExtendedThirdCompactInitialPolicy e m N)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N N 0 ((N : ℝ) ^ thirdPrefixRho)) =
      actualSmallRosserPlusDensity N N
        ((N : ℝ) ^ actualExtendedThirdInitialStopExponent e m)
        ((N : ℝ) ^ (thirdPrefixTheta - 2 * e)) := by
  let z := (N : ℝ) ^ actualExtendedThirdInitialStopExponent e m
  let weight := fun p : ℕ => 1 / ((p : ℝ) - 1)
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hz : z ≤ (N : ℝ) ^ thirdPrefixRho :=
    Real.rpow_le_rpow_of_exponent_le hNr.le
      (actualExtendedThirdInitialStopExponent_bounds he0 he m).2.2.2.le
  have hfail : ∀ p ∈ roughPrimeUniverse N N z ((N : ℝ) ^ thirdPrefixRho),
      actualExtendedThirdCompactInitialPolicy e m N false [p] = false := by
    intro p hp
    have hn : ¬actualExtendedThirdCompactFirstStop e m N [p] := by
      intro hs
      exact (not_lt_of_ge (mem_roughPrimeUniverse_lower hp))
        ((actualExtendedThirdCompactFirstStop_iff_prime he0 he hN m p
          (mem_roughPrimeUniverse_prime hp).pos).mp hs)
    simp [actualExtendedThirdCompactInitialPolicy, oddFirstExitPolicy, hn]
  have hstop : ∀ p ∈ roughPrimeUniverse N N 0 z,
      actualExtendedThirdCompactFirstStop e m N [p] := by
    intro p hp
    exact (actualExtendedThirdCompactFirstStop_iff_prime he0 he hN m p
      (mem_roughPrimeUniverse_prime hp).pos).mpr (mem_roughPrimeUniverse_upper hp)
  rw [roughPrimeUniverse_split N N z ((N : ℝ) ^ thirdPrefixRho) hz,
    initial_root_skip_high e m N weight _ _ hfail,
    initial_root_on_low e m N weight _ hstop]
  have hlevel : 0 < thirdPrefixTheta - 2 * e := by
    dsimp [thirdPrefixTheta]
    linarith
  simpa only [Bool.false_eq_true, if_false] using
    firstExitRetainedPolynomial_ordinaryParityRosser_eq_actualDensity
      false N N z ((N : ℝ) ^ (thirdPrefixTheta - 2 * e))
      (Real.one_lt_rpow hNr hlevel) (by simp)

end

end ImbalancedChen
