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
    change x < d * ((i.val + 1 : ℕ) : ℝ) at hhi
    change d * ((i.val + 1 : ℕ) : ℝ) ≤ wall at hwall
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
  simp [actualExtendedThirdCompactInitialPolicy, ordinaryParityRosserPolicy,
    oddFirstExitPolicy, hne]

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
      simp only [firstExitRetainedPolynomial, Bool.not_true, htest]
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
      simpa only [List.cons_append, firstExitRetainedPolynomial, Bool.not_true, hp,
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
  let R := (N : ℝ) ^ (thirdPrefixTheta - 2 * e)
  let carrier := roughPrimeUniverse N N 0 z
  let policy := ordinaryParityRosserPolicy false R
  let Adm := ordinaryRosserPrefixAdmissible false R
  have hR : 1 < R := Real.one_lt_rpow hNr hlevel
  have hnil : Adm [] := by
    simp [Adm, ordinaryRosserPrefixAdmissible,
      MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet, hR]
  have htail (q : ℕ) (pre : List ℕ) (hq : q.Prime)
      (hsort : (q :: pre).Pairwise (· < ·)) (hadm : Adm (q :: pre)) : Adm pre := by
    have hmin := (List.pairwise_cons.mp hsort).1
    have hnot : q ∉ pre.toFinset := by
      intro hqmem
      exact (lt_irrefl q) (hmin q (List.mem_toFinset.mp hqmem))
    have hmin' : ∀ p ∈ pre.toFinset, q ≤ p :=
      fun p hp => (hmin p (List.mem_toFinset.mp hp)).le
    have hprod : (pre.prod : ℝ) < R := by
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_lt.le
      have hh := hadm.1
      simp only [List.prod_cons, Nat.cast_mul] at hh
      nlinarith [Nat.cast_nonneg (α := ℝ) pre.prod]
    refine ⟨hprod, ?_⟩
    exact MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperAdmissible_of_insert_min
      hnot hmin' (by simpa only [Bool.false_eq_true, if_false,
        List.toFinset_cons] using hadm.2)
  have happend (small pre : List ℕ)
      (hprime : ∀ p ∈ small ++ pre, p.Prime)
      (hsort : (small ++ pre).Pairwise (· < ·))
      (hadm : Adm (small ++ pre)) : Adm pre := by
    induction small with
    | nil => simpa using hadm
    | cons q qs ih =>
        have hh := htail q (qs ++ pre) (hprime q (by simp)) hsort hadm
        exact ih (fun p hp => hprime p (List.mem_cons_of_mem q hp))
          (List.pairwise_cons.mp hsort).2 hh
  have hstep (pre : List ℕ) (positive : Bool) (q : ℕ)
      (hpre : Adm pre) (hsign : positive = evenListLength pre) (hq : q.Prime)
      (hsort : (q :: pre).Pairwise (· < ·)) :
      policy (!positive) (q :: pre) = decide (Adm (q :: pre)) := by
    have hmin := (List.pairwise_cons.mp hsort).1
    have hnot : q ∉ pre.toFinset := by
      intro hqmem
      exact (lt_irrefl q) (hmin q (List.mem_toFinset.mp hqmem))
    have hmin' : ∀ p ∈ pre.toFinset, q ≤ p :=
      fun p hp => (hmin p (List.mem_toFinset.mp hp)).le
    have hnd := (List.pairwise_cons.mp hsort).2.nodup
    have hprod : pre.toFinset.prod (fun p : ℕ => p) = pre.prod := by
      simpa using List.prod_toFinset (fun p : ℕ => p) hnd
    have hparity : ∀ xs : List ℕ, evenListLength xs = decide (Even xs.length) := by
      intro xs
      induction xs with
      | nil => simp [evenListLength]
      | cons x xs ih =>
          simp only [evenListLength, ih, List.length_cons, Nat.even_add_one, decide_not]
    cases positive with
    | false =>
        have hodd : ¬Even pre.toFinset.card := by
          simpa only [List.toFinset_card_of_nodup hnd, hparity, decide_eq_false_iff_not]
            using hsign.symm
        have ha := MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperAdmissible_insert_min_of_odd
          hnot hmin' hpre.2 hodd
        have hl := MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.prod_insert_min_lt_of_odd
          hnot hq hmin' hpre.2 hodd
        have hfull : Adm (q :: pre) := by
          refine ⟨?_, ?_⟩
          · simpa only [Finset.prod_insert hnot, id_eq, hprod, List.prod_cons] using hl
          · simpa only [Bool.false_eq_true, if_false, List.toFinset_cons] using ha
        simp [policy, ordinaryParityRosserPolicy, hfull]
    | true => rfl
  have hforward : ∀ (remaining pre : List ℕ) (positive : Bool) (mass : ℝ),
      Adm pre → positive = evenListLength pre →
      (∀ p ∈ remaining.reverse ++ pre, p.Prime) →
      (remaining.reverse ++ pre).Pairwise (· < ·) → ∀ leaf : FirstExitLeaf ℕ,
      leaf ∈ firstExitRetainedLeaves policy (fun _ => 1) pre positive mass remaining →
        Adm leaf.selected := by
    intro remaining
    induction remaining with
    | nil =>
        intro pre positive mass hpre _ _ _ leaf hleaf
        simp only [firstExitRetainedLeaves, List.mem_singleton] at hleaf
        subst leaf
        exact hpre
    | cons q qs ih =>
        intro pre positive mass hpre hsign hprime hsort leaf hleaf
        have hprime' : ∀ p ∈ qs.reverse ++ q :: pre, p.Prime := by
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hprime
        have hsort' : (qs.reverse ++ q :: pre).Pairwise (· < ·) := by
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hsort
        rw [firstExitRetainedLeaves, List.mem_append] at hleaf
        rcases hleaf with hskip | hselect
        · have hsub : List.Sublist (qs.reverse ++ pre) (qs.reverse ++ q :: pre) :=
            (List.Sublist.cons q (List.Sublist.refl pre)).append_left qs.reverse
          exact ih pre positive mass hpre hsign
            (fun p hp => hprime' p (hsub.subset hp)) (hsort'.sublist hsub) leaf hskip
        · by_cases ht : policy (!positive) (q :: pre) = true
          · rw [if_pos ht] at hselect
            have hnext : Adm (q :: pre) := by
              rw [hstep pre positive q hpre hsign
                (hprime' q (List.mem_append_right _ (by simp)))
                (List.pairwise_append.mp hsort').2.1] at ht
              simpa only [decide_eq_true_eq] using ht
            have hsign' : (!positive) = evenListLength (q :: pre) := by
              rw [hsign]
              rfl
            exact ih (q :: pre) (!positive) (mass * 1) hnext hsign'
              hprime' hsort' leaf hselect
          · simp only [if_neg ht, List.not_mem_nil] at hselect
  have hconstruct : ∀ {chosen remaining : List ℕ}, List.Sublist chosen remaining →
      ∀ (pre : List ℕ) (positive : Bool) (mass : ℝ),
      (∀ p ∈ chosen.reverse ++ pre, p.Prime) →
      (chosen.reverse ++ pre).Pairwise (· < ·) → Adm (chosen.reverse ++ pre) →
      ∃ leaf ∈ firstExitRetainedLeaves policy (fun _ => 1) pre positive mass remaining,
        leaf.selected = chosen.reverse ++ pre := by
    intro chosen remaining hsub
    induction hsub with
    | slnil =>
        intro pre positive mass _ _ _
        exact ⟨⟨pre, positive, mass⟩, by simp [firstExitRetainedLeaves], by simp⟩
    | cons p hsub ih =>
        intro pre positive mass hprime hsort hfinal
        obtain ⟨leaf, hleaf, heq⟩ := ih pre positive mass hprime hsort hfinal
        refine ⟨leaf, ?_, heq⟩
        rw [firstExitRetainedLeaves]
        exact List.mem_append_left _ hleaf
    | @cons_cons chosen remaining p hsub ih =>
        intro pre positive mass hprime hsort hfinal
        have hprime' : ∀ q ∈ chosen.reverse ++ p :: pre, q.Prime := by
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hprime
        have hsort' : (chosen.reverse ++ p :: pre).Pairwise (· < ·) := by
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hsort
        have hfinal' : Adm (chosen.reverse ++ p :: pre) := by
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hfinal
        have hnext := happend chosen.reverse (p :: pre) hprime' hsort' hfinal'
        have htest : policy (!positive) (p :: pre) = true := by
          simp [policy, ordinaryParityRosserPolicy, oddFirstExitPolicy]
          exact Or.inr (show ordinaryRosserPrefixAdmissible false R (p :: pre) from hnext)
        obtain ⟨leaf, hleaf, heq⟩ :=
          ih (p :: pre) (!positive) (mass * 1) hprime' hsort' hfinal'
        refine ⟨leaf, ?_, ?_⟩
        · rw [firstExitRetainedLeaves, if_pos htest]
          exact List.mem_append_right _ hleaf
        · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using heq
  have hsort : carrier.Pairwise (· > ·) := roughPrimeUniverse_pairwise_gt N N 0 z
  have hprime : ∀ p ∈ carrier, p.Prime := fun _ hp => mem_roughPrimeUniverse_prime hp
  have hcarrier0 : carrier.prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hzero
    exact (hprime 0 hzero).ne_zero rfl
  have hpf (xs : List ℕ) (hnd : xs.Nodup) (hpr : ∀ p ∈ xs, p.Prime) :
      xs.prod.primeFactors = xs.toFinset := by
    have hh : xs.toFinset.prod (fun p : ℕ => p) = xs.prod := by
      simpa using List.prod_toFinset (fun p : ℕ => p) hnd
    rw [← hh]
    exact Nat.primeFactors_prod (fun p hp => hpr p (List.mem_toFinset.mp hp))
  have hiff (d : ℕ) : d ∈ firstExitRetainedModuli policy carrier ↔
      d ∈ carrier.prod.divisors ∧ (d : ℝ) < R ∧
        MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R d.primeFactors := by
    constructor
    · intro hd
      obtain ⟨leaf, hleaf, rfl⟩ := (mem_firstExitRetainedModuli policy carrier d).mp hd
      have hfull := hforward carrier [] true 1 hnil (by simp [evenListLength])
        (by simpa only [List.append_nil, List.mem_reverse] using hprime)
        (by simpa only [List.append_nil, List.pairwise_reverse] using hsort) leaf hleaf
      have hsub := mem_firstExitRootLeaves_selected_reverse_sublist
        policy (fun _ => 1) carrier leaf hleaf
      refine ⟨Nat.mem_divisors.mpr ⟨?_, hcarrier0⟩, hfull.1, ?_⟩
      · simpa only [List.prod_reverse] using hsub.prod_dvd_prod
      · rw [mem_firstExitRootLeaves_primeFactors_selectedProd
          policy (fun _ => 1) carrier hsort.nodup hprime leaf hleaf]
        exact hfull.2
    · rintro ⟨hdiv, hlevel, hadm⟩
      have hdvd : d ∣ carrier.prod := (Nat.mem_divisors.mp hdiv).1
      have hdsq : Squarefree d := fun x hx =>
        list_prod_squarefree_of_nodup_primes carrier hsort.nodup hprime x (hx.trans hdvd)
      have hsubset : d.primeFactors ⊆ carrier.toFinset := by
        rw [← hpf carrier hsort.nodup hprime]
        exact Nat.primeFactors_mono hdvd hcarrier0
      let chosen := carrier.filter (fun p => p ∈ d.primeFactors)
      have hsub : List.Sublist chosen carrier := List.filter_sublist
      have hcset : chosen.toFinset = d.primeFactors := by
        ext p
        simp only [chosen, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
        exact ⟨fun h => h.2, fun hp => ⟨List.mem_toFinset.mp (hsubset hp), hp⟩⟩
      have hcprod : chosen.prod = d := by
        have hh : chosen.toFinset.prod (fun p : ℕ => p) = chosen.prod := by
          simpa using List.prod_toFinset (fun p : ℕ => p) (hsort.nodup.sublist hsub)
        rw [← hh]
        simpa only [hcset] using Nat.prod_primeFactors_of_squarefree hdsq
      have hcprime : ∀ p ∈ chosen.reverse ++ [], p.Prime := by
        simpa only [List.append_nil, List.mem_reverse] using
          (show ∀ p ∈ chosen, p.Prime from fun p hp => hprime p (hsub.subset hp))
      have hcsort : (chosen.reverse ++ []).Pairwise (· < ·) := by
        simpa only [List.append_nil, List.pairwise_reverse] using hsort.sublist hsub
      have hcfull : Adm (chosen.reverse ++ []) := by
        simpa only [Adm, ordinaryRosserPrefixAdmissible, Bool.false_eq_true, if_false,
          List.append_nil, List.prod_reverse, List.toFinset_reverse, hcprod, hcset]
          using And.intro hlevel hadm
      obtain ⟨leaf, hleaf, heq⟩ := hconstruct hsub [] true 1 hcprime hcsort hcfull
      apply (mem_firstExitRetainedModuli policy carrier d).mpr
      exact ⟨leaf, hleaf, by simpa only [heq, List.append_nil, List.prod_reverse] using hcprod⟩
  have hcoef (d : ℕ) : (firstExitRetainedCoefficient policy carrier d : ℝ) =
      MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight carrier.prod R d := by
    have hmu (hd : d ∈ firstExitRetainedModuli policy carrier) :
        (ArithmeticFunction.moebius d : ℝ) = (-1 : ℝ) ^ d.primeFactors.card := by
      obtain ⟨leaf, hleaf, rfl⟩ := (mem_firstExitRetainedModuli policy carrier d).mp hd
      rw [mem_firstExitRootLeaves_primeFactors_selectedProd
        policy (fun _ => 1) carrier hsort.nodup hprime leaf hleaf,
        List.toFinset_card_of_nodup (mem_firstExitRootLeaves_selected_nodup
          policy (fun _ => 1) carrier hsort.nodup leaf hleaf),
        mem_firstExitRootLeaves_moebius_selectedProd
          policy (fun _ => 1) carrier hsort.nodup hprime leaf hleaf]
      norm_cast
    by_cases hd : d ∈ firstExitRetainedModuli policy carrier
    · rw [firstExitRetainedCoefficient, if_pos hd, hmu hd,
        MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight_apply,
        if_pos ((hiff d).mp hd)]
    · rw [firstExitRetainedCoefficient, if_neg hd, Int.cast_zero,
        MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight_apply,
        if_neg (fun ha => hd ((hiff d).mpr ha))]
  change firstExitRetainedPolynomial policy weight [] true 1 carrier =
    actualSmallRosserPlusDensity N N z R
  rw [firstExitRetainedPolynomial_eq_retainedModuli_sum policy weight carrier hsort.nodup hprime]
  simp_rw [hcoef]
  have hsum : Finset.sum (firstExitRetainedModuli policy carrier)
      (fun d => MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight carrier.prod R d *
        d.primeFactors.prod weight) =
      Finset.sum carrier.prod.divisors
        (fun d => MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight carrier.prod R d *
          d.primeFactors.prod weight) := by
    apply Finset.sum_subset
    · intro d hd
      exact ((hiff d).mp hd).1
    · intro d _hd hdnot
      rw [← hcoef, firstExitRetainedCoefficient, if_neg hdnot, Int.cast_zero, zero_mul]
  rw [hsum]
  have hM : actualSmallPrimeProduct N N z = carrier.prod := by
    unfold actualSmallPrimeProduct actualSmallPrimeFinset
    rw [← roughPrimeUniverse_toFinset N N 0 z]
    change (roughPrimeUniverse N N 0 z).toFinset.prod (id : ℕ → ℕ) =
      (roughPrimeUniverse N N 0 z).prod
    rw [List.prod_toFinset (id : ℕ → ℕ) (roughPrimeUniverse_nodup N N 0 z), List.map_id]
  rw [← hM]
  unfold actualSmallRosserPlusDensity reciprocalTotientDensity
    actualSmallRosserSupport actualSmallRosserPlus
  apply Finset.sum_congr rfl
  intro d hd
  have hdsq : Squarefree d := Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd).1
    (actualSmallPrimeProduct_squarefree N N z)
  change MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight
      (actualSmallPrimeProduct N N z) R d *
        d.primeFactors.prod (fun p : ℕ => 1 / ((p : ℝ) - 1)) = _
  rw [primeFactors_prod_reciprocalTotient hdsq]
  ring

end

end ImbalancedChen
