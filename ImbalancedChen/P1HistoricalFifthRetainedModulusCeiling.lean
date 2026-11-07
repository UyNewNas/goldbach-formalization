import ImbalancedChen.P1HistoricalCapCeilingCheck
import ImbalancedChen.P1HistoricalFixedCoefficientAssembly
import ImbalancedChen.FirstExitValidSelection

/-!
# Complete retained-prefix validity and a rough-modulus ceiling

The effective level is the original constant through rank two, the frozen
third selector at ranks three/four, and the frozen fifth selector thereafter.
Active rank-three and rank-five tests check the complete ordinary prefix.
All other selections propagate complete validity using sorted primes and
`ordinaryParityRosserPolicy_eq_full_on_valid_prefix`; in particular no
even-rank validity is inferred from a Boolean `true` alone.

The support and coefficient are the exact assembly p1FifthRoughSupport and
p1FifthRoughCoefficient. Only the rough modulus is bounded. Small weights,
additional products, and a 599/1000 physical-support licence are not supplied.
Sibling imports record intended integration; this draft is uncompiled.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical

namespace HistoricalPrefixCapData

def p1FifthEffectiveLevel (D : HistoricalPrefixCapData) (N : ℝ)
    (history : List ℕ) : ℝ :=
  if history.length ≤ 2 then N ^ (D.old : ℝ) else
    if history.length ≤ 4 then D.level3 N (rosserAncestor 3 history) else
      D.level5 N (rosserAncestor 5 history)

theorem p1UpperFifthPolicy_eq_effective (D : HistoricalPrefixCapData) (N : ℝ)
    (positive : Bool) (history : List ℕ) :
    D.upperFifthPolicy N positive history =
      ordinaryParityRosserPolicy false (D.p1FifthEffectiveLevel N history) positive history := by
  by_cases h2 : history.length ≤ 2
  · have h4 : history.length ≤ 4 := by omega
    simp only [upperFifthPolicy, fifthCappedUpperPolicy, thirdCappedUpperPolicy,
      firstExitDepthSplicePolicy, frozenParityRosserPolicy, ancestorFrozenPolicy,
      p1FifthEffectiveLevel, if_pos h2, if_pos h4]
  · by_cases h4 : history.length ≤ 4
    · simp only [upperFifthPolicy, fifthCappedUpperPolicy, thirdCappedUpperPolicy,
        firstExitDepthSplicePolicy, frozenParityRosserPolicy, ancestorFrozenPolicy,
        p1FifthEffectiveLevel, if_neg h2, if_pos h4]
    · simp only [upperFifthPolicy, fifthCappedUpperPolicy, thirdCappedUpperPolicy,
        firstExitDepthSplicePolicy, frozenParityRosserPolicy, ancestorFrozenPolicy,
        p1FifthEffectiveLevel, if_neg h2, if_neg h4]

private theorem p1Fifth_evenListLength (history : List ℕ) :
    evenListLength history = decide (Even history.length) := by
  induction history with
  | nil => simp [evenListLength]
  | cons p ps ih =>
      simp only [evenListLength, ih, List.length_cons, Nat.even_add_one, decide_not]

/-- Away from the two actual reset steps, the frozen level is identical
before and after selecting the next prime. -/
theorem p1FifthEffectiveLevel_cons_of_not_reset (D : HistoricalPrefixCapData) (N : ℝ)
    (q : ℕ) (pre : List ℕ) (h3 : pre.length ≠ 2) (h5 : pre.length ≠ 4) :
    D.p1FifthEffectiveLevel N (q :: pre) = D.p1FifthEffectiveLevel N pre := by
  by_cases h2 : pre.length ≤ 2
  · have hn2 : (q :: pre).length ≤ 2 := by simp only [List.length_cons]; omega
    simp only [p1FifthEffectiveLevel, if_pos h2, if_pos hn2]
  · have hn2 : ¬(q :: pre).length ≤ 2 := by simp only [List.length_cons]; omega
    by_cases h4 : pre.length ≤ 4
    · have hn4 : (q :: pre).length ≤ 4 := by simp only [List.length_cons]; omega
      simp only [p1FifthEffectiveLevel, if_neg h2, if_neg hn2, if_pos h4, if_pos hn4,
        rosserAncestor_cons 3 q pre (by omega)]
    · have hn4 : ¬(q :: pre).length ≤ 4 := by simp only [List.length_cons]; omega
      simp only [p1FifthEffectiveLevel, if_neg h2, if_neg hn2, if_neg h4, if_neg hn4,
        rosserAncestor_cons 5 q pre (by omega)]

/-- Complete one-step validity. At the active reset ranks the full test
is read directly; every inactive step uses the full incoming validity. -/
theorem p1UpperFifthPolicy_oneStep_admissible (D : HistoricalPrefixCapData) (N : ℝ)
    (pre : List ℕ) (positive : Bool) (q : ℕ)
    (hpre : ordinaryRosserPrefixAdmissible false (D.p1FifthEffectiveLevel N pre) pre)
    (hsign : positive = evenListLength pre) (hq : q.Prime)
    (hsort : (q :: pre).Pairwise (· < ·))
    (htest : D.upperFifthPolicy N (!positive) (q :: pre) = true) :
    ordinaryRosserPrefixAdmissible false (D.p1FifthEffectiveLevel N (q :: pre)) (q :: pre) := by
  rw [D.p1UpperFifthPolicy_eq_effective N (!positive) (q :: pre)] at htest
  by_cases hreset : pre.length = 2 ∨ pre.length = 4
  · have hs : positive = true := by
      rcases hreset with h2 | h4
      · rw [hsign, p1Fifth_evenListLength, h2]
        decide
      · rw [hsign, p1Fifth_evenListLength, h4]
        decide
    simpa only [hs, Bool.not_true, ordinaryParityRosserPolicy, Bool.false_eq_true,
      if_false, oddFirstExitPolicy, Bool.false_or, decide_eq_true_eq] using htest
  · have h3 : pre.length ≠ 2 := fun h => hreset (Or.inl h)
    have h5 : pre.length ≠ 4 := fun h => hreset (Or.inr h)
    have hlevel := D.p1FifthEffectiveLevel_cons_of_not_reset N q pre h3 h5
    rw [hlevel] at htest ⊢
    rw [ordinaryParityRosserPolicy_eq_full_on_valid_prefix false
      (D.p1FifthEffectiveLevel N pre) pre positive q hpre hsign hq (by simp) hsort] at htest
    exact of_decide_eq_true htest

/-- The valid chosen sublist carries complete ordinary admissibility at
its actual final effective level, not only its last parity test. -/
theorem p1ValidSelection_upperFifth_admissible (D : HistoricalPrefixCapData) (N : ℝ)
    (chosen pre : List ℕ) (positive : Bool)
    (hpre : ordinaryRosserPrefixAdmissible false (D.p1FifthEffectiveLevel N pre) pre)
    (hsign : positive = evenListLength pre)
    (hprime : ∀ p ∈ chosen.reverse ++ pre, p.Prime)
    (hsort : (chosen.reverse ++ pre).Pairwise (· < ·))
    (hvalid : FirstExitValidSelection (D.upperFifthPolicy N) pre positive chosen) :
    ordinaryRosserPrefixAdmissible false
      (D.p1FifthEffectiveLevel N (chosen.reverse ++ pre)) (chosen.reverse ++ pre) := by
  induction chosen generalizing pre positive with
  | nil => simpa only [List.reverse_nil, List.nil_append] using hpre
  | cons q qs ih =>
      have hprime' : ∀ p ∈ qs.reverse ++ q :: pre, p.Prime := by
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hprime
      have hsort' : (qs.reverse ++ q :: pre).Pairwise (· < ·) := by
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hsort
      obtain ⟨htest, htail⟩ := hvalid
      have hnext := D.p1UpperFifthPolicy_oneStep_admissible N pre positive q hpre hsign
        (hprime' q (by simp)) (List.pairwise_append.mp hsort').2.1 htest
      have hsign' : (!positive) = evenListLength (q :: pre) := by rw [hsign]; rfl
      have h := ih (q :: pre) (!positive) hnext hsign' hprime' hsort' htail
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using h

/-- Every actual retained leaf is fully ordinary-admissible at its current
effective level. The root and unit branch are paid by old>0 and N>1. -/
theorem p1UpperFifth_retainedLeaf_admissible (D : HistoricalPrefixCapData)
    (N : ℝ) (hN : 1 < N) (hold : 0 < D.old) (h : ℕ → ℝ)
    (carrier : List ℕ) (hprime : ∀ p ∈ carrier, p.Prime)
    (hsort : carrier.Pairwise (· > ·)) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (D.upperFifthPolicy N) h [] true 1 carrier) :
    ordinaryRosserPrefixAdmissible false (D.p1FifthEffectiveLevel N leaf.selected) leaf.selected := by
  obtain ⟨chosen, hsub, hvalid, heq⟩ :=
    exists_validSelection_of_mem_firstExitRetainedLeaves (D.upperFifthPolicy N) h
      [] carrier true 1 leaf hleaf
  have hQ : 1 < N ^ (D.old : ℝ) := by
    have holdR : (0 : ℝ) < D.old := by exact_mod_cast hold
    simpa using Real.rpow_lt_rpow_of_exponent_lt hN holdR
  have hroot : ordinaryRosserPrefixAdmissible false (D.p1FifthEffectiveLevel N []) [] := by
    simpa only [p1FifthEffectiveLevel, List.length_nil, Nat.zero_le, if_true] using
      ordinaryRosserPrefixAdmissible_nil false hQ
  have hp : ∀ p ∈ chosen.reverse ++ [], p.Prime := by
    intro p hp
    have hpchosen : p ∈ chosen := by simpa only [List.append_nil, List.mem_reverse] using hp
    exact hprime p (hsub.subset hpchosen)
  have hs : (chosen.reverse ++ []).Pairwise (· < ·) := by
    simpa only [List.append_nil, List.pairwise_reverse] using hsort.sublist hsub
  have hadm := D.p1ValidSelection_upperFifth_admissible N chosen [] true hroot rfl hp hs hvalid
  simpa only [← heq] using hadm

theorem p1ActualUpperFifth_retainedLeaf_admissible (D : HistoricalPrefixCapData)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (hold : 0 < D.old) (z : ℝ)
    (h : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (D.upperFifthPolicy (N : ℝ)) h [] true 1
      (roughPrimeUniverse N cap 0 z)) :
    ordinaryRosserPrefixAdmissible false
      (D.p1FifthEffectiveLevel (N : ℝ) leaf.selected) leaf.selected := by
  exact D.p1UpperFifth_retainedLeaf_admissible (N : ℝ) hN hold h _
    (fun _ hp => mem_roughPrimeUniverse_prime hp)
    (roughPrimeUniverse_pairwise_gt N cap 0 z) leaf hleaf

/-- At lengths three and four, the actual inherited level is the frozen Q3. -/
theorem p1ActualUpperFifth_retainedLeaf_third_admissible (D : HistoricalPrefixCapData)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (hold : 0 < D.old) (z : ℝ)
    (h : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (D.upperFifthPolicy (N : ℝ)) h [] true 1
      (roughPrimeUniverse N cap 0 z))
    (hlen3 : 3 ≤ leaf.selected.length) (hlen4 : leaf.selected.length ≤ 4) :
    ordinaryRosserPrefixAdmissible false
      (D.level3 (N : ℝ) (rosserAncestor 3 leaf.selected)) leaf.selected := by
  have h2 : ¬leaf.selected.length ≤ 2 := by omega
  simpa only [p1FifthEffectiveLevel, if_neg h2, if_pos hlen4] using
    D.p1ActualUpperFifth_retainedLeaf_admissible N cap hN hold z h leaf hleaf

/-- At every later rank, complete validity is at the frozen Q5. -/
theorem p1ActualUpperFifth_retainedLeaf_fifth_admissible (D : HistoricalPrefixCapData)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (hold : 0 < D.old) (z : ℝ)
    (h : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (D.upperFifthPolicy (N : ℝ)) h [] true 1
      (roughPrimeUniverse N cap 0 z)) (hlen : 5 ≤ leaf.selected.length) :
    ordinaryRosserPrefixAdmissible false
      (D.level5 (N : ℝ) (rosserAncestor 5 leaf.selected)) leaf.selected := by
  have h2 : ¬leaf.selected.length ≤ 2 := by omega
  have h4 : ¬leaf.selected.length ≤ 4 := by omega
  simpa only [p1FifthEffectiveLevel, if_neg h2, if_neg h4] using
    D.p1ActualUpperFifth_retainedLeaf_admissible N cap hN hold z h leaf hleaf

theorem p1FifthEffectiveLevel_le_ceiling (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (theta : ℚ) (hceil : D.p1CapCeilingCheck theta = true)
    (N : ℝ) (hN : 1 ≤ N) (history : List ℕ) :
    D.p1FifthEffectiveLevel N history ≤ N ^ (theta : ℝ) := by
  unfold p1FifthEffectiveLevel
  split_ifs with h2 h4
  · apply Real.rpow_le_rpow_of_exponent_le hN
    exact_mod_cast (D.p1CapCeilingCheck_sound theta hceil).1
  · exact D.p1Level3_le_power_ceiling hab theta hceil N hN _
  · exact D.p1Level5_le_power_ceiling hab theta hceil N hN _

/-- The full-prefix predicate supplies prod<Q; the independent upper
check then bounds Q. This includes the unit leaf. -/
theorem p1ActualUpperFifth_retainedLeaf_prod_lt_ceiling (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (theta : ℚ) (hceil : D.p1CapCeilingCheck theta = true)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (hold : 0 < D.old) (z : ℝ)
    (h : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (D.upperFifthPolicy (N : ℝ)) h [] true 1
      (roughPrimeUniverse N cap 0 z)) :
    (leaf.selected.prod : ℝ) < (N : ℝ) ^ (theta : ℝ) := by
  exact (D.p1ActualUpperFifth_retainedLeaf_admissible N cap hN hold z h leaf hleaf).1.trans_le
    (D.p1FifthEffectiveLevel_le_ceiling hab theta hceil (N : ℝ) hN.le leaf.selected)

/-- A nonzero coefficient belongs to the exact assembly rough support. -/
theorem p1FifthRoughCoefficient_mem_support (D : HistoricalPrefixCapData)
    (N cap : ℕ) (z : ℝ) (d : ℕ) (hd : D.p1FifthRoughCoefficient N cap z d ≠ 0) :
    d ∈ D.p1FifthRoughSupport N cap z := by
  by_contra hnot
  have hzero : D.p1FifthRoughCoefficient N cap z d = 0 := by
    have hnot' : d ∉ oddFirstExitRetainedModuli (D.p1FifthRetainOdd N) (fun _ => 1)
        (roughPrimeUniverse N cap 0 z) := hnot
    simp only [p1FifthRoughCoefficient, fixedRoughCoefficient,
      oddFirstExitRetainedCoefficient, if_neg hnot', Int.cast_zero]
  exact hd hzero

/-- Every displayed rough support modulus has the strict rational-cap
ceiling. No condition is imposed on a physical small-weight product. -/
theorem p1FifthRoughSupport_lt_ceiling (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (theta : ℚ) (hceil : D.p1CapCeilingCheck theta = true)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (hold : 0 < D.old) (z : ℝ)
    (d : ℕ) (hd : d ∈ D.p1FifthRoughSupport N cap z) :
    (d : ℝ) < (N : ℝ) ^ (theta : ℝ) := by
  obtain ⟨leaf, hleaf, hprod⟩ :=
    (mem_oddFirstExitRetainedModuli (D.p1FifthRetainOdd N) (fun _ => 1)
      (roughPrimeUniverse N cap 0 z) d).mp hd
  have hpolicy : oddFirstExitPolicy (D.p1FifthRetainOdd N) = D.upperFifthPolicy (N : ℝ) :=
    (D.upperFifthPolicy_eq_oddFirstExitPolicy (N : ℝ)).symm
  have hleaf' : leaf ∈ firstExitRetainedLeaves (D.upperFifthPolicy (N : ℝ)) (fun _ => 1)
      [] true 1 (roughPrimeUniverse N cap 0 z) := by
    simpa only [oddFirstExitRetainedLeaves, hpolicy] using hleaf
  rw [← hprod]
  exact D.p1ActualUpperFifth_retainedLeaf_prod_lt_ceiling hab theta hceil
    N cap hN hold z (fun _ => 1) leaf hleaf'

/-- Checked terminal interface for the same assembly coefficient. The
original levelCheck is retained as a separate successful check; its role
is inherited monotonicity, whereas cutoff follows from complete validity
and the ceiling check. -/
theorem p1FifthRoughCoefficient_checked_lt_ceiling (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (hlevels : D.levelCheck = true)
    (theta : ℚ) (hceil : D.p1CapCeilingCheck theta = true)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (hold : 0 < D.old) (z : ℝ)
    (d : ℕ) (hd : D.p1FifthRoughCoefficient N cap z d ≠ 0) :
    D.levelCheck = true ∧ (d : ℝ) < (N : ℝ) ^ (theta : ℝ) := by
  exact ⟨hlevels, D.p1FifthRoughSupport_lt_ceiling hab theta hceil N cap hN hold z d
    (D.p1FifthRoughCoefficient_mem_support N cap z d hd)⟩

theorem p1FifthRoughCoefficient_lt_ceiling (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (hlevels : D.levelCheck = true)
    (theta : ℚ) (hceil : D.p1CapCeilingCheck theta = true)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (hold : 0 < D.old) (z : ℝ)
    (d : ℕ) (hd : D.p1FifthRoughCoefficient N cap z d ≠ 0) :
    (d : ℝ) < (N : ℝ) ^ (theta : ℝ) := by
  exact (D.p1FifthRoughCoefficient_checked_lt_ceiling hab hlevels theta hceil
    N cap hN hold z d hd).2

end HistoricalPrefixCapData

end

end ImbalancedChen
