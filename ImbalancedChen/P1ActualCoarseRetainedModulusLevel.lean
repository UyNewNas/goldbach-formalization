import ImbalancedChen.P1ActualCoarseLevelCeiling
import ImbalancedChen.P1ActualCoarseFixedCoefficient
import ImbalancedChen.FirstExitHistoricalLevels

/-!
Actual retained leaves, including even terminal ranks, satisfy the COMPLETE
ordinary Rosser predicate at the actual coarse frozen level. Inactive even
admission alone does not imply this: the proof propagates full validity using
the sorted prime carrier and the genuine one-step upper Rosser dictionary.

Ranks zero/one/two use the original initial policy; that policy still includes
the literal firstStop. Rank three reads its actual raw selected/fallback level;
all later selections keep that same ancestor. Only the ROUGH coefficient is
bounded here. No small-weight attachment or enlarged physical exponent occurs.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical
open HistoricalThirdCoarse P1ThirdFallbackSupport P1ActualCoarseLevelCeiling
open VariableEnvelope

namespace P1ActualCoarseRetainedModulusLevel

theorem frozenLevel_short (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (pre : List ℕ) (hlen : pre.length ≤ 2) :
    frozenLevel e chi m omega N pre = N ^ initial e := by
  unfold frozenLevel
  apply rawLevel_inactive
  intro ha
  have hlen3 := ha.1
  rw [rosserAncestor_length] at hlen3
  omega

/-- The original firstStop restriction only strengthens the initial odd test. -/
theorem initial_pass_implies_ordinaryParity (e : ℝ) (m : ℕ) (N : ℝ)
    (positive : Bool) (pre : List ℕ)
    (ht : initialPolicy e m N positive pre = true) :
    ordinaryParityRosserPolicy false (N ^ initial e) positive pre = true := by
  cases positive with
  | false =>
      have hfull : ordinaryRosserPrefixAdmissible false (N ^ initial e) pre ∧
          (pre.length = 1 → firstStop e m N pre) := by
        simpa [initialPolicy, oddFirstExitPolicy, imp_iff_not_or] using ht
      simpa [ordinaryParityRosserPolicy, oddFirstExitPolicy] using hfull.1
  | true => simp [ordinaryParityRosserPolicy, oddFirstExitPolicy]

private theorem evenListLength_eq_decide_even (pre : List ℕ) :
    evenListLength pre = decide (Even pre.length) := by
  induction pre with
  | nil => simp [evenListLength]
  | cons p ps ih =>
      simp only [evenListLength, ih, List.length_cons, Nat.even_add_one, decide_not]

/-- Full validity is propagated through the actual retained-LEAF recursion.
The incoming validity/sign are induction invariants, not final caller premises. -/
theorem mem_retained_leaf_valid_from_entry
    (e chi : ℝ) (m : ℕ) (omega N : ℝ) (weight : ℕ → ℝ)
    (pre carrier : List ℕ) (positive : Bool) (mass : ℝ)
    (hpre : ordinaryRosserPrefixAdmissible false (frozenLevel e chi m omega N pre) pre)
    (hsign : positive = evenListLength pre)
    (hprime : ∀ p ∈ carrier, p.Prime)
    (hsort : (carrier.reverse ++ pre).Pairwise (· < ·))
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (policy e chi m omega N)
      weight pre positive mass carrier) :
    ordinaryRosserPrefixAdmissible false
        (frozenLevel e chi m omega N leaf.selected) leaf.selected ∧
      leaf.positive = evenListLength leaf.selected := by
  induction carrier generalizing pre positive mass with
  | nil =>
      simp only [firstExitRetainedLeaves, List.mem_singleton] at hleaf
      subst leaf
      exact ⟨hpre, hsign⟩
  | cons q qs ih =>
      have hsort' : (qs.reverse ++ q :: pre).Pairwise (· < ·) := by
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hsort
      have hskipSort : (qs.reverse ++ pre).Pairwise (· < ·) :=
        hsort'.sublist ((List.Sublist.refl qs.reverse).append ((List.Sublist.refl pre).cons q))
      have hprime' : ∀ p ∈ qs, p.Prime :=
        fun p hp => hprime p (List.mem_cons_of_mem q hp)
      rw [firstExitRetainedLeaves, List.mem_append] at hleaf
      rcases hleaf with hskip | hselect
      · exact ih pre positive mass hpre hsign hprime' hskipSort hskip
      · by_cases ht : policy e chi m omega N (!positive) (q :: pre) = true
        · rw [if_pos ht] at hselect
          have hnext : ordinaryRosserPrefixAdmissible false
              (frozenLevel e chi m omega N (q :: pre)) (q :: pre) := by
            by_cases hshort : (q :: pre).length ≤ 2
            · have hpreShort : pre.length ≤ 2 := by simp only [List.length_cons] at hshort; omega
              have hinitial : ordinaryRosserPrefixAdmissible false (N ^ initial e) pre := by
                rw [frozenLevel_short e chi m omega N pre hpreShort] at hpre
                exact hpre
              have htinitial : initialPolicy e m N (!positive) (q :: pre) = true := by
                rw [← policy_through_two e chi m omega N (!positive) (q :: pre) hshort]
                exact ht
              have hord := initial_pass_implies_ordinaryParity e m N (!positive)
                (q :: pre) htinitial
              rw [ordinaryParityRosserPolicy_eq_full_on_valid_prefix false (N ^ initial e)
                pre positive q hinitial hsign (hprime q (by simp))
                (by simp) (List.pairwise_append.mp hsort').2.1] at hord
              rw [frozenLevel_short e chi m omega N (q :: pre) hshort]
              exact of_decide_eq_true hord
            · have ht' : ordinaryParityRosserPolicy false
                  (rawLevel e chi m omega N (rosserAncestor 3 (q :: pre)))
                  (!positive) (q :: pre) = true := by
                simpa only [policy, thirdCappedUpperPolicy, firstExitDepthSplicePolicy,
                  if_neg hshort, frozenParityRosserPolicy, ancestorFrozenPolicy] using ht
              change ordinaryRosserPrefixAdmissible false
                (rawLevel e chi m omega N (rosserAncestor 3 (q :: pre))) (q :: pre)
              by_cases hdeep : 3 ≤ pre.length
              · rw [rosserAncestor_cons 3 q pre hdeep] at ht' ⊢
                rw [ordinaryParityRosserPolicy_eq_full_on_valid_prefix false
                  (rawLevel e chi m omega N (rosserAncestor 3 pre)) pre positive q
                  hpre hsign (hprime q (by simp)) (by simp)
                  (List.pairwise_append.mp hsort').2.1] at ht'
                exact of_decide_eq_true ht'
              · have hlen2 : pre.length = 2 := by simp only [List.length_cons] at hshort; omega
                have hs : positive = true := by
                  rw [hsign, evenListLength_eq_decide_even, hlen2]
                  decide
                simpa only [hs, Bool.not_true, ordinaryParityRosserPolicy,
                  Bool.false_eq_true, if_false, oddFirstExitPolicy, Bool.false_or,
                  decide_eq_true_eq] using ht'
          have hsign' : (!positive) = evenListLength (q :: pre) := by rw [hsign]; rfl
          exact ih (q :: pre) (!positive) (mass * weight q) hnext hsign'
            hprime' hsort' hselect
        · simp only [if_neg ht, List.not_mem_nil] at hselect

/-- The empty history needs its own strict level bound, since its product is 1. -/
theorem initial_level_gt_one (e N : ℝ) (heupper : 2 * e < (299 / 500 : ℝ))
    (hN : 1 < N) : 1 < N ^ initial e := by
  have hpos : (0 : ℝ) < initial e := by
    dsimp [initial, extendedDistributionCap]
    linarith
  simpa only [Real.rpow_zero] using Real.rpow_lt_rpow_of_exponent_lt hN hpos

/-- Root and short-rank validity are discharged; only genuine prime/sort data remain. -/
theorem retained_leaf_valid
    (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (heupper : 2 * e < (299 / 500 : ℝ)) (hN : 1 < N)
    (weight : ℕ → ℝ) (carrier : List ℕ)
    (hprime : ∀ p ∈ carrier, p.Prime) (hsort : carrier.Pairwise (· > ·))
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (policy e chi m omega N)
      weight [] true 1 carrier) :
    ordinaryRosserPrefixAdmissible false
      (frozenLevel e chi m omega N leaf.selected) leaf.selected := by
  have hroot : ordinaryRosserPrefixAdmissible false
      (frozenLevel e chi m omega N []) [] := by
    rw [frozenLevel_short e chi m omega N [] (by simp)]
    exact ordinaryRosserPrefixAdmissible_nil false (initial_level_gt_one e N heupper hN)
  exact (mem_retained_leaf_valid_from_entry e chi m omega N weight [] carrier true 1
    hroot rfl hprime (by simpa only [List.append_nil, List.pairwise_reverse] using hsort)
    leaf hleaf).1

/-- All actual rough leaves satisfy the complete predicate, including even rank. -/
theorem actual_retained_leaf_valid
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * e < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (policy e chi m omega (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z)) :
    ordinaryRosserPrefixAdmissible false
      (frozenLevel e chi m omega (N : ℝ) leaf.selected) leaf.selected := by
  exact retained_leaf_valid e chi m omega (N : ℝ) heupper hN weight _
    (fun _ hp => mem_roughPrimeUniverse_prime hp)
    (roughPrimeUniverse_pairwise_gt N cap w z) leaf hleaf

theorem actual_retained_leaf_prod_lt_frozen
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * e < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (policy e chi m omega (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z)) :
    (leaf.selected.prod : ℝ) < frozenLevel e chi m omega (N : ℝ) leaf.selected := by
  exact (actual_retained_leaf_valid e chi m omega N cap w z heupper hN weight leaf hleaf).1

theorem actual_retained_leaf_prod_lt_initial
    (e chi : ℝ) (he : 0 ≤ e) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * e < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (policy e chi m omega (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z)) :
    (leaf.selected.prod : ℝ) < (N : ℝ) ^ initial e := by
  exact (actual_retained_leaf_prod_lt_frozen e chi m omega N cap w z
    heupper hN weight leaf hleaf).trans_le
      (frozenLevel_le_initial e chi he m omega (N : ℝ) hN.le leaf.selected)

/-- A stronger Lambda bound is used only for a real active selected ancestor. -/
theorem actual_supported_leaf_prod_lt_lambda
    (e chi : ℝ) (he : 0 ≤ e) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * e < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (policy e chi m omega (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z))
    (hs : frozenSupported e chi m omega (N : ℝ) leaf.selected) :
    (leaf.selected.prod : ℝ) < (N : ℝ) ^ (VariableEnvelope.cap - 2 * e) := by
  exact (actual_retained_leaf_prod_lt_frozen e chi m omega N cap w z
    heupper hN weight leaf hleaf).trans_le
      (rawLevel_supported_le_lambda e chi he m omega (N : ℝ) hN.le
        (rosserAncestor 3 leaf.selected) hs)

/-- Exact support of the original fixed ROUGH coefficient, including the unit. -/
theorem roughSupport_modulus_lt_initial
    (e chi : ℝ) (he : 0 ≤ e) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * e < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ)) (d : ℕ)
    (hd : d ∈ P1ActualCoarseFixedCoefficient.roughSupport e chi m omega N cap w z) :
    (d : ℝ) < (N : ℝ) ^ initial e := by
  rw [P1ActualCoarseFixedCoefficient.support_eq_original_retainedModuli] at hd
  obtain ⟨leaf, hleaf, hprod⟩ :=
    (mem_firstExitRetainedModuli (policy e chi m omega (N : ℝ))
      (roughPrimeUniverse N cap w z) d).mp hd
  simpa only [hprod] using actual_retained_leaf_prod_lt_initial e chi he m omega
    N cap w z heupper hN (fun _ => 1) leaf hleaf

theorem roughCoefficient_nonzero_modulus_lt_initial
    (e chi : ℝ) (he : 0 ≤ e) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * e < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ)) (d : ℕ)
    (hc : P1ActualCoarseFixedCoefficient.roughCoefficient e chi m omega N cap w z d ≠ 0) :
    (d : ℝ) < (N : ℝ) ^ initial e := by
  exact roughSupport_modulus_lt_initial e chi he m omega N cap w z heupper hN d
    (P1ActualCoarseFixedCoefficient.coefficient_nonzero_mem_support
      e chi m omega N cap w z d hc)

/-- A nonzero coefficient carries a real fully valid leaf; any stronger bound
is conditional on that leaf's actual selected/rough-activated ancestor. -/
theorem roughCoefficient_nonzero_valid_leaf_witness
    (e chi : ℝ) (he : 0 ≤ e) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * e < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ)) (d : ℕ)
    (hc : P1ActualCoarseFixedCoefficient.roughCoefficient e chi m omega N cap w z d ≠ 0) :
    ∃ leaf : FirstExitLeaf ℕ,
      leaf ∈ firstExitRetainedLeaves (policy e chi m omega (N : ℝ))
        (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z) ∧
      leaf.selected.prod = d ∧
      ordinaryRosserPrefixAdmissible false
        (frozenLevel e chi m omega (N : ℝ) leaf.selected) leaf.selected ∧
      (d : ℝ) < (N : ℝ) ^ initial e ∧
      (frozenSupported e chi m omega (N : ℝ) leaf.selected →
        (d : ℝ) < (N : ℝ) ^ (VariableEnvelope.cap - 2 * e)) := by
  have hd := P1ActualCoarseFixedCoefficient.coefficient_nonzero_mem_support
    e chi m omega N cap w z d hc
  rw [P1ActualCoarseFixedCoefficient.support_eq_original_retainedModuli] at hd
  obtain ⟨leaf, hleaf, hprod⟩ :=
    (mem_firstExitRetainedModuli (policy e chi m omega (N : ℝ))
      (roughPrimeUniverse N cap w z) d).mp hd
  refine ⟨leaf, hleaf, hprod,
    actual_retained_leaf_valid e chi m omega N cap w z heupper hN (fun _ => 1) leaf hleaf,
    roughCoefficient_nonzero_modulus_lt_initial e chi he m omega N cap w z heupper hN d hc,
    ?_⟩
  intro hs
  simpa only [hprod] using actual_supported_leaf_prod_lt_lambda e chi he m omega
    N cap w z heupper hN (fun _ => 1) leaf hleaf hs

theorem roughCoefficient_zero_of_initial_le
    (e chi : ℝ) (he : 0 ≤ e) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * e < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ)) (d : ℕ)
    (hd : (N : ℝ) ^ initial e ≤ (d : ℝ)) :
    P1ActualCoarseFixedCoefficient.roughCoefficient e chi m omega N cap w z d = 0 := by
  by_contra hc
  exact (not_lt_of_ge hd)
    (roughCoefficient_nonzero_modulus_lt_initial e chi he m omega N cap w z heupper hN d hc)

end P1ActualCoarseRetainedModulusLevel
end
end ImbalancedChen
