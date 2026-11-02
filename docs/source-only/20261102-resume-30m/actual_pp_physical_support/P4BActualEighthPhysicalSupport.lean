import ImbalancedChen.P4AOriginalEighthParentPhysicalLedger
import ImbalancedChen.Part3ActualCompactAllRankSupport
import ImbalancedChen.ActualUpperCountingInputs

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This file concerns the EXISTING local descending17/ascending19 actions.
It does not identify either structural action with all 87 adopted cells.
The ninth odd query resets the complete ordinary predicate; subsequent
even queries inherit it. Thus an actual nonzero physical coefficient
supplies full-word support, with short and inherited branches explicit.
No Supported, CapPlan, distribution, cap-ceiling, or class-membership
premise occurs. The still-missing full adopted compiler is not replaced.
-/

namespace ImbalancedChen.P4BActualEighthPhysicalSupport

noncomputable section
open scoped Classical
open P4AOriginalEighthParentPhysicalLedger

private theorem evenListLength_eq_decide_even (pre : List ℕ) :
    evenListLength pre = decide (Even pre.length) := by
  induction pre with
  | nil => simp [evenListLength]
  | cons p ps ih =>
      simp only [evenListLength, ih, List.length_cons, Nat.even_add_one, decide_not]

/-- A leaf, not just its rank-eight frontier, keeps the complete predicate
at the physical eighth level. Nothing is asserted about short leaves. -/
theorem eighth_leaf_valid_from_entry
    (parent : Bool → List ℕ → Bool) (Q8 : List ℕ → ℝ)
    (weight : ℕ → ℝ) (pre carrier : List ℕ) (positive : Bool) (mass : ℝ)
    (hpre : 9 ≤ pre.length → ordinaryRosserPrefixAdmissible false
      (Q8 (rosserAncestor 8 pre)) pre)
    (hsign : positive = evenListLength pre)
    (hprime : ∀ p ∈ carrier, p.Prime)
    (hsort : (carrier.reverse ++ pre).Pairwise (· < ·))
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (firstExitDepthSplicePolicy 8 parent (frozenParityRosserPolicy false 8 Q8))
      weight pre positive mass carrier) :
    (9 ≤ leaf.selected.length → ordinaryRosserPrefixAdmissible false
      (Q8 (rosserAncestor 8 leaf.selected)) leaf.selected) ∧
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
      have hprime' : ∀ p ∈ qs, p.Prime := fun p hp => hprime p (List.mem_cons_of_mem q hp)
      rw [firstExitRetainedLeaves, List.mem_append] at hleaf
      rcases hleaf with hskip | hselect
      · exact ih pre positive mass hpre hsign hprime' hskipSort hskip
      · by_cases ht : firstExitDepthSplicePolicy 8 parent
            (frozenParityRosserPolicy false 8 Q8) (!positive) (q :: pre) = true
        · rw [if_pos ht] at hselect
          have hnext : 9 ≤ (q :: pre).length → ordinaryRosserPrefixAdmissible false
              (Q8 (rosserAncestor 8 (q :: pre))) (q :: pre) := by
            intro hlen
            have hdeep : ¬(q :: pre).length ≤ 8 := by omega
            have ht' : ordinaryParityRosserPolicy false
                (Q8 (rosserAncestor 8 (q :: pre))) (!positive) (q :: pre) = true := by
              simpa only [firstExitDepthSplicePolicy, if_neg hdeep,
                frozenParityRosserPolicy, ancestorFrozenPolicy] using ht
            by_cases hp : 9 ≤ pre.length
            · rw [rosserAncestor_cons 8 q pre (by omega)] at ht' ⊢
              rw [ordinaryParityRosserPolicy_eq_full_on_valid_prefix false
                (Q8 (rosserAncestor 8 pre)) pre positive q (hpre hp) hsign
                (hprime q (by simp)) (by simp) (List.pairwise_append.mp hsort').2.1] at ht'
              exact of_decide_eq_true ht'
            · have hlen8 : pre.length = 8 := by simp only [List.length_cons] at hlen; omega
              have hs : positive = true := by
                rw [hsign, evenListLength_eq_decide_even, hlen8]
                decide
              simpa only [hs, Bool.not_true, ordinaryParityRosserPolicy, Bool.false_eq_true,
                if_false, oddFirstExitPolicy, Bool.false_or, decide_eq_true_eq] using ht'
          have hsign' : (!positive) = evenListLength (q :: pre) := by rw [hsign]; rfl
          exact ih (q :: pre) (!positive) (mass * weight q) hnext hsign' hprime' hsort' hselect
        · simp only [if_neg ht, List.not_mem_nil] at hselect

/-- Normalize only the already supplied odd policy, exactly as the
physical coefficient does. No assumption on unused base-even queries. -/
theorem action_odd_policy_eq_splice (a : Action) (N : ℝ)
    (lambda6 : List ℕ → ℝ) (base : Bool → List ℕ → Bool) :
    oddFirstExitPolicy (actionPolicy a N lambda6 base false) =
      firstExitDepthSplicePolicy 8 (oddFirstExitPolicy (parentPolicy N lambda6 base false))
        (frozenParityRosserPolicy false 8 (actionLevel a N lambda6)) := by
  funext positive pre
  cases positive <;>
    simp [oddFirstExitPolicy, actionPolicy, replacement, firstExitDepthSplicePolicy,
      frozenParityRosserPolicy, ancestorFrozenPolicy, ordinaryParityRosserPolicy]

/-- Branch names are those of the existing policy; this is a dictionary,
not a new cap or an adopted-policy declaration. -/
def actionExponent (a : Action) (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) : ℝ :=
  match a with
  | .descending17 => P4ASlot17DescendingChargedFrontierSourceOnly.raisedExponent N lambda6 pre
  | .ascending19 => P4ASlot19ChargedFrontierSourceOnly.raisedExponent N lambda6 pre

theorem actionLevel_eq (a : Action) (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) :
    actionLevel a N lambda6 pre = N ^ actionExponent a N lambda6 pre := by
  cases a <;> rfl

/-- The actual branch test either inherits the sixth ancestor exactly or
selects a cap below 153/256. No upper bound on lambda6 is assumed. -/
theorem actionExponent_inherited_or_selected (a : Action) (N : ℝ)
    (lambda6 : List ℕ → ℝ) (pre : List ℕ) :
    actionExponent a N lambda6 pre = lambda6 (rosserAncestor 6 pre) ∨
      actionExponent a N lambda6 pre < (153 / 256 : ℝ) := by
  cases a with
  | descending17 =>
      change P4ASlot17DescendingChargedFrontierSourceOnly.raisedExponent N lambda6 pre =
        lambda6 (rosserAncestor 6 pre) ∨
        P4ASlot17DescendingChargedFrontierSourceOnly.raisedExponent N lambda6 pre < 153 / 256
      unfold P4ASlot17DescendingChargedFrontierSourceOnly.raisedExponent
      dsimp only
      split_ifs with h
      · right
        have hcap := (P4ASlot17DescendingChargedFrontierSourceOnly.descending_license h).2.trans_le
          (VariableEnvelope.v_le_cap _)
        simpa only [VariableEnvelope.cap] using hcap
      · left
        rfl
  | ascending19 =>
      change P4ASlot19ChargedFrontierSourceOnly.raisedExponent N lambda6 pre =
        lambda6 (rosserAncestor 6 pre) ∨
        P4ASlot19ChargedFrontierSourceOnly.raisedExponent N lambda6 pre < 153 / 256
      unfold P4ASlot19ChargedFrontierSourceOnly.raisedExponent
      dsimp only
      split_ifs with h
      · right
        rw [P2OriginalThirdMinorantLogDictionarySourceOnly.newCap_active h.1]
        have hcap := VariableEnvelope.v_le_cap
          (P2OriginalThirdMinorantLogDictionarySourceOnly.selectedSum
            (primeHistoryLogCoordinates N 8 pre))
        dsimp only [VariableEnvelope.cap] at hcap
        dsimp only [P2OriginalThirdMinorantLogDictionarySourceOnly.eta]
        linarith
      · left
        rfl

/-- An actual retained modulus supplies its full chronological word.
The only alternatives are its true short rank and full ordinary support
at the true frozen eighth level, including every inherited odd test. -/
theorem rough_factor_full_word (a : Action) (N cap : ℕ) (w z : ℝ)
    (lambda6 : List ℕ → ℝ) (base : Bool → List ℕ → Bool) {d : ℕ}
    (hd : d ∈ fixedRoughSupport (actionPolicy a (N : ℝ) lambda6 base false) N cap w z) :
    ∃ leaf : FirstExitLeaf ℕ,
      leaf ∈ firstExitRootLeaves
        (oddFirstExitPolicy (actionPolicy a (N : ℝ) lambda6 base false)) (fun _ => 1)
        (roughPrimeUniverse N cap w z) ∧
      leaf.selected.prod = d ∧
      (leaf.selected.length ≤ 8 ∨
        (ordinaryRosserPrefixAdmissible false
          (actionLevel a (N : ℝ) lambda6 (rosserAncestor 8 leaf.selected)) leaf.selected ∧
        actualDwellSupport (actionLevel a (N : ℝ) lambda6 (rosserAncestor 8 leaf.selected))
          leaf.selected.reverse)) := by
  change d ∈ firstExitRetainedModuli
    (oddFirstExitPolicy (actionPolicy a (N : ℝ) lambda6 base false))
    (roughPrimeUniverse N cap w z) at hd
  obtain ⟨leaf, hleaf, hprod⟩ := (mem_firstExitRetainedModuli _ _ d).mp hd
  refine ⟨leaf, hleaf, hprod, ?_⟩
  by_cases hshort : leaf.selected.length ≤ 8
  · exact Or.inl hshort
  · right
    have hleaf' := hleaf
    rw [action_odd_policy_eq_splice] at hleaf'
    have hv := eighth_leaf_valid_from_entry
      (oddFirstExitPolicy (parentPolicy (N : ℝ) lambda6 base false))
      (actionLevel a (N : ℝ) lambda6) (fun _ => 1) []
      (roughPrimeUniverse N cap w z) true 1 (by simp) rfl
      (fun _ hp => mem_roughPrimeUniverse_prime hp)
      (by simpa only [List.append_nil, List.pairwise_reverse]
        using roughPrimeUniverse_pairwise_gt N cap w z) leaf hleaf'
    have hadm := hv.1 (by omega)
    have hsub := mem_firstExitRootLeaves_selected_reverse_sublist _ _ _ leaf hleaf
    refine ⟨hadm, ?_⟩
    apply Part3.ActualCompactAllRankSupport.upper_set_dwell_support leaf.selected.reverse
      (fun p hp => mem_roughPrimeUniverse_prime (hsub.subset hp))
      ((roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub)
    simpa only [List.toFinset_reverse] using hadm.2

/-- Full physical modulus, with the actual sign-selected beta factor.
The one epsilon occurs in both the small cutoff and its physical level.
Every long branch has q below beta-level times its ACTUAL eighth level. -/
theorem attached_nonzero_full_word (a : Action) (nu r epsilon : ℝ)
    (lambda6 : ℕ → List ℕ → ℝ) (base : ℕ → Bool → List ℕ → Bool)
    (cap : ℕ → ℕ) (N q : ℕ)
    (hq : attachedUpperCoefficient nu r epsilon
      (fun M => actionPolicy a (M : ℝ) (lambda6 M) (base M) false) cap N q ≠ 0) :
    ∃ small rough : ℕ, ∃ leaf : FirstExitLeaf ℕ,
      leaf ∈ firstExitRootLeaves
        (oddFirstExitPolicy (actionPolicy a (N : ℝ) (lambda6 N) (base N) false)) (fun _ => 1)
        (roughPrimeUniverse N (cap N) ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))) ∧
      small ∈ actualSmallRosserSupport N (cap N) ((N : ℝ) ^ (nu * epsilon ^ 2)) ∧
      q = small * rough ∧ (small : ℝ) < (N : ℝ) ^ (nu * epsilon) ∧
      leaf.selected.prod = rough ∧
      (leaf.selected.length ≤ 8 ∨
        ((rough : ℝ) < actionLevel a (N : ℝ) (lambda6 N) (rosserAncestor 8 leaf.selected) ∧
        (q : ℝ) < (N : ℝ) ^ (nu * epsilon) *
          actionLevel a (N : ℝ) (lambda6 N) (rosserAncestor 8 leaf.selected) ∧
        actualDwellSupport
          (actionLevel a (N : ℝ) (lambda6 N) (rosserAncestor 8 leaf.selected))
          leaf.selected.reverse)) := by
  obtain ⟨small, hs, rough, hr, hprod, hsL, _hrne⟩ := actualSmallRoughRho_ne_zero_factors
    (actionPolicy a (N : ℝ) (lambda6 N) (base N) false) N (cap N)
    ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))
    ((N : ℝ) ^ (nu * epsilon)) hq
  obtain ⟨leaf, hleaf, hleafprod, hbranch⟩ := rough_factor_full_word a N (cap N)
    ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r)) (lambda6 N) (base N) hr
  refine ⟨small, rough, leaf, hleaf, hs, hprod, hsL, hleafprod, ?_⟩
  rcases hbranch with hshort | ⟨hadm, hsquares⟩
  · exact Or.inl hshort
  · right
    have hrQ : (rough : ℝ) < _ := by simpa only [hleafprod] using hadm.1
    refine ⟨hrQ, ?_, hsquares⟩
    have hL : 0 < (N : ℝ) ^ (nu * epsilon) :=
      lt_of_le_of_lt (Nat.cast_nonneg small) hsL
    rw [hprod, Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_right hsL.le (Nat.cast_nonneg rough)).trans_lt
      (mul_lt_mul_of_pos_left hrQ hL)

/-- No inherited branch is silently discarded. A common beta exponent
at most 1/1000 pays every selected long branch at the original theta.
The remaining two alternatives are precisely the unresolved source ports. -/
theorem attached_nonzero_original_theta_or_unresolved
    (a : Action) (nu r epsilon : ℝ)
    (lambda6 : ℕ → List ℕ → ℝ) (base : ℕ → Bool → List ℕ → Bool)
    (cap : ℕ → ℕ) (N q : ℕ) (hN : 2 ≤ N) (hbeta : nu * epsilon ≤ 1 / 1000)
    (hq : attachedUpperCoefficient nu r epsilon
      (fun M => actionPolicy a (M : ℝ) (lambda6 M) (base M) false) cap N q ≠ 0) :
    ∃ small rough : ℕ, ∃ leaf : FirstExitLeaf ℕ,
      leaf ∈ firstExitRootLeaves
        (oddFirstExitPolicy (actionPolicy a (N : ℝ) (lambda6 N) (base N) false)) (fun _ => 1)
        (roughPrimeUniverse N (cap N) ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))) ∧
      q = small * rough ∧ (small : ℝ) < (N : ℝ) ^ (nu * epsilon) ∧
      leaf.selected.prod = rough ∧
      (leaf.selected.length ≤ 8 ∨
        (q : ℝ) < (N : ℝ) ^
          (nu * epsilon + lambda6 N (rosserAncestor 6 (rosserAncestor 8 leaf.selected))) ∨
        (q : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ)) := by
  obtain ⟨small, rough, leaf, hleaf, _hs, hprod, hsL, hleafprod, hbranch⟩ :=
    attached_nonzero_full_word a nu r epsilon lambda6 base cap N q hq
  refine ⟨small, rough, leaf, hleaf, hprod, hsL, hleafprod, ?_⟩
  rcases hbranch with hshort | ⟨_hrQ, hqQ, _hsquares⟩
  · exact Or.inl hshort
  · right
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hNr
    rw [actionLevel_eq, ← Real.rpow_add hN0] at hqQ
    rcases actionExponent_inherited_or_selected a (N : ℝ) (lambda6 N)
      (rosserAncestor 8 leaf.selected) with hinherited | hselected
    · left
      simpa only [hinherited] using hqQ
    · right
      apply hqQ.trans_le
      apply Real.rpow_le_rpow_of_exponent_le hNr
      linarith only [hselected, hbeta]

end
end ImbalancedChen.P4BActualEighthPhysicalSupport
