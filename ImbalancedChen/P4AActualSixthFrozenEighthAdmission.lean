import ImbalancedChen.FirstExitHistoricalLevels
import ImbalancedChen.P4ASlot9InheritedActualAction

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

A sixth-rank action changes only tests after the retained sixth prefix.
Its seventh test is active upper parity and checks the complete prefix at
that actual sixth ancestor's level. Later even tests inherit full validity;
merely reading the eighth admission Boolean would not establish this.
The proof below follows the actual frontier recursion and pays the seventh
reset directly. No historical admission or component density is a premise.

The actual slot-9 action is instantiated below, including its unchanged
inherited-parent fallback. Complete original sixth-policy/87-domain data,
selected cell endpoints and all22 identification remain OPEN.
-/
namespace ImbalancedChen.P4AActualSixthFrozenEighthAdmission

noncomputable section
open scoped Classical

/-- Parent decisions through six, then the literal ancestor-frozen upper
continuation. Q6 is the physical level, not an auxiliary support cover. -/
def sixthPolicy (parent : Bool → List ℕ → Bool) (Q6 : List ℕ → ℝ) :
    Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 6 parent (frozenParityRosserPolicy false 6 Q6)

private theorem evenListLength_eq_decide_even (pre : List ℕ) :
    evenListLength pre = decide (Even pre.length) := by
  induction pre with
  | nil => simp [evenListLength]
  | cons p ps ih =>
      simp only [evenListLength, ih, List.length_cons, Nat.even_add_one, decide_not]

/-- At the first new odd test the complete inherited history is checked
at Q6. Every later selection uses the unchanged sixth ancestor and the
ordinary one-step admission theorem, including inactive even tests. -/
theorem mem_frontier_sixth_valid
    (parent : Bool → List ℕ → Bool) (Q6 : List ℕ → ℝ)
    (k : ℕ) (h : ℕ → ℝ) (pre carrier : List ℕ)
    (positive : Bool) (mass : ℝ)
    (hpre : 7 ≤ pre.length → ordinaryRosserPrefixAdmissible false
      (Q6 (rosserAncestor 6 pre)) pre)
    (hsign : positive = evenListLength pre)
    (hprime : ∀ p ∈ carrier, p.Prime)
    (hsort : (carrier.reverse ++ pre).Pairwise (· < ·))
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k (sixthPolicy parent Q6)
      h pre positive mass carrier) :
    (7 ≤ state.selectedPrefix.length → ordinaryRosserPrefixAdmissible false
      (Q6 (rosserAncestor 6 state.selectedPrefix)) state.selectedPrefix) ∧
      state.positive = evenListLength state.selectedPrefix := by
  induction carrier generalizing pre positive mass with
  | nil =>
      by_cases hk : k ≤ pre.length
      · simp only [firstExitDepthFrontier, if_pos hk, List.mem_singleton] at hstate
        subst state
        exact ⟨hpre, hsign⟩
      · simp [firstExitDepthFrontier, hk] at hstate
  | cons q qs ih =>
      by_cases hk : k ≤ pre.length
      · rw [firstExitDepthFrontier_of_rank_le_length k _ h pre (q :: qs)
          positive mass hk, List.mem_singleton] at hstate
        subst state
        exact ⟨hpre, hsign⟩
      · have hsort' : (qs.reverse ++ q :: pre).Pairwise (· < ·) := by
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hsort
        have hskipSort : (qs.reverse ++ pre).Pairwise (· < ·) :=
          hsort'.sublist ((List.Sublist.refl qs.reverse).append ((List.Sublist.refl pre).cons q))
        have hprime' : ∀ p ∈ qs, p.Prime :=
          fun p hp => hprime p (List.mem_cons_of_mem q hp)
        by_cases ht : sixthPolicy parent Q6 (!positive) (q :: pre) = true
        · rw [firstExitDepthFrontier, if_neg hk, if_pos ht, List.mem_append] at hstate
          rcases hstate with hskip | hselect
          · exact ih pre positive mass hpre hsign hprime' hskipSort hskip
          · have hnext : 7 ≤ (q :: pre).length → ordinaryRosserPrefixAdmissible false
                (Q6 (rosserAncestor 6 (q :: pre))) (q :: pre) := by
              intro hlen
              have hdeep : ¬(q :: pre).length ≤ 6 := by omega
              have ht' : ordinaryParityRosserPolicy false
                  (Q6 (rosserAncestor 6 (q :: pre))) (!positive) (q :: pre) = true := by
                simpa only [sixthPolicy, firstExitDepthSplicePolicy, if_neg hdeep,
                  frozenParityRosserPolicy, ancestorFrozenPolicy] using ht
              by_cases hp : 7 ≤ pre.length
              · rw [rosserAncestor_cons 6 q pre (by omega)] at ht' ⊢
                rw [ordinaryParityRosserPolicy_eq_full_on_valid_prefix false
                  (Q6 (rosserAncestor 6 pre)) pre positive q (hpre hp) hsign
                  (hprime q (by simp)) (by simp) (List.pairwise_append.mp hsort').2.1] at ht'
                exact of_decide_eq_true ht'
              · have hlen6 : pre.length = 6 := by simp only [List.length_cons] at hlen; omega
                have hs : positive = true := by
                  rw [hsign, evenListLength_eq_decide_even, hlen6]
                  decide
                simpa only [hs, Bool.not_true, ordinaryParityRosserPolicy, Bool.false_eq_true,
                  if_false, oddFirstExitPolicy, Bool.false_or, decide_eq_true_eq] using ht'
            have hsign' : (!positive) = evenListLength (q :: pre) := by rw [hsign]; rfl
            exact ih (q :: pre) (!positive) (mass * h q) hnext hsign' hprime' hsort' hselect
        · rw [firstExitDepthFrontier, if_neg hk, if_neg ht, List.append_nil] at hstate
          exact ih pre positive mass hpre hsign hprime' hskipSort hstate

/-- Actual capped, target-deleted carriers supply sorting and primality.
The presieve w is arbitrary: the argument is not limited to w=0. -/
theorem actual_frontier_admissible
    (parent : Bool → List ℕ → Bool) (Q6 : List ℕ → ℝ)
    (k : ℕ) (hk : 7 ≤ k) (N cap : ℕ) (w z : ℝ) (h : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k (sixthPolicy parent Q6)
      h [] true 1 (roughPrimeUniverse N cap w z)) :
    ordinaryRosserPrefixAdmissible false (Q6 (rosserAncestor 6 state.selectedPrefix))
      state.selectedPrefix := by
  have hv := mem_frontier_sixth_valid parent Q6 k h []
    (roughPrimeUniverse N cap w z) true 1 (by simp) rfl
    (fun _ hp => mem_roughPrimeUniverse_prime hp)
    (by simpa only [List.append_nil, List.pairwise_reverse]
      using roughPrimeUniverse_pairwise_gt N cap w z) state hstate
  apply hv.1
  rw [firstExitDepthFrontier_selected_length k _ h [] _ true 1 (by simp) state hstate]
  exact hk

/-- In particular rank eight is fully admissible, although its last
parity-safe Boolean is automatically true. No hHistory is requested. -/
theorem actual_rank_eight_admissible
    (parent : Bool → List ℕ → Bool) (Q6 : List ℕ → ℝ)
    (N cap : ℕ) (w z : ℝ) (h : ℕ → ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 8 (sixthPolicy parent Q6)
      h [] true 1 (roughPrimeUniverse N cap w z)) :
    ordinaryRosserPrefixAdmissible false (Q6 (rosserAncestor 6 state.selectedPrefix))
      state.selectedPrefix :=
  actual_frontier_admissible parent Q6 8 (by omega) N cap w z h state hstate

/-- The actual seventh history behind an eighth state is valid at the
same sixth level. Its first-exit cubic tests are obtained from the real
carrier and inherited admission, rather than supplied as a history guard. -/
theorem actual_rank_eight_seventh_admissible
    (parent : Bool → List ℕ → Bool) (Q6 : List ℕ → ℝ)
    (N cap : ℕ) (w z : ℝ) (h : ℕ → ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 8 (sixthPolicy parent Q6)
      h [] true 1 (roughPrimeUniverse N cap w z)) :
    ordinaryRosserPrefixAdmissible false (Q6 (rosserAncestor 6 state.selectedPrefix))
      (rosserAncestor 7 state.selectedPrefix) := by
  have hlen := firstExitDepthFrontier_selected_length 8 _ h []
    (roughPrimeUniverse N cap w z) true 1 (by simp) state hstate
  have hadm := actual_rank_eight_admissible parent Q6 N cap w z h state hstate
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 8
    (sixthPolicy parent Q6) h (roughPrimeUniverse N cap w z) state hstate
  have hprime : ∀ p ∈ state.selectedPrefix, p.Prime := by
    intro p hp
    exact mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp))
  have hsort : state.selectedPrefix.Pairwise (· < ·) := by
    simpa only [List.pairwise_reverse] using
      (roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub
  cases hpre : state.selectedPrefix with
  | nil => simp [hpre] at hlen
  | cons q qs =>
      have hq : q.Prime := hprime q (by simp [hpre])
      have htail := ordinaryRosserPrefixAdmissible_tail false
        (Q6 (rosserAncestor 6 state.selectedPrefix)) q qs hq
        (by simpa only [hpre] using hsort)
        (by simpa only [hpre] using hadm)
      have hanc : rosserAncestor 7 state.selectedPrefix = qs := by
        rw [rosserAncestor, hlen]
        simp [hpre]
      simpa only [hanc] using htail

/-- Genuine original mask34 action, including the true inherited current
fallback: no selected-row or gain hypothesis is needed for admission. -/
theorem slot9_actual_rank_eight_admissible
    (parent : Bool → List ℕ → Bool) (lambda6 : List ℕ → ℝ)
    (N cap : ℕ) (w z : ℝ) (h : ℕ → ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 8
      (P4ASlot9InheritedActualActionSourceOnly.nextPolicy (N : ℝ) lambda6 parent)
      h [] true 1 (roughPrimeUniverse N cap w z)) :
    ordinaryRosserPrefixAdmissible false
      (P4ASlot9InheritedActualActionSourceOnly.nextLevel (N : ℝ) lambda6
        (rosserAncestor 6 state.selectedPrefix)) state.selectedPrefix := by
  exact actual_rank_eight_admissible parent
    (P4ASlot9InheritedActualActionSourceOnly.nextLevel (N : ℝ) lambda6)
    N cap w z h state hstate

end
end ImbalancedChen.P4AActualSixthFrozenEighthAdmission
