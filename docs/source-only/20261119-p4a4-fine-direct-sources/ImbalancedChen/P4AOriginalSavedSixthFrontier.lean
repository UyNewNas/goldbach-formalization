import ImbalancedChen.P4AOriginalSavedSixthStage
import ImbalancedChen.P4AActualSixthFrozenEighthAdmission

/-! The actual fifth policy first changes at its own odd rank five. The
test checks the complete word at its own level. The retained sixth word
inherits that fifth ancestor while its even admission test is inactive. -/
namespace ImbalancedChen.P4AOriginalSavedSixthFrontier
noncomputable section
open scoped Classical
open P5OriginalCommonRefinedConstructor (OriginalData common3)
open P4AOriginalFull87DataPolicy (fifthPolicy level5Exponent)

def afterFour (parent : Bool → List ℕ → Bool) (Q5 : List ℕ → ℝ) :=
  firstExitDepthSplicePolicy 4 parent (frozenParityRosserPolicy false 5 Q5)

private theorem evenListLength_eq_decide_even (pre : List ℕ) :
    evenListLength pre = decide (Even pre.length) := by
  induction pre with
  | nil => simp [evenListLength]
  | cons p ps ih =>
      simp only [evenListLength, ih, List.length_cons, Nat.even_add_one, decide_not]

/-- At the first new odd test the complete inherited history is checked
at the true fifth cap. Every later selection uses the unchanged fifth ancestor and the
ordinary one-step admission theorem, including inactive even tests. -/
theorem fifth_valid
    (parent : Bool → List ℕ → Bool) (Q5 : List ℕ → ℝ)
    (k : ℕ) (h : ℕ → ℝ) (pre carrier : List ℕ)
    (positive : Bool) (mass : ℝ)
    (hpre : 5 ≤ pre.length → ordinaryRosserPrefixAdmissible false
      (Q5 (rosserAncestor 5 pre)) pre)
    (hsign : positive = evenListLength pre)
    (hprime : ∀ p ∈ carrier, p.Prime)
    (hsort : (carrier.reverse ++ pre).Pairwise (· < ·))
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k (afterFour parent Q5)
      h pre positive mass carrier) :
    (5 ≤ state.selectedPrefix.length → ordinaryRosserPrefixAdmissible false
      (Q5 (rosserAncestor 5 state.selectedPrefix)) state.selectedPrefix) ∧
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
        by_cases ht : afterFour parent Q5 (!positive) (q :: pre) = true
        · rw [firstExitDepthFrontier, if_neg hk, if_pos ht, List.mem_append] at hstate
          rcases hstate with hskip | hselect
          · exact ih pre positive mass hpre hsign hprime' hskipSort hskip
          · have hnext : 5 ≤ (q :: pre).length → ordinaryRosserPrefixAdmissible false
                (Q5 (rosserAncestor 5 (q :: pre))) (q :: pre) := by
              intro hlen
              have hdeep : ¬(q :: pre).length ≤ 4 := by omega
              have ht' : ordinaryParityRosserPolicy false
                  (Q5 (rosserAncestor 5 (q :: pre))) (!positive) (q :: pre) = true := by
                simpa only [afterFour, firstExitDepthSplicePolicy, if_neg hdeep,
                  frozenParityRosserPolicy, ancestorFrozenPolicy] using ht
              by_cases hp : 5 ≤ pre.length
              · rw [rosserAncestor_cons 5 q pre (by omega)] at ht' ⊢
                rw [ordinaryParityRosserPolicy_eq_full_on_valid_prefix false
                  (Q5 (rosserAncestor 5 pre)) pre positive q (hpre hp) hsign
                  (hprime q (by simp)) (by simp) (List.pairwise_append.mp hsort').2.1] at ht'
                exact of_decide_eq_true ht'
              · have hlen4 : pre.length = 4 := by simp only [List.length_cons] at hlen; omega
                have hs : positive = true := by
                  rw [hsign, evenListLength_eq_decide_even, hlen4]
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
    (parent : Bool → List ℕ → Bool) (Q5 : List ℕ → ℝ)
    (k : ℕ) (hk : 5 ≤ k) (N cap : ℕ) (w z : ℝ) (h : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k (afterFour parent Q5)
      h [] true 1 (roughPrimeUniverse N cap w z)) :
    ordinaryRosserPrefixAdmissible false (Q5 (rosserAncestor 5 state.selectedPrefix))
      state.selectedPrefix := by
  have hv := fifth_valid parent Q5 k h []
    (roughPrimeUniverse N cap w z) true 1 (by simp) rfl
    (fun _ hp => mem_roughPrimeUniverse_prime hp)
    (by simpa only [List.append_nil, List.pairwise_reverse]
      using roughPrimeUniverse_pairwise_gt N cap w z) state hstate
  apply hv.1
  rw [firstExitDepthFrontier_selected_length k _ h [] _ true 1 (by simp) state hstate]
  exact hk



theorem actual_fifth_at_six (n : ℕ) (d : OriginalData) (N cap : ℕ) (w z : ℝ) (weight : ℕ → ℝ)
    (s : FirstExitDepthState ℕ) (hs : s∈firstExitDepthFrontier 6 (fifthPolicy n d (N:ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z)) :
    ordinaryRosserPrefixAdmissible false
      ((N:ℝ)^level5Exponent n d (N:ℝ) (rosserAncestor 5 s.selectedPrefix)) s.selectedPrefix :=
  actual_frontier_admissible (common3 d (N:ℝ)) (fun p => (N:ℝ)^level5Exponent n d (N:ℝ) p)
    6 (by omega) N cap w z weight s hs

end
end ImbalancedChen.P4AOriginalSavedSixthFrontier
