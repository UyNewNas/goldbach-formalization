import ImbalancedChen.Part3ActualCompactAllRankSupport
import ImbalancedChen.ActualUpperCountingInputs
import ImbalancedChen.FirstExitValidSelection

/-!
# Nonzero actual attached coefficients have original rough frontiers

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

A valid selection is realized at its own rank in the actual stopped
frontier.  The existing literal small/rough factorization of a nonzero
physical coefficient supplies that valid selection on the same rough
carrier.  No replacement modulus, enumeration cap, or coefficient is used.

The actual attached-coefficient theorem retains its small factor and its
strict small level, the nonzero rough coefficient, the original frontier,
and the complete product identity.  On each active compact rank >= 3
branch its full rough D-well support is then a conclusion.  This is not
yet full support of the small-attached product or a signed tensor estimate.
-/

namespace ImbalancedChen.Part3.ActualAttachedRoughFrontier

noncomputable section

open scoped List
open ActualCompactAllRankSupport

/-- Realize a valid chosen sublist at its own selected rank.  The
unprocessed carrier is whatever the original recursion leaves there. -/
theorem valid_selection_frontier_witness {α : Type*}
    (retained : Bool → List α → Bool) (weight : α → ℝ)
    {chosen remaining : List α} (hsub : chosen <+ remaining)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (hvalid : FirstExitValidSelection retained pre positive chosen) :
    ∃ state ∈ firstExitDepthFrontier (pre.length + chosen.length)
      retained weight pre positive mass remaining,
      state.selectedPrefix = chosen.reverse ++ pre := by
  induction hsub generalizing pre positive mass with
  | slnil =>
      refine ⟨⟨pre, positive, mass, []⟩, ?_, by simp⟩
      simp [firstExitDepthFrontier]
  | @cons chosen remaining p hsub ih =>
      by_cases hempty : chosen = []
      · subst chosen
        refine ⟨⟨pre, positive, mass, p :: remaining⟩, ?_, by simp⟩
        simp [firstExitDepthFrontier]
      · have hpos : 0 < chosen.length := List.length_pos_iff.mpr hempty
        have hdeep : ¬pre.length + chosen.length ≤ pre.length := by omega
        obtain ⟨state, hstate, heq⟩ := ih pre positive mass hvalid
        refine ⟨state, ?_, heq⟩
        rw [firstExitDepthFrontier, if_neg hdeep]
        exact List.mem_append_left _ hstate
  | @cons_cons chosen remaining p hsub ih =>
      have hdeep : ¬pre.length + (p :: chosen).length ≤ pre.length := by
        simp only [List.length_cons]
        omega
      obtain ⟨hpass, htail⟩ := hvalid
      obtain ⟨state, hstate, heq⟩ := ih (p :: pre) (!positive) (mass * weight p) htail
      have hrank : (p :: pre).length + chosen.length =
          pre.length + (p :: chosen).length := by simp only [List.length_cons]; omega
      rw [hrank] at hstate
      refine ⟨state, ?_, ?_⟩
      · rw [firstExitDepthFrontier, if_neg hdeep, if_pos hpass]
        exact List.mem_append_right _ hstate
      · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using heq

/-- A literal nonzero compact physical coefficient supplies its own small
factor and original rough frontier.  Active high-rank square support is
derived from that frontier, with the same physical cell and cap. -/
theorem actual_compact_rho_ne_zero_frontier
    (e h : ℝ) (m N cap : ℕ) (w z L : ℝ) {q : ℕ}
    (hq : actualSmallRoughRho (actualExtendedThirdCompactUpperPolicy e h m N false)
      N cap w z L q ≠ 0) :
    ∃ a k (state : FirstExitDepthState ℕ),
      a ∈ actualSmallRosserSupport N cap w ∧ (a : ℝ) < L ∧
      state.selectedPrefix.length = k ∧
      state ∈ firstExitDepthFrontier k (actualExtendedThirdCompactUpperPolicy e h m N)
        (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z) ∧
      q = a * state.selectedPrefix.prod ∧
      fixedRoughCoefficient (actualExtendedThirdCompactUpperPolicy e h m N false)
        N cap w z state.selectedPrefix.prod ≠ 0 ∧
      ∀ j : ActualExtendedThirdDyadicLabel m, j ∈ actualExtendedThirdCompactCells e h m →
        3 ≤ k →
        primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 state.selectedPrefix) ∈
          actualExtendedThirdOwnedCell m j →
        actualDwellSupport ((N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j)
          state.selectedPrefix.reverse := by
  obtain ⟨a, ha, b, hb, hprod, haL, hbne⟩ := actualSmallRoughRho_ne_zero_factors
    (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z L hq
  have hbret : b ∈ firstExitRetainedModuli (actualExtendedThirdCompactUpperPolicy e h m N)
      (roughPrimeUniverse N cap w z) := by
    rw [← UpperPolicyFiniteBridge.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
      (actualExtendedThirdCompactUpperPolicy e h m N)
      (actualExtendedThirdCompactUpperPolicy_even e h m N) N cap w z]
    exact hb
  obtain ⟨chosen, hsub, hvalid, hchosen⟩ :=
    (mem_firstExitRetainedModuli_iff_validSelection
      (actualExtendedThirdCompactUpperPolicy e h m N) (roughPrimeUniverse N cap w z) b).mp hbret
  obtain ⟨state, hstate, hselected⟩ := valid_selection_frontier_witness
    (actualExtendedThirdCompactUpperPolicy e h m N) (fun _ => 1) hsub [] true 1 hvalid
  have hstate' : state ∈ firstExitDepthFrontier chosen.length
      (actualExtendedThirdCompactUpperPolicy e h m N) (fun _ => 1) [] true 1
      (roughPrimeUniverse N cap w z) := by simpa only [List.length_nil, zero_add] using hstate
  have hlen : state.selectedPrefix.length = chosen.length := by simp [hselected]
  have hstateprod : state.selectedPrefix.prod = b := by
    simpa only [hselected, List.append_nil, List.prod_reverse] using hchosen
  refine ⟨a, chosen.length, state, ha, haL, hlen, hstate', ?_, ?_, ?_⟩
  · simpa only [hstateprod] using hprod
  · simpa only [hstateprod] using hbne
  · intro j hj hk ht
    exact actual_compact_frontier_all_rank_support e h m N cap chosen.length hk w z
      (fun _ => 1) state hstate' hj ht

/-- The actual counting interface's nu=1 coefficient, with its literal
epsilon-squared small cutoff, original rough ceiling, and unchanged cap.  No
support or frontier witness is supplied by the caller. -/
theorem actual_attached_upper_ne_zero_frontier
    (e h epsilon : ℝ) (m N : ℕ) (cap : ℕ → ℕ) {q : ℕ}
    (hq : attachedUpperCoefficient 1 thirdPrefixRho epsilon
      (fun M => actualExtendedThirdCompactUpperPolicy e h m M false) cap N q ≠ 0) :
    ∃ a k (state : FirstExitDepthState ℕ),
      a ∈ actualSmallRosserSupport N (cap N) ((N : ℝ) ^ (epsilon ^ 2)) ∧
      (a : ℝ) < (N : ℝ) ^ epsilon ∧ state.selectedPrefix.length = k ∧
      state ∈ firstExitDepthFrontier k (actualExtendedThirdCompactUpperPolicy e h m N)
        (fun _ => 1) [] true 1
        (roughPrimeUniverse N (cap N) ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho)) ∧
      q = a * state.selectedPrefix.prod ∧
      fixedRoughCoefficient (actualExtendedThirdCompactUpperPolicy e h m N false)
        N (cap N) ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho)
        state.selectedPrefix.prod ≠ 0 ∧
      ∀ j : ActualExtendedThirdDyadicLabel m, j ∈ actualExtendedThirdCompactCells e h m →
        3 ≤ k →
        primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 state.selectedPrefix) ∈
          actualExtendedThirdOwnedCell m j →
        actualDwellSupport ((N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j)
          state.selectedPrefix.reverse := by
  apply actual_compact_rho_ne_zero_frontier e h m N (cap N)
    ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho) ((N : ℝ) ^ epsilon)
  simpa only [attachedUpperCoefficient, one_mul] using hq

end

end ImbalancedChen.Part3.ActualAttachedRoughFrontier
