import ImbalancedChen.OriginalFourthSuccessorTransition
import ImbalancedChen.FirstExitValidSelection

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_FORMAL_CREDIT.

Full owned-cap continuation, including genuinely raising rows. The level
used after a real original rank-four state is a constant on that state's
entire continuation, although it is not a constant over all source states.
The specialized recursion identifies its exact stopped descendants with
the ordinary parity policy at this actual owned Q. Complete admissibility
then propagates after every selection, including inactive even tests.

Incoming admissibility is derived from the ORIGINAL producer root state
and the retained raw-Q3 floor. No claimed validity of an arbitrary
replacement policy, selected-row improvement, archived raw chronology,
or distribution license is assumed. All positional owner data, even a
zero owner and tied rows, are retained without changing the original max.
-/

namespace ImbalancedChen.OriginalFourthOwnedContinuationLicense20261026b

noncomputable section
open scoped Classical
open HistoricalThirdCoarse P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open OriginalFullFourthPriorityOwnership20261026a
open OriginalFourthSuccessorTransition20261026b

variable (records : List FourthWireRow) (e chi : ℝ) (m : ℕ) (omega N : ℝ)
  (licensed : ProducerRow → Prop)

/-- This is the literal next policy call. Its Q is the attained original
maximum at the already selected fourth ancestor, not an old argmax reused
at a new source point. Only the later selected history varies. -/
theorem next_policy_at_ownedQ (history : List ℕ) (hlen : history.length = 4)
    (later : List ℕ) (p : ℕ) (positive : Bool) :
    producerPolicy4 e chi m omega N (fourthFamily records) licensed positive
        (p :: (later ++ history)) =
      ordinaryParityRosserPolicy false
        (producerLevel4 e chi m omega N (fourthFamily records) licensed history)
        positive (p :: (later ++ history)) := by
  have hdeep : ¬ (p :: (later ++ history)).length ≤ 4 := by
    simp only [List.length_cons, List.length_append]
    omega
  have ha : rosserAncestor 4 (p :: (later ++ history)) = history := by
    change rosserAncestor 4 ((p :: later) ++ history) = history
    rw [rosserAncestor_append 4 (p :: later) history (by omega),
      rosserAncestor_self_of_length 4 history hlen]
  simp only [producerPolicy4, policy4, fourthCappedUpperPolicy,
    firstExitDepthSplicePolicy, if_neg hdeep, frozenParityRosserPolicy,
    ancestorFrozenPolicy, ha]

/-- Exact continuation identity at every stopping rank, preserving all
fields of each returned state and all choices which fail the own test. -/
theorem owned_frontiers_eq_ordinary (history : List ℕ) (hlen : history.length = 4)
    (rank : ℕ) (weight : ℕ → ℝ) (later remaining : List ℕ)
    (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier rank
        (producerPolicy4 e chi m omega N (fourthFamily records) licensed)
        weight (later ++ history) positive mass remaining =
      firstExitDepthFrontier rank
        (ordinaryParityRosserPolicy false
          (producerLevel4 e chi m omega N (fourthFamily records) licensed history))
        weight (later ++ history) positive mass remaining := by
  induction remaining generalizing later positive mass with
  | nil => rfl
  | cons p ps ih =>
      by_cases hstop : rank ≤ (later ++ history).length
      · simp only [firstExitDepthFrontier, if_pos hstop]
      · have htest := next_policy_at_ownedQ records e chi m omega N licensed
          history hlen later p (!positive)
        simp only [firstExitDepthFrontier, if_neg hstop, htest]
        rw [ih later positive mass, ih (p :: later) (!positive) (mass * weight p)]

/-- The complete license comes from a real original producer state and
the exact literal continuation. It covers raising, fallback, negative-gap,
and tied-row owners together, with no owner-zero premise. -/
theorem actual_owned_descendant_license
    (Nnat cap : ℕ) (hN : 1 ≤ (Nnat : ℝ)) (z : ℝ) (weight : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 4
      (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
      weight [] true 1 (roughPrimeUniverse Nnat cap 0 z))
    (rank : ℕ) (descendant : FirstExitDepthState ℕ)
    (hdesc : descendant ∈ firstExitDepthFrontier rank
      (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
      weight state.selectedPrefix state.positive state.mass state.remaining) :
    producerFrozenLevel4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed
        descendant.selectedPrefix =
      producerLevel4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed
        state.selectedPrefix ∧
      ordinaryRosserPrefixAdmissible false
        (producerFrozenLevel4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed
          descendant.selectedPrefix) descendant.selectedPrefix ∧
      ancestorOwner records e chi m omega (Nnat : ℝ) licensed descendant.selectedPrefix =
        ancestorOwner records e chi m omega (Nnat : ℝ) licensed state.selectedPrefix ∧
      descendant.positive = evenListLength descendant.selectedPrefix := by
  have hlen := firstExitDepthFrontier_selected_length 4
    (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
    weight [] (roughPrimeUniverse Nnat cap 0 z) true 1 (by simp) state hstate
  have hincoming : ordinaryRosserPrefixAdmissible false
      (producerLevel4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed
        state.selectedPrefix) state.selectedPrefix := by
    rw [original_history_level_eq_owner records e chi m omega (Nnat : ℝ)
      licensed state.selectedPrefix hlen]
    exact actual_frontier_owned_cap_admissible records e chi m omega Nnat cap hN z
      licensed weight state hstate
  have hsign := mem_firstExitDepthFrontier_positive_eq_evenListLength 4
    (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
    weight (roughPrimeUniverse Nnat cap 0 z) state hstate
  have hsub : state.selectedPrefix.reverse ++ state.remaining <+
      roughPrimeUniverse Nnat cap 0 z := by
    simpa only [List.reverse_nil, List.nil_append] using
      firstExitDepthFrontier_selected_remaining_sublist 4
        (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
        weight [] (roughPrimeUniverse Nnat cap 0 z) true 1 state hstate
  have hprime : ∀ p ∈ state.remaining, p.Prime := by
    intro p hp
    exact mem_roughPrimeUniverse_prime
      (hsub.subset (List.mem_append.mpr (Or.inr hp)))
  have hsort : (state.remaining.reverse ++ state.selectedPrefix).Pairwise (· < ·) := by
    have hgt := (roughPrimeUniverse_pairwise_gt Nnat cap 0 z).sublist hsub
    have hrev : (state.selectedPrefix.reverse ++ state.remaining).reverse.Pairwise (· < ·) := by
      simpa only [List.pairwise_reverse] using hgt
    simpa only [List.reverse_append, List.reverse_reverse] using hrev
  have heq := owned_frontiers_eq_ordinary records e chi m omega (Nnat : ℝ) licensed
    state.selectedPrefix hlen rank weight [] state.remaining state.positive state.mass
  simp only [List.nil_append] at heq
  have hordinary := hdesc
  rw [heq] at hordinary
  have hvalid := mem_firstExitDepthFrontier_ordinaryParityRosser_valid false
    (producerLevel4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed state.selectedPrefix)
    rank weight state.selectedPrefix state.remaining state.positive state.mass
    hincoming hsign hprime (by intro hfalse; cases hfalse) hsort descendant hordinary
  have hleaf := firstExitDepthFrontier_toLeaf_mem rank
    (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
    weight state.selectedPrefix state.remaining state.positive state.mass descendant hdesc
  obtain ⟨chosen, _hchosen, _hvalid, hselected⟩ :=
    exists_validSelection_of_mem_firstExitRetainedLeaves
      (producerPolicy4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed)
      weight state.selectedPrefix state.remaining state.positive state.mass
      { selected := descendant.selectedPrefix, positive := descendant.positive,
        mass := descendant.mass } hleaf
  change descendant.selectedPrefix = chosen.reverse ++ state.selectedPrefix at hselected
  have hQ : producerFrozenLevel4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed
      descendant.selectedPrefix =
        producerLevel4 e chi m omega (Nnat : ℝ) (fourthFamily records) licensed
          state.selectedPrefix := by
    rw [hselected, producerFrozenLevel4_append e chi m omega (Nnat : ℝ)
      (fourthFamily records) licensed chosen.reverse state.selectedPrefix (by omega)]
    unfold producerFrozenLevel4 frozenLevel4
    rw [rosserAncestor_self_of_length 4 state.selectedPrefix hlen]
  refine ⟨hQ, ?_, ?_, hvalid.2⟩
  · rw [hQ]
    exact hvalid.1
  · rw [hselected]
    exact ancestorOwner_append records e chi m omega (Nnat : ℝ) licensed
      chosen.reverse state.selectedPrefix (by omega)

end
end ImbalancedChen.OriginalFourthOwnedContinuationLicense20261026b
