import ImbalancedChen.OriginalFourthFallbackCausalContinuation
import ImbalancedChen.FirstExitValidSelection

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_FORMAL_CREDIT.

The fallback continuation theorem is now attached to literal ORIGINAL
producer frontier states on the target-deleted rough prime carrier. All
incoming complete admissibility, sign, order and primality facts are
derived from that state. The continuation induction then gives complete
admissibility after every attained later selection, including even tests,
at the very same original frozen Q. An old admissibility premise is not
silently assumed for a replacement policy.

The second part handles both genuine rough-cutoff inactivity and the
active-but-unselected coarse branch. The original Theta seed defeats
every candidate, so input row order and ties cannot replace it. This is a
compositional branch theorem, not a recovered 22-stage archive witness.
-/

namespace ImbalancedChen.OriginalFourthFallbackActualStateLicense20261026b

noncomputable section
open scoped Classical
open HistoricalThirdCoarse P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open OriginalFullFourthPriorityOwnership20261026a
open OriginalFourthFallbackCausalContinuation20261026b

variable (records : List FourthWireRow) (e chi : ℝ) (m : ℕ) (omega : ℝ)
  (licensed : ProducerRow → Prop)

/-- The premise is membership of a real producer state. Complete incoming
validity and all later validity are obtained from the recursion itself. -/
theorem actual_descendant_sameQ_admissible
    (N cap : ℕ) (z : ℝ) (weight : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 4
      (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
      weight [] true 1 (roughPrimeUniverse N cap 0 z))
    (hwin : inheritedWinner records e chi m omega (N : ℝ) licensed state.selectedPrefix)
    (rank : ℕ) (hrank : 4 ≤ rank) (descendant : FirstExitDepthState ℕ)
    (hdesc : descendant ∈ firstExitDepthFrontier rank
      (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
      weight state.selectedPrefix state.positive state.mass state.remaining) :
    producerFrozenLevel4 e chi m omega (N : ℝ) (fourthFamily records) licensed
        descendant.selectedPrefix = frozenLevel e chi m omega (N : ℝ) descendant.selectedPrefix ∧
      ordinaryRosserPrefixAdmissible false
        (producerFrozenLevel4 e chi m omega (N : ℝ) (fourthFamily records) licensed
          descendant.selectedPrefix) descendant.selectedPrefix ∧
      descendant.positive = evenListLength descendant.selectedPrefix := by
  have hcoarse := hstate
  change state ∈ firstExitDepthFrontier 4
    (fourthCappedUpperPolicy (initialPolicy e m (N : ℝ))
      (rawLevel e chi m omega (N : ℝ))
      (producerLevel4 e chi m omega (N : ℝ) (fourthFamily records) licensed))
    weight [] true 1 (roughPrimeUniverse N cap 0 z) at hcoarse
  rw [fourthCappedUpperPolicy_frontier_four] at hcoarse
  have hlen : state.selectedPrefix.length = 4 :=
    firstExitDepthFrontier_selected_length 4 _ weight []
      (roughPrimeUniverse N cap 0 z) true 1 (by simp) state hcoarse
  have hincoming := actualThirdCapped_rankFour_admissible
    (initialPolicy e m (N : ℝ)) (rawLevel e chi m omega (N : ℝ))
    N cap z weight state hcoarse
  have hsign := mem_firstExitDepthFrontier_positive_eq_evenListLength
    4 (HistoricalThirdCoarse.policy e chi m omega (N : ℝ)) weight
    (roughPrimeUniverse N cap 0 z) state hcoarse
  have hsub : state.selectedPrefix.reverse ++ state.remaining <+
      roughPrimeUniverse N cap 0 z := by
    simpa only [List.reverse_nil, List.nil_append] using
      firstExitDepthFrontier_selected_remaining_sublist 4
        (HistoricalThirdCoarse.policy e chi m omega (N : ℝ)) weight []
        (roughPrimeUniverse N cap 0 z) true 1 state hcoarse
  have hprime : ∀ p ∈ state.remaining, p.Prime := by
    intro p hp
    exact mem_roughPrimeUniverse_prime
      (hsub.subset (List.mem_append.mpr (Or.inr hp)))
  have hsort : (state.remaining.reverse ++ state.selectedPrefix).Pairwise (· < ·) := by
    have hgt := (roughPrimeUniverse_pairwise_gt N cap 0 z).sublist hsub
    have hrev : (state.selectedPrefix.reverse ++ state.remaining).reverse.Pairwise (· < ·) := by
      simpa only [List.pairwise_reverse] using hgt
    simpa only [List.reverse_append, List.reverse_reverse] using hrev
  have heq := frontiers_on_later_history records e chi m omega (N : ℝ) licensed
    state.selectedPrefix hlen hwin rank weight [] state.remaining state.positive state.mass
  simp only [List.nil_append] at heq
  have hdescCoarse := hdesc
  rw [heq] at hdescCoarse
  have hvalid := mem_firstExitDepthFrontier_thirdCapped_valid
    (initialPolicy e m (N : ℝ)) (rawLevel e chi m omega (N : ℝ)) rank weight
    state.selectedPrefix state.remaining state.positive state.mass
    (fun _ => hincoming) hsign hprime hsort descendant hdescCoarse
  have hdescLen := firstExitDepthFrontier_selected_length rank
    (HistoricalThirdCoarse.policy e chi m omega (N : ℝ)) weight
    state.selectedPrefix state.remaining state.positive state.mass
    (by omega) descendant hdescCoarse
  have hadmissible := hvalid.1 (by omega : 3 ≤ descendant.selectedPrefix.length)
  have hleaf := firstExitDepthFrontier_toLeaf_mem rank
    (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
    weight state.selectedPrefix state.remaining state.positive state.mass descendant hdesc
  obtain ⟨chosen, _hchosen, _hchosenValid, hselected⟩ :=
    exists_validSelection_of_mem_firstExitRetainedLeaves
      (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
      weight state.selectedPrefix state.remaining state.positive state.mass
      { selected := descendant.selectedPrefix, positive := descendant.positive,
        mass := descendant.mass } hleaf
  have hQ : producerFrozenLevel4 e chi m omega (N : ℝ) (fourthFamily records) licensed
      descendant.selectedPrefix = frozenLevel e chi m omega (N : ℝ) descendant.selectedPrefix := by
    change descendant.selectedPrefix = chosen.reverse ++ state.selectedPrefix at hselected
    rw [hselected]
    exact sameQ_on_later_history records e chi m omega (N : ℝ) licensed
      state.selectedPrefix hlen hwin chosen.reverse
  refine ⟨hQ, ?_, hvalid.2⟩
  rw [hQ]
  exact hadmissible

/-- Unsupported means the literal strict-cutoff branch OR an active
ancestor outside the adopted half-open coarse union. Equality at the rough
cutoff remains active, exactly as in the original source. -/
theorem unsupported_inheritedWinner (N : ℝ) (history : List ℕ)
    (hs : ¬ P1ThirdFallbackSupport.frozenSupported e chi m omega N history) :
    inheritedWinner records e chi m omega N licensed history := by
  have hseed : seedExponent e chi m omega N history = initial e := by
    unfold seedExponent P1CoarseFirstCubeFallbackMargin.effectiveExponent
    exact if_neg hs
  apply (owner_zero_iff records e (seedExponent e chi m omega N history)
    licensed (primeHistoryLogCoordinates N 4 history)).mpr
  rw [hseed]
  exact P1OriginalVariableFourthActiveOnly.producerProfile_initial e
    (fourthFamily records) licensed _

/-- Cutoff and geometric fallback give both the exact original initial Q
and the exact first-stop initial policy throughout the inherited history. -/
theorem unsupported_sameQ_and_policy (N : ℝ) (history : List ℕ)
    (hlen : history.length = 4)
    (hs : ¬ P1ThirdFallbackSupport.frozenSupported e chi m omega N history)
    (later : List ℕ) (positive : Bool) :
    producerFrozenLevel4 e chi m omega N (fourthFamily records) licensed
        (later ++ history) = N ^ initial e ∧
      producerPolicy4 e chi m omega N (fourthFamily records) licensed
          positive (later ++ history) = initialPolicy e m N positive (later ++ history) := by
  have hwin := unsupported_inheritedWinner records e chi m omega licensed N history hs
  have hsLater : ¬ P1ThirdFallbackSupport.frozenSupported e chi m omega N
      (later ++ history) := by
    unfold P1ThirdFallbackSupport.frozenSupported
    rw [rosserAncestor_append 3 later history (by omega)]
    exact hs
  constructor
  · rw [sameQ_on_later_history records e chi m omega N licensed history hlen hwin later]
    exact P1ThirdFallbackSupport.frozenLevel_fallback e chi m omega N _ hsLater
  · rw [policy_on_later_history records e chi m omega N licensed history hlen hwin later positive]
    exact P1ThirdFallbackSupport.policy_fallback e chi m omega N positive _ hsLater

end
end ImbalancedChen.OriginalFourthFallbackActualStateLicense20261026b
