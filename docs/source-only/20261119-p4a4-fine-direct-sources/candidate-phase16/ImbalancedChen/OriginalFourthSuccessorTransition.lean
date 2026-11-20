import ImbalancedChen.OriginalFullFourthPriorityOwnership
import ImbalancedChen.P1OriginalVariableFourthActiveOnly

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The first adopted upper-ledger successor is the complete stronger-fourth
replacement, not another copy of the old partial-four or tail gain.
The manuscript says it retains rank four and changes only later odd tests.
This file supplies the previously missing literal policy connection to the
ordered full-row owner: real prime-history ancestors, the full ordinary
Rosser predicate, exact buffered tent, and the original rawQ3 fallback.

The Python source was READ, never executed. Its winner field is a subset
mask, not a chronological parent or a priority witness. Least maximizing
position is the already proved accounting convention; no claim is made
that it recovers an absent historical tie map. Non-improving candidates,
including negative differences and equality, inherit the entire policy.

This is one transition specification, not a 22-successor history license.
Row distribution/buffer licenses remain explicit primitive inputs. No
archived parse pass, whole-row geometry pass, saving or final bound occurs.
-/

namespace ImbalancedChen.OriginalFourthSuccessorTransition20261026b

noncomputable section
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open OriginalFullFourthPriorityOwnership20261026a
open VariableEnvelope

/-- The owner is read from the actual frozen fourth ancestor, not the
current longer tuple and not an independently selected third parent. -/
def ancestorOwner (records : List FourthWireRow) (e chi : ℝ) (m : ℕ)
    (omega N : ℝ) (licensed : ProducerRow → Prop) (history : List ℕ) :
    BankPosition records :=
  owner records e (seedExponent e chi m omega N (rosserAncestor 4 history)) licensed
    (primeHistoryLogCoordinates N 4 (rosserAncestor 4 history))

theorem ancestorOwner_append (records : List FourthWireRow) (e chi : ℝ) (m : ℕ)
    (omega N : ℝ) (licensed : ProducerRow → Prop) (later history : List ℕ)
    (hlen : 4 ≤ history.length) :
    ancestorOwner records e chi m omega N licensed (later ++ history) =
      ancestorOwner records e chi m omega N licensed history := by
  unfold ancestorOwner
  rw [rosserAncestor_append 4 later history hlen]

/-- Every descendant uses exactly the cap attained at its fourth owner.
The full rawQ3 seed, hence e/chi/m/omega, remains inside this formula. -/
theorem frozenLevel_eq_owner (records : List FourthWireRow) (e chi : ℝ) (m : ℕ)
    (omega N : ℝ) (licensed : ProducerRow → Prop) (history : List ℕ)
    (hlen : 4 ≤ history.length) :
    producerFrozenLevel4 e chi m omega N (fourthFamily records) licensed history =
      N ^ slotValue records e (seedExponent e chi m omega N (rosserAncestor 4 history))
        (primeHistoryLogCoordinates N 4 (rosserAncestor 4 history))
        (ancestorOwner records e chi m omega N licensed history) := by
  have ha : (rosserAncestor 4 history).length = 4 := by
    rw [rosserAncestor_length]
    omega
  exact original_history_level_eq_owner records e chi m omega N licensed
    (rosserAncestor 4 history) ha

/-- Literal later test: positive/even signs always continue; negative/odd
signs check the provider's COMPLETE upper admissibility predicate at the
owned cap. In particular a product cutoff and all old cubic tests remain. -/
theorem policy_after_four (records : List FourthWireRow) (e chi : ℝ) (m : ℕ)
    (omega N : ℝ) (licensed : ProducerRow → Prop) (positive : Bool)
    (history : List ℕ) (hlen : 4 < history.length) :
    producerPolicy4 e chi m omega N (fourthFamily records) licensed positive history =
      (positive || decide (ordinaryRosserPrefixAdmissible false
        (N ^ slotValue records e (seedExponent e chi m omega N (rosserAncestor 4 history))
          (primeHistoryLogCoordinates N 4 (rosserAncestor 4 history))
          (ancestorOwner records e chi m omega N licensed history)) history)) := by
  have hc := frozenLevel_eq_owner records e chi m omega N licensed history hlen.le
  change producerLevel4 e chi m omega N (fourthFamily records) licensed
    (rosserAncestor 4 history) = _ at hc
  simp only [producerPolicy4, policy4, fourthCappedUpperPolicy, firstExitDepthSplicePolicy,
    if_neg (not_le.mpr hlen), frozenParityRosserPolicy, ancestorFrozenPolicy,
    ordinaryParityRosserPolicy, Bool.false_eq_true, if_false, oddFirstExitPolicy]
  rw [hc]

/-- Rank four itself and every earlier decision retain the actual parent.
No fourth cube test or even exclusion is introduced by the replacement. -/
theorem policy_through_four (records : List FourthWireRow) (e chi : ℝ) (m : ℕ)
    (omega N : ℝ) (licensed : ProducerRow → Prop) (positive : Bool)
    (history : List ℕ) (hlen : history.length ≤ 4) :
    producerPolicy4 e chi m omega N (fourthFamily records) licensed positive history =
      HistoricalThirdCoarse.policy e chi m omega N positive history :=
  policy4_through_four e chi m omega N (fourthFamily records)
    (producerEligible licensed) (fun r => r.bufferedCandidate e) positive history hlen

theorem policy_even (records : List FourthWireRow) (e chi : ℝ) (m : ℕ)
    (omega N : ℝ) (licensed : ProducerRow → Prop) (history : List ℕ) :
    producerPolicy4 e chi m omega N (fourthFamily records) licensed true history = true := by
  by_cases hlen : history.length ≤ 4
  · rw [policy_through_four records e chi m omega N licensed true history hlen]
    exact HistoricalThirdCoarse.policy_even e chi m omega N history
  · rw [policy_after_four records e chi m omega N licensed true history (by omega)]
    rfl

/-- Exact fallback criterion, with NO positivity hypothesis on a candidate
or on its difference from rawQ3. Equality goes to the inherited seed. -/
theorem owner_zero_iff_all_nonimproving (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (t : Point) :
    owner records e seed licensed t = 0 ↔
      ∀ r ∈ fourthFamily records, producerEligible licensed r t →
        r.bufferedCandidate e t ≤ seed := by
  rw [owner_zero_iff]
  constructor
  · intro h r hr he
    rw [← h]
    exact finiteMax_row_le (fourthFamily records) _ _ seed r hr he
  · exact producerProfile4_eq_seed_of_dominated e (fourthFamily records) licensed seed t

/-- Losing and tied rows preserve the WHOLE original continuation, even
when boxes contain the point. This is stronger than outside-box fallback. -/
theorem policy_of_nonimproving (records : List FourthWireRow) (e chi : ℝ) (m : ℕ)
    (omega N : ℝ) (licensed : ProducerRow → Prop) (positive : Bool) (history : List ℕ)
    (hrows : ∀ r ∈ fourthFamily records,
      producerEligible licensed r (primeHistoryLogCoordinates N 4 (rosserAncestor 4 history)) →
        r.bufferedCandidate e (primeHistoryLogCoordinates N 4 (rosserAncestor 4 history)) ≤
          seedExponent e chi m omega N (rosserAncestor 4 history)) :
    producerPolicy4 e chi m omega N (fourthFamily records) licensed positive history =
      HistoricalThirdCoarse.policy e chi m omega N positive history := by
  by_cases hlen : history.length ≤ 4
  · exact policy_through_four records e chi m omega N licensed positive history hlen
  · have ha : (rosserAncestor 4 history).length = 4 := by
      rw [rosserAncestor_length]
      omega
    have ho := (owner_zero_iff_all_nonimproving records e
      (seedExponent e chi m omega N (rosserAncestor 4 history)) licensed
      (primeHistoryLogCoordinates N 4 (rosserAncestor 4 history))).mpr hrows
    have hc := original_history_seed_branch records e chi m omega N licensed
      (rosserAncestor 4 history) ha ho
    unfold HistoricalThirdCoarse.frozenLevel at hc
    rw [rosserAncestor_nested 3 4 (by omega)] at hc
    simp only [producerPolicy4, policy4, fourthCappedUpperPolicy, firstExitDepthSplicePolicy,
      if_neg hlen, frozenParityRosserPolicy, ancestorFrozenPolicy]
    rw [hc]
    simp only [HistoricalThirdCoarse.policy, thirdCappedUpperPolicy, firstExitDepthSplicePolicy,
      if_neg (show ¬history.length ≤ 2 by omega), frozenParityRosserPolicy, ancestorFrozenPolicy]

/-- Both original Theta branches (inactive at the literal rough cutoff,
or active outside adopted half-open cells) keep their original policy.
No mesh lower endpoint is substituted for the actual third prime. -/
theorem policy_original_cutoff_fallback (records : List FourthWireRow) (e chi : ℝ) (m : ℕ)
    (omega N : ℝ) (licensed : ProducerRow → Prop) (positive : Bool) (history : List ℕ)
    (hs : ¬ P1ThirdFallbackSupport.supported e chi m omega N (rosserAncestor 3 history)) :
    producerPolicy4 e chi m omega N (fourthFamily records) licensed positive history =
      HistoricalThirdCoarse.policy e chi m omega N positive history := by
  apply policy_of_nonimproving records e chi m omega N licensed positive history
  intro r _hr _he
  have hseed : seedExponent e chi m omega N (rosserAncestor 4 history) =
      HistoricalThirdCoarse.initial e := by
    rw [seedExponent_ancestor_four]
    exact if_neg hs
  rw [hseed]
  exact (P1OriginalVariableFourthActiveOnly.bufferedCandidate_lt_initial e r _).le

/-- A nonzero owner is a genuine strict raise over rawQ3. Seed-first ties
make this strict even though later row ties use weak comparisons. -/
theorem row_owner_strict_raise (records : List FourthWireRow) (e seed : ℝ)
    (licensed : ProducerRow → Prop) (t : Point) (i : Fin records.length)
    (ho : owner records e seed licensed t = i.succ) :
    seed < v (∑ k ∈ (rowAt records i).selected, t k) - 2 * e := by
  have hg := (owner_eq_iff_orderedGates records e seed licensed t i.succ).mp ho
  have hlt := hg.2.2 0 (by simp) True.intro
  simpa only [slotValue, Fin.cases_zero, Fin.cases_succ,
    ProducerRow.bufferedCandidate_eq] using hlt

/-- Admissibility is obtained from membership in the ACTUAL inherited
rank-four frontier and the retained rawQ3 floor. It is never assumed as
a final certificate premise. The claim is valid also on the fallback. -/
theorem actual_frontier_owned_cap_admissible (records : List FourthWireRow)
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (z : ℝ)
    (licensed : ProducerRow → Prop) (weight : ℕ → ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 4
      (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
      weight [] true 1 (roughPrimeUniverse N cap 0 z)) :
    ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ slotValue records e
        (seedExponent e chi m omega (N : ℝ) state.selectedPrefix)
        (primeHistoryLogCoordinates (N : ℝ) 4 state.selectedPrefix)
        (owner records e (seedExponent e chi m omega (N : ℝ) state.selectedPrefix) licensed
          (primeHistoryLogCoordinates (N : ℝ) 4 state.selectedPrefix))) state.selectedPrefix := by
  have hf := fourthCappedUpperPolicy_frontier_four (HistoricalThirdCoarse.initialPolicy e m (N : ℝ))
    (HistoricalThirdCoarse.rawLevel e chi m omega (N : ℝ))
    (producerLevel4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
    weight [] (roughPrimeUniverse N cap 0 z) true 1
  change firstExitDepthFrontier 4
      (producerPolicy4 e chi m omega (N : ℝ) (fourthFamily records) licensed)
      weight [] true 1 (roughPrimeUniverse N cap 0 z) =
    firstExitDepthFrontier 4 (HistoricalThirdCoarse.policy e chi m omega (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap 0 z) at hf
  rw [hf] at hstate
  have hv := actualThirdCapped_rankFour_admissible (HistoricalThirdCoarse.initialPolicy e m (N : ℝ))
    (HistoricalThirdCoarse.rawLevel e chi m omega (N : ℝ)) N cap z weight state hstate
  have hlen := firstExitDepthFrontier_selected_length 4
    (HistoricalThirdCoarse.policy e chi m omega (N : ℝ)) weight []
    (roughPrimeUniverse N cap 0 z) true 1 (by simp) state hstate
  have hm := producer_frozenThird_le_level4 e chi m omega (N : ℝ) hN
    (fourthFamily records) licensed state.selectedPrefix
  have hadm := ordinaryRosserPrefixAdmissible_mono false state.selectedPrefix hm hv
  rw [original_history_level_eq_owner records e chi m omega (N : ℝ) licensed
    state.selectedPrefix (by simpa using hlen)] at hadm
  exact hadm

end
end ImbalancedChen.OriginalFourthSuccessorTransition20261026b
