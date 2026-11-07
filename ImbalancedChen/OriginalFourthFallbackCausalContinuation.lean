import ImbalancedChen.OriginalFullFourthPriorityOwnership
import ImbalancedChen.P1OriginalVariableFourthActiveOnly

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_FORMAL_CREDIT.

The inherited winner is a causal state, not an assertion about the sign of
a saved statistic. Once the literal original fourth maximum selects slot
zero, its entire continuation is the original coarse continuation. This is
proved by induction on the actual skip/select recursion, retaining the
ordered leaves and every field of every stopped state. Eligible negative
and tied rows remain in the bank. No first-match replacement is made.

The assertion is local to this original fourth transition. Neither the
chronological 22-successor witness nor a pass of the archived checks is
constructed here. All external row licences stay explicit.
-/

namespace ImbalancedChen.OriginalFourthFallbackCausalContinuation20261026b

noncomputable section
open scoped Classical
open HistoricalThirdCoarse P2OriginalFourthCapProducerInterface
open P1OriginalPrefixRowDecodeSoundness P1OriginalFullTableActualProducerAdapter
open P1OriginalVariableFourthContinuation
open OriginalFullFourthPriorityOwnership20261026a

variable (records : List FourthWireRow) (e chi : ℝ) (m : ℕ) (omega N : ℝ)
  (licensed : ProducerRow → Prop)

/-- This proposition uses the original maximum and literal bank positions.
It includes eligible rows which lose to, or tie, the inherited raw-Q3 seed. -/
def inheritedWinner (history : List ℕ) : Prop :=
  owner records e (seedExponent e chi m omega N history) licensed
    (primeHistoryLogCoordinates N 4 history) = 0

theorem inheritedWinner_of_nonpositive_gaps (history : List ℕ)
    (hgap : ∀ r ∈ fourthFamily records,
      producerEligible licensed r (primeHistoryLogCoordinates N 4 history) →
      r.bufferedCandidate e (primeHistoryLogCoordinates N 4 history) -
        seedExponent e chi m omega N history ≤ 0) :
    inheritedWinner records e chi m omega N licensed history := by
  apply (owner_zero_iff records e (seedExponent e chi m omega N history)
    licensed (primeHistoryLogCoordinates N 4 history)).mpr
  apply producerProfile4_eq_seed_of_dominated
  intro r hr he
  exact sub_nonpos.mp (hgap r hr he)

/-- The same numerical level survives any later selected history. This
uses the original third seed and both ancestor-freezing laws. -/
theorem sameQ_on_later_history (history : List ℕ) (hlen : history.length = 4)
    (hwin : inheritedWinner records e chi m omega N licensed history)
    (later : List ℕ) :
    producerFrozenLevel4 e chi m omega N (fourthFamily records) licensed
        (later ++ history) = frozenLevel e chi m omega N (later ++ history) := by
  rw [producerFrozenLevel4_append e chi m omega N (fourthFamily records)
    licensed later history (by omega)]
  rw [HistoricalThirdCoarse.frozenLevel_append e chi m omega N later history (by omega)]
  unfold producerFrozenLevel4 frozenLevel4
  rw [rosserAncestor_self_of_length 4 history hlen]
  exact original_history_seed_branch records e chi m omega N licensed history hlen hwin

/-- Equality is at the policy call made by the actual recursion, with its
actual incoming sign. No admissibility of that call is presumed. -/
theorem policy_on_later_history (history : List ℕ) (hlen : history.length = 4)
    (hwin : inheritedWinner records e chi m omega N licensed history)
    (later : List ℕ) (positive : Bool) :
    producerPolicy4 e chi m omega N (fourthFamily records) licensed positive
        (later ++ history) =
      HistoricalThirdCoarse.policy e chi m omega N positive (later ++ history) := by
  by_cases hshort : (later ++ history).length ≤ 4
  · exact policy4_through_four e chi m omega N (fourthFamily records)
      (producerEligible licensed) (fun r => r.bufferedCandidate e)
      positive (later ++ history) hshort
  · have hdeep : ¬ (later ++ history).length ≤ 2 := by omega
    have hQ := sameQ_on_later_history records e chi m omega N licensed history hlen hwin later
    change producerLevel4 e chi m omega N (fourthFamily records) licensed
      (rosserAncestor 4 (later ++ history)) =
        rawLevel e chi m omega N (rosserAncestor 3 (later ++ history)) at hQ
    simp only [producerPolicy4, policy4, fourthCappedUpperPolicy,
      firstExitDepthSplicePolicy, if_neg hshort, frozenParityRosserPolicy,
      ancestorFrozenPolicy]
    rw [hQ]
    simp only [HistoricalThirdCoarse.policy, thirdCappedUpperPolicy,
      firstExitDepthSplicePolicy, if_neg hdeep, frozenParityRosserPolicy,
      ancestorFrozenPolicy]

/-- Literal ordered terminal lists coincide, not merely their total mass.
The induction retains skip branches, rejected choices, signs and weights. -/
theorem leaves_on_later_history (history : List ℕ) (hlen : history.length = 4)
    (hwin : inheritedWinner records e chi m omega N licensed history)
    (weight : ℕ → ℝ) (later remaining : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitRetainedLeaves
        (producerPolicy4 e chi m omega N (fourthFamily records) licensed)
        weight (later ++ history) positive mass remaining =
      firstExitRetainedLeaves (HistoricalThirdCoarse.policy e chi m omega N)
        weight (later ++ history) positive mass remaining := by
  induction remaining generalizing later positive mass with
  | nil => rfl
  | cons p ps ih =>
      have htest := policy_on_later_history records e chi m omega N licensed
        history hlen hwin (p :: later) (!positive)
      simp only [firstExitRetainedLeaves, htest]
      rw [ih later positive mass, ih (p :: later) (!positive) (mass * weight p)]

/-- Every stopped descendant keeps exactly its selected history, remaining
carrier, sign and mass, including an exhausted or already attained rank. -/
theorem frontiers_on_later_history (history : List ℕ) (hlen : history.length = 4)
    (hwin : inheritedWinner records e chi m omega N licensed history)
    (rank : ℕ) (weight : ℕ → ℝ) (later remaining : List ℕ)
    (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier rank
        (producerPolicy4 e chi m omega N (fourthFamily records) licensed)
        weight (later ++ history) positive mass remaining =
      firstExitDepthFrontier rank (HistoricalThirdCoarse.policy e chi m omega N)
        weight (later ++ history) positive mass remaining := by
  induction remaining generalizing later positive mass with
  | nil => rfl
  | cons p ps ih =>
      by_cases hstop : rank ≤ (later ++ history).length
      · simp only [firstExitDepthFrontier, if_pos hstop]
      · have htest := policy_on_later_history records e chi m omega N licensed
          history hlen hwin (p :: later) (!positive)
        simp only [firstExitDepthFrontier, if_neg hstop, htest]
        rw [ih later positive mass, ih (p :: later) (!positive) (mass * weight p)]

/-- Signed conservation includes negative incoming masses and zero-saving
choices. No positive-part operation is used. -/
theorem signed_saving_zero (history : List ℕ) (hlen : history.length = 4)
    (hwin : inheritedWinner records e chi m omega N licensed history)
    (weight : ℕ → ℝ) (later remaining : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial
        (producerPolicy4 e chi m omega N (fourthFamily records) licensed)
        weight (later ++ history) positive mass remaining -
      firstExitRetainedPolynomial (HistoricalThirdCoarse.policy e chi m omega N)
        weight (later ++ history) positive mass remaining = 0 := by
  rw [firstExitRetainedPolynomial_eq_leaves_sum,
    firstExitRetainedPolynomial_eq_leaves_sum,
    leaves_on_later_history records e chi m omega N licensed history hlen hwin
      weight later remaining positive mass, sub_self]

end
end ImbalancedChen.OriginalFourthFallbackCausalContinuation20261026b
