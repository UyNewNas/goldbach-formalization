import ImbalancedChen.Part5OriginalH430FilteredQPositionCapacityDebt

/-!
P5.6 / h34 — exact slack in the TRUE fixed-Q, rank-two, tagged
arithmetic-source capacity ledger.

The previous filtered capacity bound gave
  originalSlots <= keptFinPositions + erasedOriginalSlots.
Here its loss is computed exactly: for every physical Q, kept
positions minus their distinct observed kept slot representatives.

The slack is a Nat cardinality difference. Its nonnegativity comes
from the ACTUAL fixed-Q slot-to-Fin injection, not from an assumed
count-owner licence. In particular a filter that deletes an occupied
original slot replaces it by arithmetic erasure debt, rather than
automatically improving the paid negative-quarter estimate.

All results are manuscript-INTERNAL finite identities. Neither a
causal full/selected/inherited owner nor a quantitative upper bound
on the six q/tag rejection lanes is inferred.
SOURCE_ONLY / CANDIDATE_UNCOMPILED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430OccupiedSlotSlack

noncomputable section
open scoped Classical BigOperators

open Part5OriginalH430FixedQPositionFilterLedger
open Part5OriginalH430TruePositionReceiptLedger
open Part5OriginalH430SignedQuarterFrontierCapacity
open Part5OriginalH430OriginalUpperOverlapCount
open Part5OriginalH430NegativeQuarterActualPositionDirection
open Part5OriginalH430ActualPositionMassGap
open Part5OriginalH430FilteredQPositionCapacityDebt

/-- At each actual observed physical Q, count surviving Fin list
positions in excess of the observed source slots injected into them.
These are cardinalities of LIST OCCURRENCES, not distinct states,
not tagged q receivers, and not historical mass. -/
def actualUnusedKeptQPositionSlack
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) : ℝ :=
  ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
    (((keptPositions N cap z0 Q lower (keep Q)).card -
       (keptSlots N cap precision tau z0 lower Q (keep Q)).card :
        ℕ) : ℝ)

/-- The slack is nonnegative by construction, even if different
Q fibres contain duplicate states or U4 has two arithmetic tags. -/
theorem actual_unused_kept_q_position_slack_nonneg
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    0 ≤ actualUnusedKeptQPositionSlack
      N cap precision tau z0 lower keep := by
  unfold actualUnusedKeptQPositionSlack
  apply Finset.sum_nonneg
  intro Q hQ
  exact Nat.cast_nonneg _

/-- Exact aggregate CARDINALITY, not merely a capacity inequality:
kept history positions = observed kept slots + unoccupied slack.
The original fixed-Q slot injection pays for the Nat subtraction. -/
theorem actual_filtered_q_capacity_eq_kept_plus_unused
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    actualFilteredQPositionCapacity N cap precision tau z0 lower keep =
      actualKeptQSlotCapacity N cap precision tau z0 lower keep +
      actualUnusedKeptQPositionSlack N cap precision tau z0 lower keep := by
  unfold actualFilteredQPositionCapacity actualKeptQSlotCapacity
    actualUnusedKeptQPositionSlack
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Q hQ
  have hle :
      (keptSlots N cap precision tau z0 lower Q (keep Q)).card ≤
      (keptPositions N cap z0 Q lower (keep Q)).card :=
    kept_slots_le_kept_positions
      N cap precision tau z0 lower Q (keep Q)
  have hnat :
      (keptSlots N cap precision tau z0 lower Q (keep Q)).card +
        ((keptPositions N cap z0 Q lower (keep Q)).card -
         (keptSlots N cap precision tau z0 lower Q (keep Q)).card) =
      (keptPositions N cap z0 Q lower (keep Q)).card := by
    omega
  exact_mod_cast hnat.symm

/-- Filtered historical capacity PLUS deleted original arithmetic
slots is exactly all observed original slots PLUS the unused Fin
position slack. Erasing occupied slots cannot improve this combined
source obligation; it moves them into the erasure term. -/
theorem actual_filtered_capacity_with_erasure_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    actualFilteredQPositionCapacity N cap precision tau z0 lower keep +
      actualErasedQSlotDebt N cap precision tau z0 lower keep =
    actualObservedQSlotCapacity N cap precision tau z0 lower +
      actualUnusedKeptQPositionSlack N cap precision tau z0 lower keep := by
  have hslots := actual_observed_q_slots_eq_kept_plus_erased
    N cap precision tau z0 lower keep
  have hpositions := actual_filtered_q_capacity_eq_kept_plus_unused
    N cap precision tau z0 lower keep
  linarith only [hslots, hpositions]

/-- The original, doubly tagged U3/U4 source has an EXACT
arithmetic-source identity after filtering. The six original q/tag
collision and rejection lanes are not merged with the slack. -/
theorem original_tagged_source_plus_unused_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    (currentChenUpsilon3 N + currentChenUpsilon4 N) +
      actualUnusedKeptQPositionSlack N cap precision tau z0 lower keep =
    (actualFilteredQPositionCapacity N cap precision tau z0 lower keep +
      actualErasedQSlotDebt N cap precision tau z0 lower keep) +
      originalSixUnpaidReceiptLanes N cap precision tau z0 lower
        (fun _ => (1 : ℝ)) := by
  have hsource := original_unit_source_eq_filtered_slots_erased_and_six
    N cap precision tau z0 lower hzcap keep
  have hbudget := actual_filtered_capacity_with_erasure_exact
    N cap precision tau z0 lower keep
  linarith only [hsource, hbudget]

/-- Exact original Chen -1/4 contribution: the unused Fin slack
returns as POSITIVE correction. This is not a proof of a final
constant, or a licence to discard the erased q/tag source. -/
theorem original_signed_quarter_with_unused_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    originalU34SignedQuarter N =
      -(1 / 4 : ℝ) *
        ((actualFilteredQPositionCapacity N cap precision tau z0 lower keep +
          actualErasedQSlotDebt N cap precision tau z0 lower keep) +
          originalSixUnpaidReceiptLanes N cap precision tau z0 lower
            (fun _ => (1 : ℝ))) +
        (1 / 4 : ℝ) *
          actualUnusedKeptQPositionSlack N cap precision tau z0 lower keep := by
  have hsource := original_tagged_source_plus_unused_exact
    N cap precision tau z0 lower hzcap keep
  rw [originalU34SignedQuarter]
  linarith only [hsource]

/-- The earlier filtered upper envelope is exact precisely when
no unused history-list capacity survives the chosen Q-dependent
filter. This is a condition on actual Fin occurrences, not an
assumed selected-count-owner hypothesis. -/
theorem actual_filtered_bound_tight_iff_no_unused
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    actualFilteredQPositionCapacity N cap precision tau z0 lower keep +
      actualErasedQSlotDebt N cap precision tau z0 lower keep =
        actualObservedQSlotCapacity N cap precision tau z0 lower ↔
    actualUnusedKeptQPositionSlack N cap precision tau z0 lower keep = 0 := by
  have h := actual_filtered_capacity_with_erasure_exact
    N cap precision tau z0 lower keep
  constructor
  · intro ht
    linarith only [h, ht]
  · intro hz
    linarith only [h, hz]

/-- At the TRUE ordinary full-prefix gate of this same frontier,
there is zero erased source, so the slack is exactly the old full
frontier capacity minus the distinct observed physical slots.
No selected/inherited manuscript gate is claimed here. -/
theorem actual_full_prefix_frontier_eq_slots_plus_unused
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    actualQFrontierPositionCapacity N cap precision tau z0 lower =
      actualObservedQSlotCapacity N cap precision tau z0 lower +
      actualUnusedKeptQPositionSlack N cap precision tau z0 lower
        (fun Q => actualFullPrefixGate lower Q) := by
  have h := actual_filtered_capacity_with_erasure_exact
    N cap precision tau z0 lower
      (fun Q => actualFullPrefixGate lower Q)
  rw [actual_ordinary_full_prefix_kept_capacity_eq_frontier,
    actual_ordinary_full_prefix_erased_debt_zero] at h
  linarith only [h]

end
end ImbalancedChen.Part5OriginalH430OccupiedSlotSlack
