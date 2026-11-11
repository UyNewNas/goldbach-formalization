import ImbalancedChen.Part5OriginalH430NegativeQuarterActualPositionDirection

/-!
P5.6 / h34 — a LOWER-bound direction for the ORIGINAL negative Chen
quarter, paid against ACTUAL rank-two LIST OCCURRENCE CAPACITY at
each separate physical Q, plus ALL six explicit original q/tag lanes.

The previous quarter packet produced an upper bound on the signed
subtraction, the wrong direction for the Chen lower sieve. Here we
instead start from the real unit-weight original tagged arithmetic
source, not the observed historical rank-two mass. An observed
physical (Q,p,ell) slot uses at most one Fin position in its OWN
physical-Q rank-two list. Each such slot contributes exactly ONE
original tagged representative, and the complete original q surplus,
cross-tag collisions, non-retention, cutoff, and policy rejection
receipts remain on the six original lanes.

We obtain a genuine lower bound for -(Upsilon3+Upsilon4)/4 in terms
of the total ACTUAL per-Q rank-two list lengths and the literal six
unpaid UNIT receipt lanes. The U4-overlap tags remain two receipts.
This is a finite positional capacity bound, NOT a small-error bound:
the list lengths are uncontrolled by the root 7/2 or 430+11 budget,
and the six lanes remain unpaid. This does not manufacture a
full/selected/inherited owner or signed Euler first-exit payment.

SOURCE_ONLY / CANDIDATE_UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430SignedQuarterFrontierCapacity

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430PhysicalSlotListPositions
open Part5OriginalH430FixedQSlotInjection
open Part5OriginalH430FixedQPositionFilterLedger
open Part5OriginalH430TruePositionReceiptLedger
open Part5OriginalH430ActualPositionMassGap
open Part5OriginalH430QDependentPositionErasure
open Part5OriginalH430OriginalUpperOverlapCount
open Part5OriginalH430NegativeQuarterActualPositionDirection

/-- Exact number of ACTUAL observed physical slots, counted once for
each separate physical Q. This is NOT the original q/tag count. -/
def actualObservedQSlotCapacity
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) : ℝ :=
  ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
    ((observedPhysicalSlotsAtQ N cap precision tau z0 lower Q).card : ℝ)

/-- Total lengths of the ORIGINAL recursive rank-two LISTS at the
physical Q values actually represented by tagged q receipts.
Duplicates at distinct Fin indices are not silently quotiented. -/
def actualQFrontierPositionCapacity
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) : ℝ :=
  ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
    ((actualPhysicalRankTwoList N cap z0 Q lower).length : ℝ)

/-- A UNIT original representative contributes exactly one per
observed physical slot at its genuine fixed-Q Fin positions. -/
theorem original_unit_position_sum_eq_q_slot_card
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ) :
    (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      originalWeightAtActualPosition
        N cap precision tau z0 lower (fun _ => (1 : ℝ)) Q i) =
      ((observedPhysicalSlotsAtQ N cap precision tau z0 lower Q).card : ℝ) := by
  classical
  rw [actual_position_rep_weight_sum]
  simp [slotRepresentativeArithmeticWeight, SlotAtQ]

/-- The TRUE fixed-Q physical-slot injection supplies a numerical
capacity bound; q collisions are not inserted as extra positions. -/
theorem original_unit_position_sum_le_q_frontier_length
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ) :
    (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      originalWeightAtActualPosition
        N cap precision tau z0 lower (fun _ => (1 : ℝ)) Q i) ≤
      ((actualPhysicalRankTwoList N cap z0 Q lower).length : ℝ) := by
  rw [original_unit_position_sum_eq_q_slot_card]
  exact_mod_cast observed_fixed_q_slots_card_le_frontier_length
    N cap precision tau z0 lower Q

/-- At every ORIGINAL observed physical Q, the sum of slot counts is
bounded by the sum of actual Fin-list lengths at that SAME Q. -/
theorem original_observed_q_slot_capacity_le_frontier
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    actualObservedQSlotCapacity N cap precision tau z0 lower ≤
      actualQFrontierPositionCapacity N cap precision tau z0 lower := by
  unfold actualObservedQSlotCapacity actualQFrontierPositionCapacity
  apply Finset.sum_le_sum
  intro Q hQ
  exact_mod_cast observed_fixed_q_slots_card_le_frontier_length
    N cap precision tau z0 lower Q

/-- EXACT original UNIT arithmetic source: one receipt per actual
observed physical slot plus every genuine q/tag/rejection surplus
in the SIX pre-existing lanes. This is not a source-to-history owner. -/
theorem original_unit_tagged_source_eq_actual_slots_and_six
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) :
    currentChenUpsilon3 N + currentChenUpsilon4 N =
      actualObservedQSlotCapacity N cap precision tau z0 lower +
        originalSixUnpaidReceiptLanes N cap precision tau z0 lower
          (fun _ => (1 : ℝ)) := by
  classical
  have hs := complete_original_source_at_actual_positions
    N cap precision tau z0 lower hzcap (fun _ => (1 : ℝ))
  have hcount :
      (∑ z ∈ originalTagged N, (1 : ℝ)) =
        currentChenUpsilon3 N + currentChenUpsilon4 N := by
    calc
      _ = ((originalTagged N).card : ℝ) := by simp
      _ = currentChenUpsilon3 N + currentChenUpsilon4 N :=
        (original_U34_eq_tagged_card N).symm
  have hpos :
      (∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
        ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
          originalWeightAtActualPosition
            N cap precision tau z0 lower (fun _ => (1 : ℝ)) Q i) =
        actualObservedQSlotCapacity N cap precision tau z0 lower := by
    unfold actualObservedQSlotCapacity
    apply Finset.sum_congr rfl
    intro Q hQ
    exact original_unit_position_sum_eq_q_slot_card
      N cap precision tau z0 lower Q
  rw [hcount, hpos] at hs
  exact hs

/-- ACTUAL finite-frontier UPPER capacity for all ORIGINAL U3/U4
tagged q receipts; the six surplus lanes are NOT dropped. -/
theorem original_unit_tagged_source_le_frontier_plus_six
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) :
    currentChenUpsilon3 N + currentChenUpsilon4 N ≤
      actualQFrontierPositionCapacity N cap precision tau z0 lower +
        originalSixUnpaidReceiptLanes N cap precision tau z0 lower
          (fun _ => (1 : ℝ)) := by
  have hsource := original_unit_tagged_source_eq_actual_slots_and_six
    N cap precision tau z0 lower hzcap
  have hcap := original_observed_q_slot_capacity_le_frontier
    N cap precision tau z0 lower
  linarith only [hsource, hcap]

/-- EXACT original signed quarter in terms of slot capacity plus
all six genuine UNIT surplus lanes. Both U3/U4 tags carry -1/4,
including the two receipts on their common original U4 band. -/
theorem original_negative_quarter_eq_slots_and_six
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) :
    originalU34SignedQuarter N =
      -(1 / 4 : ℝ) *
        (actualObservedQSlotCapacity N cap precision tau z0 lower +
          originalSixUnpaidReceiptLanes N cap precision tau z0 lower
            (fun _ => (1 : ℝ))) := by
  rw [originalU34SignedQuarter]
  rw [original_unit_tagged_source_eq_actual_slots_and_six
    N cap precision tau z0 lower hzcap]
  ring

/-- Unlike the preceding packet's UPPER signed-quarter inequality,
this is a genuine LOWER bound in the direction needed for Chen.
It pays with the FULL rank-two list lengths AND the six still-unpaid
q/tag lanes; no 7/2 root or 430+11 smallness is inferred. -/
theorem original_negative_quarter_lower_by_actual_frontier_capacity
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) :
    -(1 / 4 : ℝ) *
        (actualQFrontierPositionCapacity N cap precision tau z0 lower +
          originalSixUnpaidReceiptLanes N cap precision tau z0 lower
            (fun _ => (1 : ℝ))) ≤
      originalU34SignedQuarter N := by
  have hsource := original_unit_tagged_source_le_frontier_plus_six
    N cap precision tau z0 lower hzcap
  rw [originalU34SignedQuarter]
  linarith only [hsource]

end
end ImbalancedChen.Part5OriginalH430SignedQuarterFrontierCapacity
