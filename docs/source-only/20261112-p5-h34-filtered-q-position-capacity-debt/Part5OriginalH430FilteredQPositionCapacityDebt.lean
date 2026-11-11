import ImbalancedChen.Part5OriginalH430SignedQuarterFrontierCapacity

/-!
P5.6 / h34 — replace the unfiltered per-Q frontier-length charge by
the number of TRUE kept Fin positions, while retaining the ORIGINAL
arithmetic-source charge for every erased observed physical slot.

The filter is explicitly Q-DEPENDENT. It is NOT asserted to equal the
manuscript's full/selected/inherited owner. We do not turn erased
slots into free capacity or count a q/tag collision as a new position.
The original six q/tag rejection lanes remain on the right-hand side.

All exact identities and inequalities here are manuscript-INTERNAL.
No new external analytic input or target-equivalent assumption.
SOURCE_ONLY / CANDIDATE_UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430FilteredQPositionCapacityDebt

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalSlotListPositions
open Part5OriginalH430FixedQPositionFilterLedger
open Part5OriginalH430QDependentPositionErasure
open Part5OriginalH430ActualPositionMassGap
open Part5OriginalH430OriginalUpperOverlapCount
open Part5OriginalH430NegativeQuarterActualPositionDirection
open Part5OriginalH430SignedQuarterFrontierCapacity

/-- Actual surviving LIST positions, with distinct occurrences counted
separately for each physical Q. This is not a paid selected owner. -/
def actualFilteredQPositionCapacity
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) : ℝ :=
  ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
    ((keptPositions N cap z0 Q lower (keep Q)).card : ℝ)

/-- Actual observed physical slots erased by the Q-dependent filter.
Their source representatives must still be paid, even if the
corresponding frontier list positions were rejected. -/
def actualErasedQSlotDebt
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) : ℝ :=
  ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
    ((erasedSlots N cap precision tau z0 lower Q (keep Q)).card : ℝ)

/-- Actual observed physical slots surviving that same Q-dependent
filter; a slot is counted once, not once for every q/tag receipt. -/
def actualKeptQSlotCapacity
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) : ℝ :=
  ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
    ((keptSlots N cap precision tau z0 lower Q (keep Q)).card : ℝ)

/-- Exact source partition across ALL actually observed physical Qs.
The deleted slot cost survives; this does not use a sign assumption. -/
theorem actual_observed_q_slots_eq_kept_plus_erased
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    actualObservedQSlotCapacity N cap precision tau z0 lower =
      actualKeptQSlotCapacity N cap precision tau z0 lower keep +
      actualErasedQSlotDebt N cap precision tau z0 lower keep := by
  unfold actualObservedQSlotCapacity actualKeptQSlotCapacity
    actualErasedQSlotDebt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Q hQ
  exact_mod_cast observed_slot_erasure_card
    N cap precision tau z0 lower Q (keep Q)

/-- The surviving physical slots inject into the actual surviving
Fin positions at each fixed Q. No chosen list index is duplicated. -/
theorem actual_kept_q_slots_le_filtered_positions
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    actualKeptQSlotCapacity N cap precision tau z0 lower keep ≤
      actualFilteredQPositionCapacity N cap precision tau z0 lower keep := by
  unfold actualKeptQSlotCapacity actualFilteredQPositionCapacity
  apply Finset.sum_le_sum
  intro Q hQ
  exact_mod_cast kept_slots_le_kept_positions
    N cap precision tau z0 lower Q (keep Q)

/-- Stronger than charging ALL frontier positions: charge only
survivors, but explicitly ADD the deleted arithmetic-slot debt. -/
theorem actual_observed_q_slots_le_filtered_plus_erased
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    actualObservedQSlotCapacity N cap precision tau z0 lower ≤
      actualFilteredQPositionCapacity N cap precision tau z0 lower keep +
      actualErasedQSlotDebt N cap precision tau z0 lower keep := by
  have hsplit := actual_observed_q_slots_eq_kept_plus_erased
    N cap precision tau z0 lower keep
  have hkeep := actual_kept_q_slots_le_filtered_positions
    N cap precision tau z0 lower keep
  linarith only [hsplit, hkeep]

/-- Explicit witness that the kept-position charge is no larger than
the old FULL rank-two list charge. This ALONE does not bound erasures. -/
theorem actual_filtered_q_capacity_le_full_frontier
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    actualFilteredQPositionCapacity N cap precision tau z0 lower keep ≤
      actualQFrontierPositionCapacity N cap precision tau z0 lower := by
  unfold actualFilteredQPositionCapacity actualQFrontierPositionCapacity
  apply Finset.sum_le_sum
  intro Q hQ
  have hsubset :
      keptPositions N cap z0 Q lower (keep Q) ⊆
      (Finset.univ :
        Finset (Fin (actualPhysicalRankTwoList N cap z0 Q lower).length)) :=
    Finset.subset_univ _
  have hcard := Finset.card_le_card hsubset
  exact_mod_cast (by simpa using hcard : 
    (keptPositions N cap z0 Q lower (keep Q)).card ≤
      (actualPhysicalRankTwoList N cap z0 Q lower).length)

/-- ORIGINAL unit-weight tagged q source, with U4 overlapping tags
both retained: exact kept physical slots + erased slots + SIX
previously identified original q/tag collision/rejection lanes. -/
theorem original_unit_source_eq_filtered_slots_erased_and_six
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    currentChenUpsilon3 N + currentChenUpsilon4 N =
      (actualKeptQSlotCapacity N cap precision tau z0 lower keep +
       actualErasedQSlotDebt N cap precision tau z0 lower keep) +
      originalSixUnpaidReceiptLanes N cap precision tau z0 lower
        (fun _ => (1 : ℝ)) := by
  rw [original_unit_tagged_source_eq_actual_slots_and_six
    N cap precision tau z0 lower hzcap,
    actual_observed_q_slots_eq_kept_plus_erased
      N cap precision tau z0 lower keep]

/-- A true FILTERED upper envelope for the original tagged source:
the historical Fin-position capacity is accompanied by the FULL
arithmetical erased-slot debt AND all six original lanes. -/
theorem original_unit_source_le_filtered_positions_with_all_debts
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    currentChenUpsilon3 N + currentChenUpsilon4 N ≤
      (actualFilteredQPositionCapacity N cap precision tau z0 lower keep +
       actualErasedQSlotDebt N cap precision tau z0 lower keep) +
      originalSixUnpaidReceiptLanes N cap precision tau z0 lower
        (fun _ => (1 : ℝ)) := by
  have hsource := original_unit_source_eq_filtered_slots_erased_and_six
    N cap precision tau z0 lower hzcap keep
  have hkept := actual_kept_q_slots_le_filtered_positions
    N cap precision tau z0 lower keep
  linarith only [hsource, hkept]

/-- Correct Chen LOWER orientation for the exact original -1/4
term. No deleted source, Q collision or rejected tag is discarded.
This is still NOT a quantitative paid root-7/2 selected owner. -/
theorem original_negative_quarter_lower_by_filtered_position_debts
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    -(1 / 4 : ℝ) *
        ((actualFilteredQPositionCapacity
            N cap precision tau z0 lower keep +
          actualErasedQSlotDebt
            N cap precision tau z0 lower keep) +
          originalSixUnpaidReceiptLanes N cap precision tau z0 lower
            (fun _ => (1 : ℝ))) ≤
      originalU34SignedQuarter N := by
  have hsource := original_unit_source_le_filtered_positions_with_all_debts
    N cap precision tau z0 lower hzcap keep
  rw [originalU34SignedQuarter]
  linarith only [hsource]

/-- The true ordinary Rosser FULL-prefix gate of this SAME frontier
erases no observed physical slot. This is NOT the manuscript's
additional full/selected/inherited count-source gate. -/
theorem actual_ordinary_full_prefix_erased_debt_zero
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    actualErasedQSlotDebt N cap precision tau z0 lower
      (fun Q => actualFullPrefixGate lower Q) = 0 := by
  unfold actualErasedQSlotDebt
  apply Finset.sum_eq_zero
  intro Q hQ
  rw [actual_full_prefix_erases_no_observed_slots
    N cap precision tau z0 lower Q]
  simp

/-- Specialization to the true ordinary full-prefix frontier:
all positions were already admitted, so its count does not
magically reduce the old frontier bound. -/
theorem actual_ordinary_full_prefix_kept_capacity_eq_frontier
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    actualFilteredQPositionCapacity N cap precision tau z0 lower
      (fun Q => actualFullPrefixGate lower Q) =
      actualQFrontierPositionCapacity N cap precision tau z0 lower := by
  unfold actualFilteredQPositionCapacity actualQFrontierPositionCapacity
  apply Finset.sum_congr rfl
  intro Q hQ
  rw [actual_full_prefix_keeps_positions]
  simp

end
end ImbalancedChen.Part5OriginalH430FilteredQPositionCapacityDebt
