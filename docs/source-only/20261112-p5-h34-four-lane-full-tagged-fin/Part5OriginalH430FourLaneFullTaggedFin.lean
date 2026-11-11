import ImbalancedChen.Part5OriginalH430FullTaggedActualFinPushforward
import ImbalancedChen.Part5OriginalH430SignedQuarterFrontierCapacity

/-!
P5.6 / h34 — replace the two artificial representative-collision
lanes in the ORIGINAL six-lane source ledger with the complete tagged
(q, U3/U4) arithmetic weight on each TRUE rank-two Fin position.

There are still FOUR real original source rejection lanes:
failure of the second Rosser test, no possible second factor,
root-prime cutoff, and physical-Q root-policy refusal.
Neither within-slot q multiplicity nor U3/U4 cross-tag overlap is
silently erased: both are inside the new position weight.

This is an exact finite arithmetic identity, NOT an injective
receipt-to-history owner, not Euler-mass payment, not the original
full/selected/inherited mask and not a small error estimate.
SOURCE_ONLY / CANDIDATE_UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430FourLaneFullTaggedFin

noncomputable section
open scoped Classical BigOperators

open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedRankTwoFibreCapacity
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430FixedQSlotInjection
open Part5OriginalH430FixedQPositionFilterLedger
open Part5OriginalH430TruePositionReceiptLedger
open Part5OriginalH430UpperRetainedFinFibre
open Part5OriginalH430ActualRootStageReceipts
open Part5OriginalH430ActualSecondRosserRetention
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430SequentialTaggedReceiptDebt
open Part5OriginalH430FullTaggedActualFinPushforward
open Part5OriginalH430NegativeQuarterActualPositionDirection

/-- Exactly the four ORIGINAL receipt rejection terms not carried
by an observed physical slot. A q/tag collision is NOT included here:
all receipts at that occupied slot are now summed at its actual Fin
position. These four terms are still completely UNPAID. -/
def originalFourOutsidePositionLanes
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) : ℝ :=
  (∑ z ∈ (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower),
      if hasPostRootPrimeFactor z ∧
          ¬ hasRetainedOriginalSecond N cap precision tau z0 lower z
      then w z else 0) +
  (∑ z ∈ (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower),
      if ¬ hasPostRootPrimeFactor z then w z else 0) +
  (∑ z ∈ rootCutoffBlocked (originalTagged N) z0, w z) +
  (∑ z ∈ physicalPolicyBlocked N precision tau z0 lower, w z)

/-- A genuine retained original q/tag receipt belongs to exactly one
observed physical (Q,p,ell) slot, even if its slot has other receipts.
This is weighted finite Fubini, without a receipt-to-Fin injection. -/
theorem retained_receipts_all_physical_slots
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ retainedReceipts N cap precision tau z0 lower, w z) =
      ∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
        ∑ z ∈ originalReceiptsAtPhysicalSlot
          N cap precision tau z0 lower slot, w z := by
  classical
  calc
    _ = ∑ z ∈ retainedReceipts N cap precision tau z0 lower,
        ∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
          if physicalRankTwoSlot N precision tau
            (chosenRankTwoKey N cap precision tau z0 lower z) = slot
          then w z else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        have hs : physicalRankTwoSlot N precision tau
            (chosenRankTwoKey N cap precision tau z0 lower z) ∈
            observedPhysicalSlots N cap precision tau z0 lower := by
          exact Finset.mem_image.mpr
            ⟨chosenRankTwoKey N cap precision tau z0 lower z,
              Finset.mem_image.mpr ⟨z, hz, rfl⟩, rfl⟩
        rw [Finset.sum_ite_eq]
        simp [hs]
    _ = ∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
          ∑ z ∈ retainedReceipts N cap precision tau z0 lower,
            if physicalRankTwoSlot N precision tau
                (chosenRankTwoKey N cap precision tau z0 lower z) = slot
            then w z else 0 := by rw [Finset.sum_comm]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro slot hs
        simp only [originalReceiptsAtPhysicalSlot, Finset.sum_filter]

/-- Partition an observed source-slot sum by its own physical Q,
never by a common Q shared across U3 and U4. -/
private theorem physical_slot_sum_over_true_Q
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (f : ℝ × ℕ × ℕ → ℝ) :
    (∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
      f slot) =
    ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
      ∑ s : SlotAtQ N cap precision tau z0 lower Q, f s.1 := by
  classical
  calc
    _ = ∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
        ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
          if slot.1 = Q then f slot else 0 := by
        apply Finset.sum_congr rfl
        intro slot hs
        have hQ : slot.1 ∈
            observedReceiptQs N cap precision tau z0 lower :=
          Finset.mem_image.mpr ⟨slot, hs, rfl⟩
        rw [Finset.sum_ite_eq]
        simp [hQ]
    _ = ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
          ∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
            if slot.1 = Q then f slot else 0 := by
          rw [Finset.sum_comm]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro Q hQ
        simp [SlotAtQ, observedPhysicalSlotsAtQ, Finset.sum_filter]

/-- The ENTIRE retained original q/tag source reaches true bounded
Fin list positions at the actual Q. This is not a per-receipt owner:
several original receipts may have one common position and are all
counted there with their distinct arithmetic weights. -/
theorem retained_receipts_all_tagged_actual_fin
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ retainedReceipts N cap precision tau z0 lower, w z) =
    ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
      ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
        actualAllTaggedAtFin N cap precision tau z0 lower w Q i := by
  calc
    _ = ∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
          ∑ z ∈ originalReceiptsAtPhysicalSlot
            N cap precision tau z0 lower slot, w z :=
      retained_receipts_all_physical_slots
        N cap precision tau z0 lower w
    _ = ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
          ∑ s : SlotAtQ N cap precision tau z0 lower Q,
            actualSlotTaggedWeight N cap precision tau z0 lower w Q s := by
          simpa [actualSlotTaggedWeight] using
            (physical_slot_sum_over_true_Q
              N cap precision tau z0 lower
                (fun slot => ∑ z ∈ originalReceiptsAtPhysicalSlot
                  N cap precision tau z0 lower slot, w z))
    _ = _ := by
          apply Finset.sum_congr rfl
          intro Q hQ
          exact (actual_all_tagged_fin_total_exact
            N cap precision tau z0 lower w Q).symm

/-- The FULL ORIGINAL U3+U4 source is the complete tagged source on
true Fin positions plus precisely FOUR source rejection classes.
Two earlier six-lane collision/surplus terms have been MOVED into
the position source, NOT proved paid by its history mass. -/
theorem original_source_four_lanes_all_tagged_fin
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (w : TaggedReceiver → ℝ) :
    (∑ z ∈ originalTagged N, w z) =
      (∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
        ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
          actualAllTaggedAtFin N cap precision tau z0 lower w Q i) +
      originalFourOutsidePositionLanes
        N cap precision tau z0 lower w := by
  have h := original_count_source_five_unpaid_lanes
    N cap precision tau z0 lower hzcap w
  have hret :
      (∑ z ∈ (originalTagged N).filter
        (selectedOriginalRootStage N cap precision tau z0 lower),
        if hasRetainedOriginalSecond N cap precision tau z0 lower z
        then w z else 0) =
      ∑ z ∈ retainedReceipts N cap precision tau z0 lower, w z := by
    simp only [retainedReceipts, Finset.sum_filter]
  rw [hret, retained_receipts_all_tagged_actual_fin
    N cap precision tau z0 lower w] at h
  unfold originalFourOutsidePositionLanes
  convert h using 1 <;> ring

/-- The original signed Chen -1/4 contribution now contains the
COMPLETE tagged Fin-position arithmetic count plus four outstanding
source rejections; it is NOT a bound by root norm 7/2 or Euler mass. -/
theorem original_negative_quarter_four_lanes_all_tagged_fin
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) :
    originalU34SignedQuarter N =
      -(1 / 4 : ℝ) *
        ((∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
          ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
            actualAllTaggedAtFin N cap precision tau z0 lower
              (fun _ => (1 : ℝ)) Q i) +
          originalFourOutsidePositionLanes
            N cap precision tau z0 lower (fun _ => (1 : ℝ))) := by
  have hcount :
      (∑ z ∈ originalTagged N, (1 : ℝ)) =
        currentChenUpsilon3 N + currentChenUpsilon4 N := by
    calc
      _ = ((originalTagged N).card : ℝ) := by simp
      _ = currentChenUpsilon3 N + currentChenUpsilon4 N :=
        (original_U34_eq_tagged_card N).symm
  have hsource := original_source_four_lanes_all_tagged_fin
    N cap precision tau z0 lower hzcap (fun _ => (1 : ℝ))
  rw [hcount] at hsource
  rw [originalU34SignedQuarter, hsource]
  ring

end
end ImbalancedChen.Part5OriginalH430FourLaneFullTaggedFin
