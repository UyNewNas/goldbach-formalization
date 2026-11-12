import ImbalancedChen.Part5OriginalH430OriginalTagSeparatedFinSource
import ImbalancedChen.Part5OriginalH430UpperRankTwoOwnerObstruction

/-!
P5.6/h34: the literal original U4 double-tag obstruction INSIDE ONE
actual physical-Q rank-two Fin position, not merely at an abstract slot.

The whole signed q/tag receipt fibre of an observed physical slot is
exactly the weight at its canonical real Fin occurrence: the fixed-Q
slot-to-Fin map is injective. For one genuinely retained original U4
pair, that single position therefore carries at least two original
arithmetic receipts, and the exact remaining q/tag fibre is preserved.

No claim supplies two historical owners, pays this multiplicity with
Euler mass/root norm 7/2, or installs the full/selected/inherited filter.
SOURCE_ONLY / CANDIDATE_UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430U4ActualFinDoubleTag

noncomputable section
open scoped Classical BigOperators

open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430FixedQSlotInjection
open Part5OriginalH430FullTaggedActualFinPushforward
open Part5OriginalH430SequentialTaggedReceiptDebt
open Part5OriginalH430UpperRankTwoOwnerObstruction
open Part5OriginalH430OriginalTagSeparatedFinSource

/-- At the actual canonical Fin occurrence of an OBSERVED slot, the
entire signed original q/tag receipt fibre is present. No other
physical slot at the same Q contributes to that index (injectivity).
This is not an injection of original tagged RECEIPTS into Fin. -/
theorem actual_all_tagged_at_injected_slot_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) (Q : ℝ)
    (s : SlotAtQ N cap precision tau z0 lower Q) :
    actualAllTaggedAtFin N cap precision tau z0 lower w Q
      (fixedQSlotPositionMap N cap precision tau z0 lower Q s) =
    actualSlotTaggedWeight N cap precision tau z0 lower w Q s := by
  classical
  have hinj := fixed_q_slot_position_injective
    N cap precision tau z0 lower Q
  unfold actualAllTaggedAtFin
  calc
    (∑ t : SlotAtQ N cap precision tau z0 lower Q,
      if fixedQSlotPositionMap N cap precision tau z0 lower Q t =
          fixedQSlotPositionMap N cap precision tau z0 lower Q s
      then actualSlotTaggedWeight N cap precision tau z0 lower w Q t
      else 0) =
      ∑ t : SlotAtQ N cap precision tau z0 lower Q,
        if t = s then actualSlotTaggedWeight
          N cap precision tau z0 lower w Q t else 0 := by
        apply Finset.sum_congr rfl
        intro t ht
        by_cases h : t = s
        · subst t
          simp
        · have hneq :
              fixedQSlotPositionMap N cap precision tau z0 lower Q t ≠
                fixedQSlotPositionMap N cap precision tau z0 lower Q s := by
            intro heq
            exact h (hinj heq)
          simp [h, hneq]
    _ = actualSlotTaggedWeight N cap precision tau z0 lower w Q s := by
      simp

/-- Any genuinely retained original U4 (p,q) creates ONE specific
actual Fin position at its actual physical Q whose COMPLETE UNIT
arithmetic weight is two original tags plus ALL other q/tag receipts
in the same slot. The two tags are not two independently paid owners. -/
theorem original_u4_retained_one_actual_fin_two_plus_rest
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower) :
    let slot := physicalRankTwoSlot N precision tau
      (chosenRankTwoKey N cap precision tau z0 lower
        (Sum.inl x : TaggedReceiver))
    ∃ i : Fin (actualPhysicalRankTwoList N cap z0 slot.1 lower).length,
      actualAllTaggedAtFin N cap precision tau z0 lower
        (fun _ => (1 : ℝ)) slot.1 i =
      (2 : ℝ) +
        ((((originalReceiptsAtPhysicalSlot
          N cap precision tau z0 lower slot).erase
            (Sum.inl x : TaggedReceiver)).erase
            (Sum.inr x : TaggedReceiver)).card : ℝ) := by
  let key := chosenRankTwoKey N cap precision tau z0 lower
    (Sum.inl x : TaggedReceiver)
  let slot := physicalRankTwoSlot N precision tau key
  change ∃ i : Fin (actualPhysicalRankTwoList
      N cap z0 slot.1 lower).length,
    actualAllTaggedAtFin N cap precision tau z0 lower
      (fun _ => (1 : ℝ)) slot.1 i =
    (2 : ℝ) +
      ((((originalReceiptsAtPhysicalSlot
        N cap precision tau z0 lower slot).erase
          (Sum.inl x : TaggedReceiver)).erase
          (Sum.inr x : TaggedReceiver)).card : ℝ)
  have hk : key ∈ observedRankTwoKeys
      N cap precision tau z0 lower :=
    Finset.mem_image.mpr ⟨Sum.inl x, hret, rfl⟩
  have hs : slot ∈ observedPhysicalSlots
      N cap precision tau z0 lower :=
    Finset.mem_image.mpr ⟨key, hk, rfl⟩
  have hsQ : slot ∈ observedPhysicalSlotsAtQ
      N cap precision tau z0 lower slot.1 :=
    Finset.mem_filter.mpr ⟨hs, rfl⟩
  let s : SlotAtQ N cap precision tau z0 lower slot.1 :=
    ⟨slot, hsQ⟩
  refine ⟨fixedQSlotPositionMap
      N cap precision tau z0 lower slot.1 s, ?_⟩
  have hc : (originalReceiptsAtPhysicalSlot
        N cap precision tau z0 lower slot).card =
      2 + (((originalReceiptsAtPhysicalSlot
        N cap precision tau z0 lower slot).erase
          (Sum.inl x : TaggedReceiver)).erase
          (Sum.inr x : TaggedReceiver)).card := by
    simpa only [slot, key] using
      (original_u4_retained_slot_card_two_plus_remaining
        N cap precision tau z0 lower hN x hx hret)
  calc
    actualAllTaggedAtFin N cap precision tau z0 lower
        (fun _ => (1 : ℝ)) slot.1
        (fixedQSlotPositionMap N cap precision tau z0 lower slot.1 s) =
      actualSlotTaggedWeight N cap precision tau z0 lower
        (fun _ => (1 : ℝ)) slot.1 s :=
      actual_all_tagged_at_injected_slot_exact
        N cap precision tau z0 lower (fun _ => (1 : ℝ)) slot.1 s
    _ = ((originalReceiptsAtPhysicalSlot
        N cap precision tau z0 lower slot).card : ℝ) := by
      simpa only [s] using
        (actual_slot_unit_weight_is_receipt_count
          N cap precision tau z0 lower slot.1 s)
    _ = (2 : ℝ) +
        ((((originalReceiptsAtPhysicalSlot
          N cap precision tau z0 lower slot).erase
            (Sum.inl x : TaggedReceiver)).erase
            (Sum.inr x : TaggedReceiver)).card : ℝ) := by
      exact_mod_cast hc

/-- The literal Chen negative-quarter charge at that same actual Fin
position is -1/2 for the U3/U4 overlap tags, MINUS one quarter of
every additional original q/tag receipt sharing the physical slot.
It is not an Euler payment or a completed selected-count estimate. -/
theorem original_u4_retained_actual_fin_signed_double_charge
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower) :
    let slot := physicalRankTwoSlot N precision tau
      (chosenRankTwoKey N cap precision tau z0 lower
        (Sum.inl x : TaggedReceiver))
    ∃ i : Fin (actualPhysicalRankTwoList N cap z0 slot.1 lower).length,
      -(1 / 4 : ℝ) *
          actualAllTaggedAtFin N cap precision tau z0 lower
            (fun _ => (1 : ℝ)) slot.1 i =
        -(1 / 2 : ℝ) -
          (1 / 4 : ℝ) *
            ((((originalReceiptsAtPhysicalSlot
              N cap precision tau z0 lower slot).erase
                (Sum.inl x : TaggedReceiver)).erase
                (Sum.inr x : TaggedReceiver)).card : ℝ) := by
  obtain ⟨i, hi⟩ :=
    original_u4_retained_one_actual_fin_two_plus_rest
      N cap precision tau z0 lower hN x hx hret
  refine ⟨i, ?_⟩
  rw [hi]
  ring

end
end ImbalancedChen.Part5OriginalH430U4ActualFinDoubleTag
