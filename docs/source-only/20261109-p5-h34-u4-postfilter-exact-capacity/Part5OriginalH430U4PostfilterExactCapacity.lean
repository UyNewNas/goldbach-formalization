import ImbalancedChen.Part5OriginalH430UpperRankTwoPrefixCapacity

/-!
P5.6 / h34: exact original q/tag receipt shortfall after an ACTUAL
rank-two Fin-position filter at a fixed physical (Q,p,ell) slot.

The rank-two recursive list has exactly one occurrence with the selected
prefix [ell,p] for an observed physical slot. This file computes whether
that ONE occurrence survives a specified Boolean post-frontier filter
and then counts the complete original retained arithmetic q/tag fibre
against precisely that zero-or-one position. For genuine original U4
overlap, TWO tagged receipts survive together at the same physical slot.

An arbitrary post-frontier Bool is NOT the manuscript full/selected/
inherited owner. The difference between a q/tag receipt count and a
Fin-position count is a necessary source-capacity shortfall, NOT a
proved signed payment, not a matching of q to the history product and
not an H430 upper estimate. The ordinary full-prefix policy already
built into the recursion has no erasure; the missing owner masks remain.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430U4PostfilterExactCapacity

noncomputable section

open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430PhysicalSlotListPositions
open Part5OriginalH430FixedQPositionFilterLedger
open Part5OriginalH430UpperRetainedFinFibre
open Part5OriginalH430UpperRankTwoPrefixCapacity

/-- Actual rank-two Fin positions for one literal physical slot which
survive a specified post-frontier position filter. Unlike a q/tag
fibre, these are positions of the genuine recursive LIST. -/
def actualSlotPostfilterPositions
    (N cap : ℕ) (z0 Q : ℝ) (lower : Bool) (p ell : ℕ)
    (keep : FirstExitDepthState ℕ → Bool) :
    Finset (Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) :=
  actualRankTwoPrefixPositions N cap z0 Q lower p ell ∩
    keptPositions N cap z0 Q lower keep

/-- For an observed slot the post-filtered genuine prefix fibre is
EITHER its unique actual Fin position OR empty. There cannot be a
separate historical position for a second original arithmetic tag. -/
theorem observed_slot_postfilter_positions_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (slot : ℝ × ℕ × ℕ)
    (hs : slot ∈ observedPhysicalSlots N cap precision tau z0 lower)
    (keep : FirstExitDepthState ℕ → Bool) :
    actualSlotPostfilterPositions
      N cap z0 slot.1 lower slot.2.1 slot.2.2 keep =
      if keep ((actualPhysicalRankTwoList N cap z0 slot.1 lower)[
          observedSlotRankTwoPosition
            N cap precision tau z0 lower slot hs]) = true
      then {observedSlotRankTwoPosition
        N cap precision tau z0 lower slot hs}
      else ∅ := by
  classical
  unfold actualSlotPostfilterPositions
  rw [observed_slot_rank_two_prefix_positions_singleton
    N cap precision tau z0 lower slot hs]
  by_cases h : keep ((actualPhysicalRankTwoList N cap z0 slot.1 lower)[
      observedSlotRankTwoPosition N cap precision tau z0 lower slot hs]) = true
  · simp [keptPositions, h]
  · simp [keptPositions, h]

/-- Exact post-filter multiplicity, zero or one, of the REAL
rank-two list position at a genuinely observed physical slot. -/
theorem observed_slot_postfilter_card_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (slot : ℝ × ℕ × ℕ)
    (hs : slot ∈ observedPhysicalSlots N cap precision tau z0 lower)
    (keep : FirstExitDepthState ℕ → Bool) :
    (actualSlotPostfilterPositions
      N cap z0 slot.1 lower slot.2.1 slot.2.2 keep).card =
      if keep ((actualPhysicalRankTwoList N cap z0 slot.1 lower)[
          observedSlotRankTwoPosition
            N cap precision tau z0 lower slot hs]) = true
      then 1 else 0 := by
  rw [observed_slot_postfilter_positions_exact
    N cap precision tau z0 lower slot hs keep]
  split_ifs <;> simp

/-- A source fibre with at least one genuine original arithmetic
receipt has an exact residual count after retaining at most its ONE
actual rank-two position. A removed prefix costs one more receipt
beyond the already unavoidable source-minus-singleton difference.
This is an equality of NATURAL CARDINALITIES, not a payment rule. -/
theorem observed_slot_exact_postfilter_excess
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (slot : ℝ × ℕ × ℕ)
    (hs : slot ∈ observedPhysicalSlots N cap precision tau z0 lower)
    (keep : FirstExitDepthState ℕ → Bool)
    (hsource : 1 ≤
      (originalReceiptsAtPhysicalSlot
        N cap precision tau z0 lower slot).card) :
    (originalReceiptsAtPhysicalSlot
      N cap precision tau z0 lower slot).card -
      (actualSlotPostfilterPositions
        N cap z0 slot.1 lower slot.2.1 slot.2.2 keep).card =
      ((originalReceiptsAtPhysicalSlot
        N cap precision tau z0 lower slot).card - 1) +
      (if keep ((actualPhysicalRankTwoList N cap z0 slot.1 lower)[
          observedSlotRankTwoPosition
            N cap precision tau z0 lower slot hs]) = true
       then 0 else 1) := by
  rw [observed_slot_postfilter_card_exact
    N cap precision tau z0 lower slot hs keep]
  split_ifs <;> omega

/-- The literal physical slot of the LEFT original U4 receipt.
This uses the original retained second-prime choice, not q in place
of the selected history letter ell. -/
def actualU4OverlapSlot
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (x : TaggedPair) : ℝ × ℕ × ℕ :=
  physicalRankTwoSlot N precision tau
    (chosenRankTwoKey N cap precision tau z0 lower
      (Sum.inl x : TaggedReceiver))

/-- A genuinely retained original U4 quotient puts its physical slot
in the actual observed image of retained original q/tag receipts. -/
theorem actual_u4_overlap_slot_observed
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (x : TaggedPair)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower) :
    actualU4OverlapSlot N cap precision tau z0 lower x ∈
      observedPhysicalSlots N cap precision tau z0 lower := by
  exact Finset.mem_image.mpr
    ⟨chosenRankTwoKey N cap precision tau z0 lower
      (Sum.inl x : TaggedReceiver),
      Finset.mem_image.mpr
        ⟨(Sum.inl x : TaggedReceiver), hret, rfl⟩, rfl⟩

/-- Exact U4 TWO-TAG arithmetic shortfall at its genuine physical slot,
including any other q/tag receipts at that slot. If the real single
rank-two position is deleted the whole original fibre remains; if
retained the excess is its cardinality minus one. This DOES NOT
identify or pay the original manuscript's count-owner obligation. -/
theorem original_u4_retained_exact_postfilter_excess
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower)
    (keep : FirstExitDepthState ℕ → Bool) :
    let slot := actualU4OverlapSlot N cap precision tau z0 lower x
    let hs := actual_u4_overlap_slot_observed
      N cap precision tau z0 lower x hret
    (originalReceiptsAtPhysicalSlot
      N cap precision tau z0 lower slot).card -
      (actualSlotPostfilterPositions
        N cap z0 slot.1 lower slot.2.1 slot.2.2 keep).card =
      ((originalReceiptsAtPhysicalSlot
        N cap precision tau z0 lower slot).card - 1) +
      (if keep ((actualPhysicalRankTwoList N cap z0 slot.1 lower)[
          observedSlotRankTwoPosition
            N cap precision tau z0 lower slot hs]) = true
       then 0 else 1) := by
  have hs := actual_u4_overlap_slot_observed
    N cap precision tau z0 lower x hret
  have htwo : 2 ≤ (originalReceiptsAtPhysicalSlot
      N cap precision tau z0 lower
        (actualU4OverlapSlot N cap precision tau z0 lower x)).card := by
    simpa only [actualU4OverlapSlot] using
      (original_u4_retained_slot_card_ge_two
        N cap precision tau z0 lower hN x hx hret)
  exact observed_slot_exact_postfilter_excess
    N cap precision tau z0 lower
    (actualU4OverlapSlot N cap precision tau z0 lower x)
    hs keep (by omega)

/-- The exact signed original q/tag source attached to actual
fixed-Q slots is retained under the position filter PLUS its erased
lane. No unsigned cardinal replaces arbitrary signed receipt weights;
no claim is made that these receipts have an historical payment. -/
theorem original_fixed_Q_receipt_filter_signed
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (keep : FirstExitDepthState ℕ → Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ s : SlotAtQ N cap precision tau z0 lower Q,
      ∑ z ∈ originalReceiptsAtPhysicalSlot
        N cap precision tau z0 lower s.1, w z) =
    (∑ s ∈ keptSlots N cap precision tau z0 lower Q keep,
      ∑ z ∈ originalReceiptsAtPhysicalSlot
        N cap precision tau z0 lower s.1, w z) +
    (∑ s ∈ erasedSlots N cap precision tau z0 lower Q keep,
      ∑ z ∈ originalReceiptsAtPhysicalSlot
        N cap precision tau z0 lower s.1, w z) := by
  exact observed_slot_erasure_signed
    N cap precision tau z0 lower Q keep
    (fun s => ∑ z ∈ originalReceiptsAtPhysicalSlot
      N cap precision tau z0 lower s, w z)

end
end ImbalancedChen.Part5OriginalH430U4PostfilterExactCapacity
