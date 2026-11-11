import ImbalancedChen.Part5OriginalH430SequentialSlotErasure
import ImbalancedChen.Part5OriginalH430U4PostfilterExactCapacity

/-!
P5.6 / h34 — genuine original tagged q-receipt weights on sequentially
filtered fixed-Q physical slots.

The previous sequential erasure accounting counted one unit per observed
(Q,p,ell) physical slot. That is not the original U3/U4 q/tag count:
several ORIGINAL tagged (p,q) receipts can have the same physical slot.
Here the two-stage partition is lifted to sums of ALL the arithmetic
receipts in each occupied slot, preserving arbitrary signed weights.
Both original U3/U4 tags, q multiplicities, and distinct physical Q
fibres are kept. No slot count is silently used to pay a receipt count.

The precise scopes are retained/observed original arithmetic receipts;
the existing six excluded/collision lanes, genuine full/selected/inherited
owner, native-history Euler costs and 430+11 inequalities stay unpaid.
The gates below are still actual Q-dependent tests, not an asserted
identification with the original manuscript's selected count owner.
SOURCE_ONLY / CANDIDATE_UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430SequentialTaggedReceiptDebt

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430FixedQPositionFilterLedger
open Part5OriginalH430TruePositionReceiptLedger
open Part5OriginalH430U4PostfilterExactCapacity
open Part5OriginalH430SequentialSlotErasure

/-- Sum ALL original q/tag arithmetic receipts at one actually observed
fixed-Q physical slot. It is not the unit slot weight, not the chosen
single representative, and not the rank-two history mass. -/
def actualSlotTaggedWeight
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) (Q : ℝ)
    (s : SlotAtQ N cap precision tau z0 lower Q) : ℝ :=
  ∑ z ∈ originalReceiptsAtPhysicalSlot
    N cap precision tau z0 lower s.1, w z

/-- The exact ORIGINAL arithmetic weight erased by a Q-dependent
filter on observed fixed-Q positions, keeping every q/tag occurrence. -/
def actualErasedTaggedReceiptWeight
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (keep : ℝ → FirstExitDepthState ℕ → Bool)
    (w : TaggedReceiver → ℝ) : ℝ :=
  ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
    ∑ s ∈ erasedSlots N cap precision tau z0 lower Q (keep Q),
      actualSlotTaggedWeight N cap precision tau z0 lower w Q s

/-- The NEW original tagged receipt weight charged only to physical
slots which survive the first actual-Q gate and fail the second. -/
def actualSecondStageTaggedReceiptWeight
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (first second : ℝ → FirstExitDepthState ℕ → Bool)
    (w : TaggedReceiver → ℝ) : ℝ :=
  ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
    ∑ s ∈ keptSlots N cap precision tau z0 lower Q (first Q) ∩
        erasedSlots N cap precision tau z0 lower Q (second Q),
      actualSlotTaggedWeight N cap precision tau z0 lower w Q s

/-- At one actual Q, the original SIGNED q/tag source erasure splits
without overlap: first rejected slots plus the newly rejected ones.
The per-slot weight is the sum over its whole original receipt fibre. -/
theorem fixed_q_sequential_tagged_erasure_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (first second : FirstExitDepthState ℕ → Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ s ∈ erasedSlots N cap precision tau z0 lower Q
        (fun t => first t && second t),
      actualSlotTaggedWeight N cap precision tau z0 lower w Q s) =
    (∑ s ∈ erasedSlots N cap precision tau z0 lower Q first,
      actualSlotTaggedWeight N cap precision tau z0 lower w Q s) +
    (∑ s ∈ keptSlots N cap precision tau z0 lower Q first ∩
        erasedSlots N cap precision tau z0 lower Q second,
      actualSlotTaggedWeight N cap precision tau z0 lower w Q s) := by
  classical
  rw [erased_slots_sequential_exact
    N cap precision tau z0 lower Q first second]
  exact Finset.sum_union
    (first_erased_disjoint_second_increment
      N cap precision tau z0 lower Q first second)

/-- Full original receipt source at this physical Q equals the
surviving actual slots, first-stage deleted q/tag receipts, and NEW
second-stage deleted q/tag receipts. No signed cancellation is
presumed and no owner mass is inserted. -/
theorem fixed_q_sequential_tagged_conservation
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (first second : FirstExitDepthState ℕ → Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ s : SlotAtQ N cap precision tau z0 lower Q,
      actualSlotTaggedWeight N cap precision tau z0 lower w Q s) =
    (∑ s ∈ keptSlots N cap precision tau z0 lower Q
        (fun t => first t && second t),
      actualSlotTaggedWeight N cap precision tau z0 lower w Q s) +
    (∑ s ∈ erasedSlots N cap precision tau z0 lower Q first,
      actualSlotTaggedWeight N cap precision tau z0 lower w Q s) +
    (∑ s ∈ keptSlots N cap precision tau z0 lower Q first ∩
        erasedSlots N cap precision tau z0 lower Q second,
      actualSlotTaggedWeight N cap precision tau z0 lower w Q s) := by
  have h := original_fixed_Q_receipt_filter_signed
    N cap precision tau z0 lower Q
    (fun t => first t && second t) w
  change (∑ s : SlotAtQ N cap precision tau z0 lower Q,
      actualSlotTaggedWeight N cap precision tau z0 lower w Q s) =
    (∑ s ∈ keptSlots N cap precision tau z0 lower Q
        (fun t => first t && second t),
      actualSlotTaggedWeight N cap precision tau z0 lower w Q s) +
    (∑ s ∈ erasedSlots N cap precision tau z0 lower Q
        (fun t => first t && second t),
      actualSlotTaggedWeight N cap precision tau z0 lower w Q s) at h
  rw [fixed_q_sequential_tagged_erasure_exact
    N cap precision tau z0 lower Q first second w] at h
  exact h

/-- For ALL truly observed physical Q, new/old tagged q debt is
additive even with signed w and repeated q receipts at a single slot.
The result is not the coarser cardinal slot-debt equation. -/
theorem actual_sequential_tagged_erasure_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (first second : ℝ → FirstExitDepthState ℕ → Bool)
    (w : TaggedReceiver → ℝ) :
    actualErasedTaggedReceiptWeight N cap precision tau z0 lower
      (sequentialQGate first second) w =
    actualErasedTaggedReceiptWeight N cap precision tau z0 lower first w +
      actualSecondStageTaggedReceiptWeight N cap precision tau z0 lower
        first second w := by
  unfold actualErasedTaggedReceiptWeight
    actualSecondStageTaggedReceiptWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Q hQ
  exact fixed_q_sequential_tagged_erasure_exact
    N cap precision tau z0 lower Q (first Q) (second Q) w

/-- Unit original arithmetic weight is the ACTUAL receipt-fibre
cardinality, not 1 per observed physical slot. This records possible
U4 two-tag overlap and repeated q contributions without merging them. -/
theorem actual_slot_unit_weight_is_receipt_count
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (s : SlotAtQ N cap precision tau z0 lower Q) :
    actualSlotTaggedWeight N cap precision tau z0 lower
      (fun _ => (1 : ℝ)) Q s =
      ((originalReceiptsAtPhysicalSlot
        N cap precision tau z0 lower s.1).card : ℝ) := by
  simp [actualSlotTaggedWeight]

/-- The literal ordinary Rosser full-prefix gate does not delete
any original tagged receipt at its first stage. This is only that
already-proved genuine policy, not a full/selected/inherited licence. -/
theorem actual_full_prefix_tagged_erasure_zero
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    actualErasedTaggedReceiptWeight N cap precision tau z0 lower
      (fun Q => actualFullPrefixGate lower Q) w = 0 := by
  unfold actualErasedTaggedReceiptWeight
  apply Finset.sum_eq_zero
  intro Q hQ
  rw [actual_full_prefix_erases_no_observed_slots
    N cap precision tau z0 lower Q]
  simp

/-- Hence a real ordinary full-prefix first stage leaves ONLY the
actual second-stage original q/tag debt, not just second-stage SLOT
cardinality. No smallness bound or selected-count owner is claimed. -/
theorem actual_after_full_prefix_tagged_erasure_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (second : ℝ → FirstExitDepthState ℕ → Bool)
    (w : TaggedReceiver → ℝ) :
    actualErasedTaggedReceiptWeight N cap precision tau z0 lower
      (sequentialQGate (fun Q => actualFullPrefixGate lower Q) second) w =
    actualSecondStageTaggedReceiptWeight N cap precision tau z0 lower
      (fun Q => actualFullPrefixGate lower Q) second w := by
  rw [actual_sequential_tagged_erasure_exact,
    actual_full_prefix_tagged_erasure_zero]
  simp

end
end ImbalancedChen.Part5OriginalH430SequentialTaggedReceiptDebt
