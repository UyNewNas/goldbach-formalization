import ImbalancedChen.Part5OriginalH430U4ActualFinDoubleTag

/-!
P5.6 / h34 — aggregate literal U4 two-tag receipt liabilities on
DISTINCT real physical-Q rank-two Fin positions.

Earlier candidate sources found two tagged receipts at one retained
U4 slot, and an older global result bounded one-representative
six-lane shortfall. This increment counts distinct U4-overlap-occupied
physical slots at EVERY actual Q, transports their COMPLETE original
q/tag receipt fibres to the actual Fin positions, and splits their
unit weight into a mandatory two-tag baseline plus exact additional
receipts. Multiple U4 pairs with one slot contribute ONE baseline,
while all other q/tag receipts remain in the explicit excess.

This is a finite arithmetic source identity. It does not turn a
rank-two position into a selected/inherited causal owner or assert a
native Euler/root-norm payment. It does not cover the four outside
source rejection lanes. No manuscript target or analytic parameter is
changed. SOURCE_ONLY / CANDIDATE_UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430DistinctU4FinReceiptDebt

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430FixedQSlotInjection
open Part5OriginalH430FullTaggedActualFinPushforward
open Part5OriginalH430SequentialTaggedReceiptDebt
open Part5OriginalH430UpperRankTwoOwnerObstruction
open Part5OriginalH430U4ActualFinDoubleTag

/-- DISTINCT physically occupied slots at the actual Q for which
at least one original U4 pair has a retained left/U3 tagged receipt.
Using a Finset of SLOTS, rather than a sum over U4 pairs, avoids
charging the same physical slot twice. -/
def u4OverlapSlotsAtQ
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (Q : ℝ) : Finset (SlotAtQ N cap precision tau z0 lower Q) := by
  classical
  exact Finset.univ.filter (fun s =>
    ∃ x : TaggedPair,
      x ∈ originalPairs N .U4 ∧
      (Sum.inl x : TaggedReceiver) ∈
        retainedReceipts N cap precision tau z0 lower ∧
      physicalRankTwoSlot N precision tau
        (chosenRankTwoKey N cap precision tau z0 lower
          (Sum.inl x : TaggedReceiver)) = s.1)

/-- The actual real LIST positions of these distinct slots.
The fixed-Q physical-slot map is injective, but no tagged-receipt
injection is claimed. -/
def u4OverlapFinAtQ
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (Q : ℝ) :
    Finset (Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) :=
  (u4OverlapSlotsAtQ N cap precision tau z0 lower Q).image
    (fixedQSlotPositionMap N cap precision tau z0 lower Q)

/-- Every U4-overlap-occupied slot carries at least the literal
U3 and U4 arithmetic receipts from its witnessing original pair.
This does NOT mean that it has two independent history owners. -/
theorem u4_overlap_slot_card_ge_two
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (Q : ℝ)
    (s : SlotAtQ N cap precision tau z0 lower Q)
    (hs : s ∈ u4OverlapSlotsAtQ N cap precision tau z0 lower Q) :
    2 ≤ (originalReceiptsAtPhysicalSlot
      N cap precision tau z0 lower s.1).card := by
  classical
  obtain ⟨x, hx, hret, hslot⟩ :=
    (Finset.mem_filter.mp hs).2
  have htwo := original_u4_retained_slot_card_ge_two
    N cap precision tau z0 lower hN x hx hret
  simpa only [hslot] using htwo

/-- The selected TRUE Fin indices carry exactly the complete
receipt weights of the distinct physical U4-overlap slots.
No arbitrary postfilter or representative receipt is used. -/
theorem u4_overlap_fin_pushforward_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (Q : ℝ) (w : TaggedReceiver → ℝ) :
    (∑ i ∈ u4OverlapFinAtQ N cap precision tau z0 lower Q,
      actualAllTaggedAtFin N cap precision tau z0 lower w Q i) =
    ∑ s ∈ u4OverlapSlotsAtQ N cap precision tau z0 lower Q,
      actualSlotTaggedWeight N cap precision tau z0 lower w Q s := by
  classical
  unfold u4OverlapFinAtQ
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro s hs
    exact actual_all_tagged_at_injected_slot_exact
      N cap precision tau z0 lower w Q s
  · intro s hs t ht heq
    exact (fixed_q_slot_position_injective
      N cap precision tau z0 lower Q) heq

/-- For one actual physical Q, the FULL unit q/tag arithmetic
weight on the distinct U4-overlap Fin positions is EXACTLY
two times the number of such slots, plus every additional receipt
at those slots (natural subtraction is legitimate by the preceding
cardinality bound). No two slots or U4 pairs are quotient-merged. -/
theorem u4_overlap_fin_two_plus_extra_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (Q : ℝ) :
    (∑ i ∈ u4OverlapFinAtQ N cap precision tau z0 lower Q,
      actualAllTaggedAtFin N cap precision tau z0 lower
        (fun _ => (1 : ℝ)) Q i) =
    (2 : ℝ) *
      ((u4OverlapSlotsAtQ N cap precision tau z0 lower Q).card : ℝ) +
    ∑ s ∈ u4OverlapSlotsAtQ N cap precision tau z0 lower Q,
      (((originalReceiptsAtPhysicalSlot
        N cap precision tau z0 lower s.1).card - 2 : ℕ) : ℝ) := by
  classical
  calc
    _ = ∑ s ∈ u4OverlapSlotsAtQ N cap precision tau z0 lower Q,
        actualSlotTaggedWeight N cap precision tau z0 lower
          (fun _ => (1 : ℝ)) Q s :=
      u4_overlap_fin_pushforward_exact
        N cap precision tau z0 lower Q (fun _ => (1 : ℝ))
    _ = ∑ s ∈ u4OverlapSlotsAtQ N cap precision tau z0 lower Q,
        (2 : ℝ) +
          (((originalReceiptsAtPhysicalSlot
            N cap precision tau z0 lower s.1).card - 2 : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [actual_slot_unit_weight_is_receipt_count]
      have htwo := u4_overlap_slot_card_ge_two
        N cap precision tau z0 lower hN Q s hs
      have hnat :
          (originalReceiptsAtPhysicalSlot
            N cap precision tau z0 lower s.1).card =
          2 + ((originalReceiptsAtPhysicalSlot
            N cap precision tau z0 lower s.1).card - 2) := by
        omega
      exact_mod_cast hnat
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp [nsmul_eq_mul, mul_comm]

/-- The NEGATIVE quarter contribution at all double-occupied true
Fin positions of one Q has the exact, correct signed direction.
The excess remains an outstanding arithmetic liability. -/
theorem u4_overlap_fin_signed_quarter_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (Q : ℝ) :
    -(1 / 4 : ℝ) *
      (∑ i ∈ u4OverlapFinAtQ N cap precision tau z0 lower Q,
        actualAllTaggedAtFin N cap precision tau z0 lower
          (fun _ => (1 : ℝ)) Q i) =
      -(1 / 2 : ℝ) *
        ((u4OverlapSlotsAtQ N cap precision tau z0 lower Q).card : ℝ) -
      (1 / 4 : ℝ) *
        (∑ s ∈ u4OverlapSlotsAtQ
          N cap precision tau z0 lower Q,
          (((originalReceiptsAtPhysicalSlot
            N cap precision tau z0 lower s.1).card - 2 : ℕ) : ℝ)) := by
  rw [u4_overlap_fin_two_plus_extra_exact
    N cap precision tau z0 lower hN Q]
  ring

/-- All actual physical Q fibres are combined by adding the EXACT
per-Q signed charges. Different Q values are not collapsed, and
multiple U4 pairs mapping to one slot only create one two-tag
baseline. This remains a necessary source charge, not payment. -/
theorem all_actual_q_u4_overlap_signed_quarter_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) :
    (∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
      -(1 / 4 : ℝ) *
        (∑ i ∈ u4OverlapFinAtQ N cap precision tau z0 lower Q,
          actualAllTaggedAtFin N cap precision tau z0 lower
            (fun _ => (1 : ℝ)) Q i)) =
    ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
      (-(1 / 2 : ℝ) *
          ((u4OverlapSlotsAtQ N cap precision tau z0 lower Q).card : ℝ) -
        (1 / 4 : ℝ) *
          (∑ s ∈ u4OverlapSlotsAtQ
            N cap precision tau z0 lower Q,
            (((originalReceiptsAtPhysicalSlot
              N cap precision tau z0 lower s.1).card - 2 : ℕ) : ℝ))) := by
  classical
  apply Finset.sum_congr rfl
  intro Q hQ
  exact u4_overlap_fin_signed_quarter_exact
    N cap precision tau z0 lower hN Q

end
end ImbalancedChen.Part5OriginalH430DistinctU4FinReceiptDebt
