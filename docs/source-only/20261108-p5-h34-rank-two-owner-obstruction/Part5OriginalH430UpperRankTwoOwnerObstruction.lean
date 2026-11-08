import ImbalancedChen.Part5OriginalH430UpperRankTwoPrefixCapacity
import ImbalancedChen.Part5OriginalH430OriginalUpperOverlapCount

/-!
P5.6 / h34: a concrete obstruction to an injective RANK-TWO owner
of the original U3/U4 retained arithmetic receivers.

For one genuinely retained original U4 (p,q), the U3 and U4
arithmetic tags survive at the SAME physical (Q,p,ell) slot.
The genuine ordinary-Rosser first-exit list has at most ONE Fin
position with the rank-two selected prefix [ell,p] at that Q.

This packet proves the resulting impossibility for an actual
receipt-to-Fin assignment, and isolates the literal Chen-quarter
cost of the two tags plus every OTHER original q/tag receipt in
that same slot. Neither an assumed owner nor an upper-bound
payment is introduced. The real full/selected/inherited owner
may live at a deeper history depth; this rank-two obstruction
does NOT rule out that possibility.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430UpperRankTwoOwnerObstruction

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430PhysicalSlotListPositions
open Part5OriginalH430UpperRetainedFinFibre
open Part5OriginalH430UpperRankTwoPrefixCapacity

/-- At the actual physical Q of an ORIGINAL retained U4 (p,q),
no injective assignment of ALL q/tag receipts at that slot to the
real rank-two Fin positions can preserve the actual [ell,p] prefix.

In particular, one cannot pay U3 and U4 by postulating two rank-two
owners for the same real first-exit event.  No claim about deeper
full/selected/inherited owner stages is made. -/
theorem original_u4_retained_no_injective_rank_two_fin_owner
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower) :
    let slot := physicalRankTwoSlot N precision tau
      (chosenRankTwoKey N cap precision tau z0 lower
        (Sum.inl x : TaggedReceiver))
    ¬ ∃ owner : TaggedReceiver →
          Fin (actualPhysicalRankTwoList N cap z0 slot.1 lower).length,
        Function.Injective owner ∧
        ∀ z ∈ originalReceiptsAtPhysicalSlot
            N cap precision tau z0 lower slot,
          (actualPhysicalRankTwoList
            N cap z0 slot.1 lower)[owner z].selectedPrefix =
            [slot.2.2, slot.2.1] := by
  dsimp
  rintro ⟨owner, hinj, hprefix⟩
  let slot := physicalRankTwoSlot N precision tau
    (chosenRankTwoKey N cap precision tau z0 lower
      (Sum.inl x : TaggedReceiver))
  have htwo := original_u4_retained_two_tags_in_slot_fibre
    N cap precision tau z0 lower hN x hx hret
  have hl : (actualPhysicalRankTwoList
        N cap z0 slot.1 lower)[owner (Sum.inl x)].selectedPrefix =
      [slot.2.2, slot.2.1] :=
    hprefix (Sum.inl x) htwo.1
  have hr : (actualPhysicalRankTwoList
        N cap z0 slot.1 lower)[owner (Sum.inr x)].selectedPrefix =
      [slot.2.2, slot.2.1] :=
    hprefix (Sum.inr x) htwo.2
  have heq : owner (Sum.inl x : TaggedReceiver) =
      owner (Sum.inr x : TaggedReceiver) :=
    actual_rank_two_prefix_position_unique
      N cap z0 slot.1 lower _ _ (hl.trans hr.symm)
  have hbad : (Sum.inl x : TaggedReceiver) =
      (Sum.inr x : TaggedReceiver) := hinj heq
  cases hbad

/-- The FULL original q/tag fibre has exactly two distinguished
retained U3/U4 receipts plus ALL other original q/tag receipts.
Unlike the lower bound on the cardinality, the leftover term
is an exact, unevaluated finite set of concrete arithmetic receipts. -/
theorem original_u4_retained_slot_card_two_plus_remaining
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower) :
    let slot := physicalRankTwoSlot N precision tau
      (chosenRankTwoKey N cap precision tau z0 lower
        (Sum.inl x : TaggedReceiver))
    let F := originalReceiptsAtPhysicalSlot
      N cap precision tau z0 lower slot
    F.card = 2 + ((F.erase (Sum.inl x)).erase (Sum.inr x)).card := by
  dsimp
  have h := original_u4_retained_slot_signed_two_tags_plus_other_q
    (M := ℕ) N cap precision tau z0 lower hN x hx hret
    (fun _ => (1 : ℕ))
  simpa using h

/-- Exact Chen negative-quarter coefficient on the real retained
slot fibre. The two actual arithmetic tags contribute -1/2 in all,
and the rest of the q/tag fibre is NOT silently discarded.
This is still an arithmetic count identity, not a historical
payment, an upper H430 selected-count estimate or a sign bound. -/
theorem original_u4_retained_slot_negative_quarter_with_remaining
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower) :
    let slot := physicalRankTwoSlot N precision tau
      (chosenRankTwoKey N cap precision tau z0 lower
        (Sum.inl x : TaggedReceiver))
    let F := originalReceiptsAtPhysicalSlot
      N cap precision tau z0 lower slot
    -(1 / 4 : ℝ) * (F.card : ℝ) =
      -(1 / 2 : ℝ) -
        (1 / 4 : ℝ) *
          (((F.erase (Sum.inl x)).erase (Sum.inr x)).card : ℝ) := by
  dsimp
  have hc := original_u4_retained_slot_card_two_plus_remaining
    N cap precision tau z0 lower hN x hx hret
  rw [hc]
  push_cast
  ring

end
end ImbalancedChen.Part5OriginalH430UpperRankTwoOwnerObstruction
