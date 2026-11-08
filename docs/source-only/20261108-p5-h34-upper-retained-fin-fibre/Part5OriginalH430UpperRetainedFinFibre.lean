import ImbalancedChen.Part5OriginalH430UpperRetainedTagPairing
import ImbalancedChen.Part5OriginalH430PhysicalSlotListPositions
import ImbalancedChen.Part5OriginalH430FixedQPositionFilterLedger

/-!
P5.6 / h34: a surviving original U4 quotient gives TWO distinct tagged
arithmetic receipts attached to ONE physical (Q,p,ell) slot, and that
slot has an actual Fin-indexed rank-two recursive frontier occurrence.

The prior tag-pairing packet supplied true retention equivalence and
common physical slot, but did not quantify the source multiplicity AT
a genuine Fin list position. Here both receipts are located in the
same literal physical-slot fibre and its cardinal is at least two;
all additional q/tag receipts remain explicitly in the signed sum.

The canonical Fin witness is taken from the ACTUAL rank-two list at
the actual physical Q, not a fabricated history or a per-q index.
The verified ordinary complete-prefix Rosser test is not a proof
of the manuscript full/selected/inherited owner or payment capacity.
No second historical occurrence is created for the other tag.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430UpperRetainedFinFibre

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedRankTwoFibreCapacity
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430PhysicalSlotListPositions
open Part5OriginalH430FixedQPositionFilterLedger
open Part5OriginalH430UpperOverlapCommonQ
open Part5OriginalH430UpperRetainedTagPairing

/-- The genuine retained ORIGINAL q/tag receipts attached to a fixed
physical (Q,p,ell) slot; it is a filter of the original finite source,
not a quotient by q or by the arithmetic U3/U4 tag. -/
def originalReceiptsAtPhysicalSlot
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (slot : ℝ × ℕ × ℕ) : Finset TaggedReceiver :=
  (retainedReceipts N cap precision tau z0 lower).filter
    (fun z =>
      physicalRankTwoSlot N precision tau
        (chosenRankTwoKey N cap precision tau z0 lower z) = slot)

/-- From ONE actually retained original U4 (p,q), BOTH distinct
arithmetic tags belong to exactly the same original source fibre.
The original q remains in each receipt, not replaced by ell. -/
theorem original_u4_retained_two_tags_in_slot_fibre
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower) :
    let slot := physicalRankTwoSlot N precision tau
      (chosenRankTwoKey N cap precision tau z0 lower
        (Sum.inl x : TaggedReceiver))
    (Sum.inl x : TaggedReceiver) ∈
      originalReceiptsAtPhysicalSlot N cap precision tau z0 lower slot ∧
    (Sum.inr x : TaggedReceiver) ∈
      originalReceiptsAtPhysicalSlot N cap precision tau z0 lower slot := by
  dsimp
  have hright : (Sum.inr x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower :=
    (original_u4_retained_inl_iff_inr
      N cap precision tau z0 lower hN x hx).mp hret
  have hslot := original_u4_overlap_actual_slot_equal
    N cap precision tau z0 lower hN x hx
  exact ⟨Finset.mem_filter.mpr ⟨hret, rfl⟩,
    Finset.mem_filter.mpr ⟨hright, hslot.symm⟩⟩

/-- At the actual common U4 physical slot the source cardinality
is AT LEAST TWO, irrespective of any other q sharing that slot.
This counts arithmetic receipts, not frontier state occurrences. -/
theorem original_u4_retained_slot_card_ge_two
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower) :
    2 ≤ (originalReceiptsAtPhysicalSlot N cap precision tau z0 lower
      (physicalRankTwoSlot N precision tau
        (chosenRankTwoKey N cap precision tau z0 lower
          (Sum.inl x : TaggedReceiver)))).card := by
  let slot := physicalRankTwoSlot N precision tau
    (chosenRankTwoKey N cap precision tau z0 lower
      (Sum.inl x : TaggedReceiver))
  have htwo := original_u4_retained_two_tags_in_slot_fibre
    N cap precision tau z0 lower hN x hx hret
  have hsub :
      ({(Sum.inl x : TaggedReceiver), (Sum.inr x : TaggedReceiver)} :
        Finset TaggedReceiver) ⊆
        originalReceiptsAtPhysicalSlot
          N cap precision tau z0 lower slot := by
    intro z hz
    have he : z = (Sum.inl x : TaggedReceiver) ∨
        z = (Sum.inr x : TaggedReceiver) := by simpa using hz
    rcases he with he | he
    · subst z
      exact htwo.1
    · subst z
      exact htwo.2
  have hcard := Finset.card_le_card hsub
  have htwoCard :
      ({(Sum.inl x : TaggedReceiver), (Sum.inr x : TaggedReceiver)} :
        Finset TaggedReceiver).card = 2 := by simp
  change 2 ≤
    (originalReceiptsAtPhysicalSlot
      N cap precision tau z0 lower slot).card
  omega

/-- The original receipt excess over ONE physical-slot representative.
It is not automatically a positive signed financial/payment deficit. -/
def originalPhysicalSlotReceiptExcess
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (slot : ℝ × ℕ × ℕ) : ℕ :=
  (originalReceiptsAtPhysicalSlot
    N cap precision tau z0 lower slot).card - 1

/-- A single surviving original U4 quotient forces at least one
extra tagged source receipt beyond ONE physical-slot representative.
The actual count may be larger because of other original q values. -/
theorem original_u4_retained_forces_positive_slot_excess
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower) :
    1 ≤ originalPhysicalSlotReceiptExcess
      N cap precision tau z0 lower
      (physicalRankTwoSlot N precision tau
        (chosenRankTwoKey N cap precision tau z0 lower
          (Sum.inl x : TaggedReceiver))) := by
  have htwo := original_u4_retained_slot_card_ge_two
    N cap precision tau z0 lower hN x hx hret
  unfold originalPhysicalSlotReceiptExcess
  omega

/-- Both arithmetic tags arrive at an EXISTING finite-indexed
rank-two list position with the same true physical Q and [ell,p].
The same position passes the recursion's real ordinary full-prefix
Rosser gate. It is NOT a full/selected/inherited historical owner,
and the two tags do NOT supply two Fin positions. -/
theorem original_u4_retained_two_tags_one_actual_fin_position
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower) :
    ∃ slot : ℝ × ℕ × ℕ,
      slot = physicalRankTwoSlot N precision tau
        (chosenRankTwoKey N cap precision tau z0 lower
          (Sum.inl x : TaggedReceiver)) ∧
      ∃ i : Fin (actualPhysicalRankTwoList
        N cap z0 slot.1 lower).length,
        (actualPhysicalRankTwoList
          N cap z0 slot.1 lower)[i].selectedPrefix =
          [slot.2.2, slot.2.1] ∧
        actualFullPrefixGate lower slot.1
          ((actualPhysicalRankTwoList N cap z0 slot.1 lower)[i]) = true ∧
        2 ≤ (originalReceiptsAtPhysicalSlot
          N cap precision tau z0 lower slot).card := by
  let slot := physicalRankTwoSlot N precision tau
    (chosenRankTwoKey N cap precision tau z0 lower
      (Sum.inl x : TaggedReceiver))
  have hkey : chosenRankTwoKey N cap precision tau z0 lower
      (Sum.inl x : TaggedReceiver) ∈
      observedRankTwoKeys N cap precision tau z0 lower :=
    Finset.mem_image.mpr ⟨Sum.inl x, hret, rfl⟩
  have hs : slot ∈ observedPhysicalSlots
      N cap precision tau z0 lower :=
    Finset.mem_image.mpr ⟨
      chosenRankTwoKey N cap precision tau z0 lower
        (Sum.inl x : TaggedReceiver), hkey, rfl⟩
  obtain ⟨i, hi⟩ := observed_slot_has_actual_rank_two_position
    N cap precision tau z0 lower slot hs
  have hfull := actual_rank_two_full_prefix_passes
    N cap z0 slot.1 lower i
  have htwo := original_u4_retained_slot_card_ge_two
    N cap precision tau z0 lower hN x hx hret
  exact ⟨slot, rfl, i, hi, hfull, htwo⟩

/-- Pure finite sum-of-two-subset lemma used on the REAL retained
slot fibre. The rest of that fibre is not discarded. -/
private theorem signed_two_mem_erase
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (F : Finset α) (a b : α) (w : α → M)
    (ha : a ∈ F) (hb : b ∈ F) (hne : b ≠ a) :
    (∑ z ∈ F, w z) =
      w a + w b + ∑ z ∈ (F.erase a).erase b, w z := by
  have hb' : b ∈ F.erase a :=
    Finset.mem_erase.mpr ⟨hne, hb⟩
  calc
    _ = w a + ∑ z ∈ F.erase a, w z :=
      (Finset.add_sum_erase F w ha).symm
    _ = w a + (w b + ∑ z ∈ (F.erase a).erase b, w z) := by
      rw [Finset.add_sum_erase (F.erase a) w hb']
    _ = _ := by ac_rfl

/-- Exact arbitrary signed weights of both original U3/U4 tags
inside the SAME actual physical-slot fibre, followed by ALL other q
and tag receipts in that fibre. No equality of tag weights, history
mass, or first-excluded payment is assumed. -/
theorem original_u4_retained_slot_signed_two_tags_plus_other_q
    {M : Type*} [AddCommMonoid M]
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower)
    (w : TaggedReceiver → M) :
    let slot := physicalRankTwoSlot N precision tau
      (chosenRankTwoKey N cap precision tau z0 lower
        (Sum.inl x : TaggedReceiver))
    let F := originalReceiptsAtPhysicalSlot
      N cap precision tau z0 lower slot
    (∑ z ∈ F, w z) =
      w (Sum.inl x) + w (Sum.inr x) +
        ∑ z ∈ (F.erase (Sum.inl x)).erase (Sum.inr x), w z := by
  dsimp
  have htwo := original_u4_retained_two_tags_in_slot_fibre
    N cap precision tau z0 lower hN x hx hret
  apply signed_two_mem_erase
  · exact htwo.1
  · exact htwo.2
  · intro heq
    cases heq

end
end ImbalancedChen.Part5OriginalH430UpperRetainedFinFibre
