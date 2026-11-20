import ImbalancedChen.Part5OriginalH430ActualFinTaggedCollisionExcess
import ImbalancedChen.Part5OriginalH430U4ActualFinDoubleTag

/-!
P5.6 / h34 — retained ORIGINAL U4 overlap forces a strictly positive
UNPAID q/tag collision excess at real, physical-Q-dependent rank-two
Fin history positions.

Unlike a general exact collision split, this proves a conditional
strict quantitative obstruction: ONE genuinely retained original U4
overlap already makes the original retained tagged arithmetic count
strictly greater than the number of occupied true Fin positions.
This is not the selected/inherited causal owner, native Euler mass,
a 7/2 root payment or a proof that such an overlap exists for every N.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430U4GlobalCollisionCapacityObstruction

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430FixedQSlotInjection
open Part5OriginalH430FullTaggedActualFinPushforward
open Part5OriginalH430U4ActualFinDoubleTag
open Part5OriginalH430ActualFinTaggedCollisionExcess

/-- A finite Nat sum is at least the value at any one member. We prove
this without introducing a hypothetical count-source owner. -/
private theorem one_le_actual_sum_of_witness
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ)
    (a : α) (ha : a ∈ s) (h : 1 ≤ f a) :
    1 ≤ ∑ x ∈ s, f x := by
  classical
  have hsum :
      (∑ x ∈ s, if x = a then (1 : ℕ) else 0) ≤
        ∑ x ∈ s, f x := by
    apply Finset.sum_le_sum
    intro x hx
    by_cases he : x = a
    · subst x
      simpa using h
    · simp [he]
  simpa [ha] using hsum

/-- A retained ORIGINAL U4-overlap pair has TWO distinct original
arithmetic tags at one true Fin occurrence. Hence at least one tag
there is in excess of one receipt per history position. -/
theorem original_retained_u4_forces_fin_extra
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower) :
    let slot := physicalRankTwoSlot N precision tau
      (chosenRankTwoKey N cap precision tau z0 lower
        (Sum.inl x : TaggedReceiver))
    ∃ i : Fin (actualPhysicalRankTwoList N cap z0 slot.1 lower).length,
      1 ≤ extraTagged N cap precision tau z0 lower slot.1 i := by
  let slot := physicalRankTwoSlot N precision tau
    (chosenRankTwoKey N cap precision tau z0 lower
      (Sum.inl x : TaggedReceiver))
  obtain ⟨i, hi⟩ :=
    original_u4_retained_one_actual_fin_two_plus_rest
      N cap precision tau z0 lower hN x hx hret
  refine ⟨i, ?_⟩
  have htwoReal :
      (2 : ℝ) ≤
        (taggedMultiplicity N cap precision tau z0 lower slot.1 i : ℝ) := by
    rw [tagged_multiplicity_cast N cap precision tau z0 lower slot.1 i, hi]
    positivity
  have htwo :
      2 ≤ taggedMultiplicity N cap precision tau z0 lower slot.1 i := by
    exact_mod_cast htwoReal
  have hpos :
      0 < taggedMultiplicity N cap precision tau z0 lower slot.1 i := by
    omega
  dsimp [extraTagged]
  simp only [if_pos hpos]
  omega

/-- This positive collision debt survives summation over ALL true
physical Q fibres; the Q of this retained U4 pair is not replaced by
a fixed representative. -/
theorem original_retained_u4_global_extra_ge_one
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower) :
    (1 : ℕ) ≤
      ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
        ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
          extraTagged N cap precision tau z0 lower Q i := by
  let key := chosenRankTwoKey N cap precision tau z0 lower
    (Sum.inl x : TaggedReceiver)
  let slot := physicalRankTwoSlot N precision tau key
  have hk : key ∈ observedRankTwoKeys
      N cap precision tau z0 lower :=
    Finset.mem_image.mpr ⟨Sum.inl x, hret, rfl⟩
  have hs : slot ∈ observedPhysicalSlots
      N cap precision tau z0 lower :=
    Finset.mem_image.mpr ⟨key, hk, rfl⟩
  have hQ : slot.1 ∈ observedReceiptQs
      N cap precision tau z0 lower :=
    Finset.mem_image.mpr ⟨slot, hs, rfl⟩
  obtain ⟨i, hi⟩ :=
    original_retained_u4_forces_fin_extra
      N cap precision tau z0 lower hN x hx hret
  have hlocal : (1 : ℕ) ≤
      ∑ j : Fin (actualPhysicalRankTwoList N cap z0 slot.1 lower).length,
        extraTagged N cap precision tau z0 lower slot.1 j := by
    exact one_le_actual_sum_of_witness Finset.univ
      (fun j => extraTagged N cap precision tau z0 lower slot.1 j)
      i (Finset.mem_univ i) hi
  exact one_le_actual_sum_of_witness
    (observedReceiptQs N cap precision tau z0 lower)
    (fun Q => ∑ j : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      extraTagged N cap precision tau z0 lower Q j)
    slot.1 hQ hlocal

/-- Strict source-capacity obstruction. If one ORIGINAL retained U4
overlap exists, counting occupied true Fin positions only ONCE loses
at least one of the original q/tag arithmetic receipts. It is invalid
to treat that one native history position as two paid owners. -/
theorem original_retained_u4_exceeds_occupied_fin_capacity
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower) :
    (∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
      ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
        ((if 0 < taggedMultiplicity N cap precision tau z0 lower Q i
          then 1 else 0 : ℕ) : ℝ)) + 1 ≤
      ∑ z ∈ retainedReceipts N cap precision tau z0 lower, (1 : ℝ) := by
  have hnat := original_retained_u4_global_extra_ge_one
    N cap precision tau z0 lower hN x hx hret
  have hreal : (1 : ℝ) ≤
      ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
        ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
          (extraTagged N cap precision tau z0 lower Q i : ℝ) := by
    exact_mod_cast hnat
  have hsource := retained_original_occupied_plus_collision_excess
    N cap precision tau z0 lower
  linarith only [hreal, hsource]

end
end ImbalancedChen.Part5OriginalH430U4GlobalCollisionCapacityObstruction
