import ImbalancedChen.Part5OriginalH430UpperRetainedFinFibre
import ImbalancedChen.FirstExitAdmittedFrontierTuples

/-!
P5.6 / h34: uniqueness of the REAL rank-two prefix position at fixed Q.

Unlike the earlier packet, which established existence of one Fin occurrence
for a surviving original U4 double-tag quotient, this packet proves that
the actual rank-two first-exit frontier contains AT MOST ONE position with
the same ordered [ell,p] prefix, at the same physical Q. It uses the already
proved admitted-frontier tuple Nodup theorem and the actual prime carrier,
not a duplicate-erasing set substituted for the original recursive list.

Thus exactly one rank-two position is available for each observed physical
slot, before ANY post-frontier filter. Any later full/selected/inherited
filter can only erase this position, not duplicate it. One retained U4
quotient contributes at least two distinct original q/tag receipts at
that slot. The resulting NATURAL CARDINALITY shortfall is at least one,
even after an arbitrary post-frontier filter.

This does NOT prove the historical payment rule, signed weight deficit,
root weight, or actual upper H430 owner. Later deeper histories are not
claimed to have unique positions from this rank-two lemma.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430UpperRankTwoPrefixCapacity

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430PhysicalSlotListPositions
open Part5OriginalH430FixedQPositionFilterLedger
open Part5OriginalH430UpperRetainedFinFibre

/-- The TRUE rank-two recursive list has no repeated selected prime
prefix. This follows from the entire admitted-frontier tuple list, NOT
from an assumed Nodup property of the states or their original q tags. -/
theorem actual_rank_two_selected_prefixes_nodup
    (N cap : ℕ) (z0 Q : ℝ) (lower : Bool) :
    ((actualPhysicalRankTwoList N cap z0 Q lower).map
      (fun s => s.selectedPrefix)).Nodup := by
  apply List.Nodup.of_map (primeHistoryTuple 2)
  simpa only [actualPhysicalRankTwoList, List.map_map, Function.comp_def] using
    (firstExitRootFrontier_admitted_tuple_nodup 2
      (ordinaryRosserRetainedPolicy lower Q)
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      (roughPrimeUniverse N cap 0 z0)
      (roughPrimeUniverse_nodup N cap 0 z0))

/-- Two actual Fin indices at the same Q with the same selected prime
prefix are equal; this refers to original LIST positions, not values
after converting the frontier to a finite set. -/
theorem actual_rank_two_prefix_position_unique
    (N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    (i j : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length)
    (hpre : (actualPhysicalRankTwoList N cap z0 Q lower)[i].selectedPrefix =
      (actualPhysicalRankTwoList N cap z0 Q lower)[j].selectedPrefix) :
    i = j := by
  let L := actualPhysicalRankTwoList N cap z0 Q lower
  have hn : (L.map (fun s => s.selectedPrefix)).Nodup :=
    actual_rank_two_selected_prefixes_nodup N cap z0 Q lower
  have hi : i.1 < (L.map (fun s => s.selectedPrefix)).length := by
    simpa only [List.length_map] using i.isLt
  have hj : j.1 < (L.map (fun s => s.selectedPrefix)).length := by
    simpa only [List.length_map] using j.isLt
  have heq :
      (L.map (fun s => s.selectedPrefix))[i.1] =
        (L.map (fun s => s.selectedPrefix))[j.1] := by
    simpa only [List.getElem_map] using hpre
  have hij : i.1 = j.1 :=
    (hn.getElem_inj_iff (hi := hi) (hj := hj)).mp heq
  exact Fin.ext hij

/-- The genuine rank-two Fin positions whose literal selected prefix
is [ell,p]; every occurrence is counted, before owner or policy filters. -/
def actualRankTwoPrefixPositions (N cap : ℕ) (z0 Q : ℝ)
    (lower : Bool) (p ell : ℕ) :
    Finset (Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) :=
  Finset.univ.filter (fun i =>
    (actualPhysicalRankTwoList N cap z0 Q lower)[i].selectedPrefix = [ell, p])

/-- An OBSERVED actual physical (Q,p,ell) slot has precisely one
rank-two Fin occurrence with its selected prefix. Existence comes from
the original q/tag Rosser-retained source, uniqueness from the real
admitted first-exit recursion. -/
theorem observed_slot_rank_two_prefix_positions_singleton
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (slot : ℝ × ℕ × ℕ)
    (hs : slot ∈ observedPhysicalSlots N cap precision tau z0 lower) :
    actualRankTwoPrefixPositions N cap z0 slot.1 lower slot.2.1 slot.2.2 =
      {observedSlotRankTwoPosition N cap precision tau z0 lower slot hs} := by
  classical
  ext i
  simp only [actualRankTwoPrefixPositions, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hi
    apply actual_rank_two_prefix_position_unique N cap z0 slot.1 lower
    exact hi.trans
      (observed_slot_rank_two_position_prefix
        N cap precision tau z0 lower slot hs).symm
  · intro hi
    subst i
    exact observed_slot_rank_two_position_prefix
      N cap precision tau z0 lower slot hs

theorem observed_slot_rank_two_prefix_positions_card_one
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (slot : ℝ × ℕ × ℕ)
    (hs : slot ∈ observedPhysicalSlots N cap precision tau z0 lower) :
    (actualRankTwoPrefixPositions
      N cap z0 slot.1 lower slot.2.1 slot.2.2).card = 1 := by
  rw [observed_slot_rank_two_prefix_positions_singleton
    N cap precision tau z0 lower slot hs]
  simp

/-- Even an arbitrary subsequent BOOLEAN position filter cannot
create a second rank-two prefix occurrence. This states a necessary
capacity bound, NOT sufficiency of any manuscript owner filter. -/
theorem observed_slot_rank_two_kept_prefix_card_le_one
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (slot : ℝ × ℕ × ℕ)
    (hs : slot ∈ observedPhysicalSlots N cap precision tau z0 lower)
    (keep : FirstExitDepthState ℕ → Bool) :
    ((actualRankTwoPrefixPositions
        N cap z0 slot.1 lower slot.2.1 slot.2.2) ∩
      keptPositions N cap z0 slot.1 lower keep).card ≤ 1 := by
  have hsub :
      (actualRankTwoPrefixPositions
        N cap z0 slot.1 lower slot.2.1 slot.2.2 ∩
        keptPositions N cap z0 slot.1 lower keep) ⊆
      actualRankTwoPrefixPositions
        N cap z0 slot.1 lower slot.2.1 slot.2.2 :=
    Finset.inter_subset_left
  have hcard := Finset.card_le_card hsub
  rw [observed_slot_rank_two_prefix_positions_card_one
    N cap precision tau z0 lower slot hs] at hcard
  exact hcard

/-- A genuinely retained original U4 quotient supplies two different
arithmetic q/tag receipts but no more than ONE physical rank-two
[ell,p] position at their actual Q, even after an arbitrary position
filter. The difference is a count of receipts versus possible rank-two
positions, NOT a proved signed payment deficit or full-history claim. -/
theorem original_u4_retained_rank_two_capacity_gap_any_filter
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower)
    (keep : FirstExitDepthState ℕ → Bool) :
    let slot := physicalRankTwoSlot N precision tau
      (chosenRankTwoKey N cap precision tau z0 lower
        (Sum.inl x : TaggedReceiver))
    let F := originalReceiptsAtPhysicalSlot
      N cap precision tau z0 lower slot
    let P := actualRankTwoPrefixPositions
      N cap z0 slot.1 lower slot.2.1 slot.2.2 ∩
      keptPositions N cap z0 slot.1 lower keep
    2 ≤ F.card ∧ P.card ≤ 1 ∧ 1 ≤ F.card - P.card := by
  dsimp
  have hkey : chosenRankTwoKey N cap precision tau z0 lower
      (Sum.inl x : TaggedReceiver) ∈
      observedRankTwoKeys N cap precision tau z0 lower :=
    Finset.mem_image.mpr ⟨Sum.inl x, hret, rfl⟩
  have hs : physicalRankTwoSlot N precision tau
      (chosenRankTwoKey N cap precision tau z0 lower
        (Sum.inl x : TaggedReceiver)) ∈
      observedPhysicalSlots N cap precision tau z0 lower :=
    Finset.mem_image.mpr
      ⟨chosenRankTwoKey N cap precision tau z0 lower
        (Sum.inl x : TaggedReceiver), hkey, rfl⟩
  have htwo := original_u4_retained_slot_card_ge_two
    N cap precision tau z0 lower hN x hx hret
  have hone := observed_slot_rank_two_kept_prefix_card_le_one
    N cap precision tau z0 lower
      (physicalRankTwoSlot N precision tau
        (chosenRankTwoKey N cap precision tau z0 lower
          (Sum.inl x : TaggedReceiver))) hs keep
  omega

end
end ImbalancedChen.Part5OriginalH430UpperRankTwoPrefixCapacity
