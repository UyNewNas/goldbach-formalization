import ImbalancedChen.Part5OriginalH430FourLaneFullTaggedFin

/-!
P5.6 / h34: exact q/tag collision excess at TRUE fixed-Q bounded Fin
history positions, not at a made-up representative or root owner.

Every original retained q/tag receipt is counted with multiplicity. One
occupied physical Fin history position need not represent one arithmetic
receipt: the surplus is explicitly recorded rather than silently charged
against native-history mass. The four real outside-position rejection
lanes remain unpaid, as do all selected/inherited ownership conditions.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualFinTaggedCollisionExcess
noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430FixedQSlotInjection
open Part5OriginalH430SequentialTaggedReceiptDebt
open Part5OriginalH430FullTaggedActualFinPushforward
open Part5OriginalH430FourLaneFullTaggedFin

/-- The NUMBER of all ORIGINAL tagged q receipts at a genuine fixed-Q
rank-two Fin list position. Unlike its state mass, this is a natural
number and includes all different q and U3/U4 tags in each slot fibre. -/
def taggedMultiplicity (N cap precision : ℕ) (tau z0 : ℝ)
    (lower : Bool) (Q : ℝ)
    (i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) : ℕ :=
  ∑ s : SlotAtQ N cap precision tau z0 lower Q,
    if fixedQSlotPositionMap N cap precision tau z0 lower Q s = i
    then (originalReceiptsAtPhysicalSlot
      N cap precision tau z0 lower s.1).card
    else 0

/-- The exact link to the PREVIOUS true-Fin all-tagged pushforward with
unit q/tag arithmetic weights. It does not assert that history mass
itself equals this receipt multiplicity. -/
theorem tagged_multiplicity_cast
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) :
    (taggedMultiplicity N cap precision tau z0 lower Q i : ℝ) =
      actualAllTaggedAtFin N cap precision tau z0 lower
        (fun _ => (1 : ℝ)) Q i := by
  classical
  unfold taggedMultiplicity actualAllTaggedAtFin
  simp only [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : fixedQSlotPositionMap N cap precision tau z0 lower Q s = i
  · simp only [if_pos h]
    exact (actual_slot_unit_weight_is_receipt_count
      N cap precision tau z0 lower Q s).symm
  · simp [h]

/-- At one genuine Fin position, at most its FIRST arithmetic receipt
could be represented by a one-receipt-per-position owner. The exact
surplus is NOT thrown away; it is still an unpaid arithmetic source. -/
def extraTagged (N cap precision : ℕ) (tau z0 : ℝ)
    (lower : Bool) (Q : ℝ)
    (i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) : ℕ :=
  let m := taggedMultiplicity N cap precision tau z0 lower Q i
  m - (if 0 < m then 1 else 0)

/-- Exact per-position decomposition; this is integer arithmetic, not a
new hypothesis about the original selected-count owner. -/
theorem multiplicity_eq_occupied_plus_extra
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) :
    taggedMultiplicity N cap precision tau z0 lower Q i =
      (if 0 < taggedMultiplicity N cap precision tau z0 lower Q i
       then 1 else 0) +
      extraTagged N cap precision tau z0 lower Q i := by
  unfold extraTagged
  by_cases h : 0 < taggedMultiplicity N cap precision tau z0 lower Q i
  · simp only [if_pos h]
    omega
  · simp only [if_neg h]
    omega

/-- ONE fixed physical Q: exact tagged receipt total equals occupied
Fin-position count plus the amount exceeding one q/tag receipt per
occupied position. No injection of arithmetic receipts into events is
postulated. -/
theorem fixed_q_all_tagged_multiplicity_split
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ) :
    (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      taggedMultiplicity N cap precision tau z0 lower Q i) =
    (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      if 0 < taggedMultiplicity N cap precision tau z0 lower Q i
      then 1 else 0) +
    (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      extraTagged N cap precision tau z0 lower Q i) := by
  classical
  calc
    _ = ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
          ((if 0 < taggedMultiplicity N cap precision tau z0 lower Q i
             then 1 else 0) +
            extraTagged N cap precision tau z0 lower Q i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact multiplicity_eq_occupied_plus_extra
            N cap precision tau z0 lower Q i
    _ = _ := Finset.sum_add_distrib

/-- The same finite equality in real arithmetic, for subsequent
signed Chen -1/4 calculations without replacing q/tag cardinalities
by a native-history Theta weight. -/
theorem fixed_q_all_tagged_multiplicity_split_real
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ) :
    (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      (taggedMultiplicity N cap precision tau z0 lower Q i : ℝ)) =
    (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      ((if 0 < taggedMultiplicity N cap precision tau z0 lower Q i
        then 1 else 0 : ℕ) : ℝ)) +
    (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      (extraTagged N cap precision tau z0 lower Q i : ℝ)) := by
  have h := congrArg (fun n : ℕ => (n : ℝ))
    (fixed_q_all_tagged_multiplicity_split
      N cap precision tau z0 lower Q)
  simpa only [Nat.cast_sum, Nat.cast_add] using h

/-- The ORIGINAL retained U3/U4 q/tag receipt source, already mapped
to actual true-Q Fin positions, is the integral number of receipts.
No catalog-label quotient or replacement by occupied positions. -/
theorem retained_tagged_unit_source_real
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    (∑ z ∈ retainedReceipts N cap precision tau z0 lower, (1 : ℝ)) =
    ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
      ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
        (taggedMultiplicity N cap precision tau z0 lower Q i : ℝ) := by
  have h := retained_receipts_all_tagged_actual_fin
    N cap precision tau z0 lower (fun _ => (1 : ℝ))
  simpa only [← tagged_multiplicity_cast] using h

/-- ACTUAL original tagged retained source, at each TRUE physical Q,
equals number of occupied genuine rank-two Fin positions plus all
unpaid duplicate q/tag receipts. Cross-Q and U3/U4 sources are not
identified; the four original outside-position rejection lanes are
still additional count obligations. -/
theorem retained_original_occupied_plus_collision_excess
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    (∑ z ∈ retainedReceipts N cap precision tau z0 lower, (1 : ℝ)) =
    (∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
      ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
        ((if 0 < taggedMultiplicity N cap precision tau z0 lower Q i
          then 1 else 0 : ℕ) : ℝ)) +
    (∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
      ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
        (extraTagged N cap precision tau z0 lower Q i : ℝ)) := by
  rw [retained_tagged_unit_source_real]
  calc
    _ = ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
        ((∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
           ((if 0 < taggedMultiplicity N cap precision tau z0 lower Q i
             then 1 else 0 : ℕ) : ℝ)) +
          (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
           (extraTagged N cap precision tau z0 lower Q i : ℝ))) := by
          apply Finset.sum_congr rfl
          intro Q hQ
          exact fixed_q_all_tagged_multiplicity_split_real
            N cap precision tau z0 lower Q
    _ = _ := Finset.sum_add_distrib

end
end ImbalancedChen.Part5OriginalH430ActualFinTaggedCollisionExcess
