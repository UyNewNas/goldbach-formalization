import ImbalancedChen.Part5OriginalH430U4GlobalCollisionCapacityObstruction
import ImbalancedChen.Part5OriginalH430FourLaneFullTaggedFin

/-!
P5.6 / h34 — exact ORIGINAL Chen -1/4 debit after separating the
TRUE-Q rank-two Fin position capacity, the literal q/tag collision
excess, and all FOUR actual outside-position rejection lanes.

This composes the previous source identities with the actual signed
Chen contribution. In particular a retained original U4 overlap
forces at least -1/4 of additional original arithmetic debit BEYOND
one unit per occupied true Fin position, regardless of the four
nonnegative outside-source rejections. This is a NECESSARY payment
obstruction, not a native-history mass bound or a selected-count owner.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430SignedOriginalFinCapacityGap
noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430FixedQSlotInjection
open Part5OriginalH430SequentialTaggedReceiptDebt
open Part5OriginalH430FullTaggedActualFinPushforward
open Part5OriginalH430ActualFinTaggedCollisionExcess
open Part5OriginalH430FourLaneFullTaggedFin
open Part5OriginalH430U4GlobalCollisionCapacityObstruction
open Part5OriginalH430NegativeQuarterActualPositionDirection

/-- ONE arithmetic unit per occupied TRUE rank-two Fin position at
its OWN physical Q, not a licence for full/selected/inherited ownership. -/
def occupiedFinUnits
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) : ℝ :=
  ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
    ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      ((if 0 < taggedMultiplicity N cap precision tau z0 lower Q i
        then 1 else 0 : ℕ) : ℝ)

/-- Every ORIGINAL U3/U4 q/tag receipt beyond the FIRST receipt at a
true Fin occurrence remains a separate nonnegative arithmetic debit. -/
def excessFinUnits
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) : ℝ :=
  ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
    ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      (extraTagged N cap precision tau z0 lower Q i : ℝ)

/-- The FOUR real original rejection lanes, with unit receipt weight.
They are NOT disguised as q/tag collisions or history mass. -/
def outsideRejectedUnits
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) : ℝ :=
  originalFourOutsidePositionLanes N cap precision tau z0 lower
    (fun _ => (1 : ℝ))

private theorem unit_ite_sum_nonneg {α : Type*}
    (s : Finset α) (p : α → Prop) :
    0 ≤ ∑ x ∈ s, if p x then (1 : ℝ) else 0 := by
  classical
  apply Finset.sum_nonneg
  intro x hx
  split_ifs <;> norm_num

/-- Each of the four actual discarded-receipt lanes has unit weights
and hence cannot cancel a negative Chen debit. -/
theorem outside_rejected_units_nonneg
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    0 ≤ outsideRejectedUnits N cap precision tau z0 lower := by
  have hsecond := unit_ite_sum_nonneg
    ((originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower))
    (fun z => hasPostRootPrimeFactor z ∧
      ¬ hasRetainedOriginalSecond N cap precision tau z0 lower z)
  have hno := unit_ite_sum_nonneg
    ((originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower))
    (fun z => ¬ hasPostRootPrimeFactor z)
  have hcut : 0 ≤
      ∑ z ∈ rootCutoffBlocked (originalTagged N) z0, (1 : ℝ) := by
    positivity
  have hpolicy : 0 ≤
      ∑ z ∈ physicalPolicyBlocked N precision tau z0 lower,
        (1 : ℝ) := by
    positivity
  unfold outsideRejectedUnits originalFourOutsidePositionLanes
  linarith only [hsecond, hno, hcut, hpolicy]

/-- Reuse the complete ORIGINAL tagged source pushforward at its
actual Q. Never identify the arithmetic q/tag fibre with Euler mass. -/
theorem tagged_unit_actual_fin_occupied_plus_excess
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    (∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
      ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
        actualAllTaggedAtFin N cap precision tau z0 lower
          (fun _ => (1 : ℝ)) Q i) =
      occupiedFinUnits N cap precision tau z0 lower +
      excessFinUnits N cap precision tau z0 lower := by
  calc
    _ = ∑ z ∈ retainedReceipts N cap precision tau z0 lower,
          (1 : ℝ) :=
      (retained_receipts_all_tagged_actual_fin
        N cap precision tau z0 lower (fun _ => (1 : ℝ))).symm
    _ = _ := retained_original_occupied_plus_collision_excess
      N cap precision tau z0 lower

/-- The COMPLETE original U3/U4 arithmetic source is exactly its
one-per-occupied-position part, all uncollapsed q/tag surplus, and
FOUR still-unpaid original rejection lanes. -/
theorem original_full_unit_source_three_way
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) :
    (∑ z ∈ originalTagged N, (1 : ℝ)) =
      (occupiedFinUnits N cap precision tau z0 lower +
        excessFinUnits N cap precision tau z0 lower) +
      outsideRejectedUnits N cap precision tau z0 lower := by
  calc
    _ = (∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
          ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
            actualAllTaggedAtFin N cap precision tau z0 lower
              (fun _ => (1 : ℝ)) Q i) +
          originalFourOutsidePositionLanes
            N cap precision tau z0 lower (fun _ => (1 : ℝ)) :=
      original_source_four_lanes_all_tagged_fin
        N cap precision tau z0 lower hzcap (fun _ => (1 : ℝ))
    _ = _ := by
      rw [tagged_unit_actual_fin_occupied_plus_excess]
      rfl

/-- Exact Chen sign and normalization, not a purported root-7/2
history payment. In particular neither collision nor rejection
receipts are permitted to disappear through the negative sign. -/
theorem original_signed_quarter_three_way
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) :
    originalU34SignedQuarter N =
      -(1 / 4 : ℝ) *
        ((occupiedFinUnits N cap precision tau z0 lower +
          excessFinUnits N cap precision tau z0 lower) +
          outsideRejectedUnits N cap precision tau z0 lower) := by
  calc
    _ = -(1 / 4 : ℝ) *
        ((∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
          ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
            actualAllTaggedAtFin N cap precision tau z0 lower
              (fun _ => (1 : ℝ)) Q i) +
          originalFourOutsidePositionLanes
            N cap precision tau z0 lower (fun _ => (1 : ℝ))) :=
      original_negative_quarter_four_lanes_all_tagged_fin
        N cap precision tau z0 lower hzcap
    _ = _ := by
      rw [tagged_unit_actual_fin_occupied_plus_excess]
      rfl

/-- The signed arithmetic payment deficit beyond giving EACH occupied
Fin position one unit is EXACTLY -1/4 times q/tag excess PLUS the
four outside-position rejections. No new error term or assumed input. -/
theorem original_signed_capacity_deficit_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) :
    originalU34SignedQuarter N +
        (1 / 4 : ℝ) * occupiedFinUnits N cap precision tau z0 lower =
      -(1 / 4 : ℝ) *
        (excessFinUnits N cap precision tau z0 lower +
          outsideRejectedUnits N cap precision tau z0 lower) := by
  rw [original_signed_quarter_three_way N cap precision tau z0 lower hzcap]
  ring

/-- A genuine retained original U4 overlap forces a positive q/tag
excess in the global TRUE-Q sum, expressed as a real arithmetic debit. -/
theorem original_retained_u4_real_excess_ge_one
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower) :
    (1 : ℝ) ≤ excessFinUnits N cap precision tau z0 lower := by
  unfold excessFinUnits
  exact_mod_cast original_retained_u4_global_extra_ge_one
    N cap precision tau z0 lower hN x hx hret

/-- Genuine ORIGINAL U4 overlap forces at least one full arithmetic
q/tag receipt BEYOND one-per-occupied-Fin capacity. The four original
outside rejection lanes only increase the strict deficit. -/
theorem original_u4_full_count_exceeds_occupied
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (hN : 2 ≤ N)
    (x : TaggedPair) (hx : x ∈ originalPairs N .U4)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower) :
    occupiedFinUnits N cap precision tau z0 lower + 1 ≤
      ∑ z ∈ originalTagged N, (1 : ℝ) := by
  have hex := original_retained_u4_real_excess_ge_one
    N cap precision tau z0 lower hN x hx hret
  have hout := outside_rejected_units_nonneg
    N cap precision tau z0 lower
  rw [original_full_unit_source_three_way
    N cap precision tau z0 lower hzcap]
  linarith only [hex, hout]

/-- The exact extra Chen DEBIT, with its original negative 1/4 sign,
is at least 1/4 in magnitude for each genuine retained U4 witness
(here only existence of ONE witness is assumed, not proven for all N).
This is not a completed causal owner/capacity inequality. -/
theorem original_u4_signed_additional_quarter_debit
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (hN : 2 ≤ N)
    (x : TaggedPair) (hx : x ∈ originalPairs N .U4)
    (hret : (Sum.inl x : TaggedReceiver) ∈
      retainedReceipts N cap precision tau z0 lower) :
    originalU34SignedQuarter N +
      (1 / 4 : ℝ) * occupiedFinUnits N cap precision tau z0 lower ≤
      -(1 / 4 : ℝ) := by
  have hex := original_retained_u4_real_excess_ge_one
    N cap precision tau z0 lower hN x hx hret
  have hout := outside_rejected_units_nonneg
    N cap precision tau z0 lower
  rw [original_signed_capacity_deficit_exact
    N cap precision tau z0 lower hzcap]
  linarith only [hex, hout]

end
end ImbalancedChen.Part5OriginalH430SignedOriginalFinCapacityGap
