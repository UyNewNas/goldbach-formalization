import ImbalancedChen.Part5OriginalH430DistinctU4FinReceiptDebt
import ImbalancedChen.Part5OriginalH430OriginalTagSeparatedFinSource

/-!
P5.6/h34: the COMPLETE original U3/U4 count at true rank-two Fin
positions, partitioned into (i) two tags on each DISTINCT U4-overlap
slot; (ii) every further q/tag receipt at that slot; (iii) ALL other
Fin-position receipts; (iv) the FOUR actual outside-source rejections.

The last two portions are not thrown away. This is a source identity,
NOT a selected/inherited causal-owner or Euler/root-7/2 payment theorem.
Frozen manuscript/constants unchanged. SOURCE_ONLY / UNCOMPILED.
-/
namespace ImbalancedChen.Part5OriginalH430GlobalU4OverlapRemainder
noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430FixedQSlotInjection
open Part5OriginalH430FullTaggedActualFinPushforward
open Part5OriginalH430SequentialTaggedReceiptDebt
open Part5OriginalH430FourLaneFullTaggedFin
open Part5OriginalH430OriginalTagSeparatedFinSource
open Part5OriginalH430DistinctU4FinReceiptDebt

/-- ALL arithmetic receipts outside the image of distinct U4-overlap
slots, measured at the actual Fin occurrences of this physical Q. -/
def otherFinUnitReceiptsAtQ
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (Q : ℝ) : ℝ :=
  ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
    if i ∈ u4OverlapFinAtQ N cap precision tau z0 lower Q
    then 0
    else actualAllTaggedAtFin N cap precision tau z0 lower
      (fun _ => (1 : ℝ)) Q i

/-- Nonnegativity of a complete UNIT arithmetic receipt fibre. -/
theorem actual_all_tagged_unit_nonneg
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (Q : ℝ)
    (i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) :
    0 ≤ actualAllTaggedAtFin N cap precision tau z0 lower
      (fun _ => (1 : ℝ)) Q i := by
  classical
  unfold actualAllTaggedAtFin
  apply Finset.sum_nonneg
  intro s hs
  by_cases h :
      fixedQSlotPositionMap N cap precision tau z0 lower Q s = i
  · simp only [h, ite_true]
    unfold actualSlotTaggedWeight
    positivity
  · simp [h]

/-- Other positions' unit receipt mass is arithmetic, not Euler, mass. -/
theorem other_fin_unit_receipts_nonneg
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (Q : ℝ) :
    0 ≤ otherFinUnitReceiptsAtQ N cap precision tau z0 lower Q := by
  classical
  unfold otherFinUnitReceiptsAtQ
  apply Finset.sum_nonneg
  intro i hi
  by_cases h : i ∈ u4OverlapFinAtQ
      N cap precision tau z0 lower Q
  · simp [h]
  · simp only [h, ite_false]
    exact actual_all_tagged_unit_nonneg
      N cap precision tau z0 lower Q i

/-- The U4-overlap image and its complement exactly partition all
real rank-two Fin occurrences without identifying q/tag with owner. -/
theorem actual_fin_unit_overlap_partition
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (Q : ℝ) :
    (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      actualAllTaggedAtFin N cap precision tau z0 lower
        (fun _ => (1 : ℝ)) Q i) =
    (∑ i ∈ u4OverlapFinAtQ N cap precision tau z0 lower Q,
      actualAllTaggedAtFin N cap precision tau z0 lower
        (fun _ => (1 : ℝ)) Q i) +
    otherFinUnitReceiptsAtQ N cap precision tau z0 lower Q := by
  classical
  let S : Finset (Fin (actualPhysicalRankTwoList
    N cap z0 Q lower).length) :=
    u4OverlapFinAtQ N cap precision tau z0 lower Q
  let f : Fin (actualPhysicalRankTwoList
    N cap z0 Q lower).length → ℝ :=
    fun i => actualAllTaggedAtFin N cap precision tau z0 lower
      (fun _ => (1 : ℝ)) Q i
  have hfilter : (Finset.univ.filter (fun i => i ∈ S)) = S := by
    ext i
    simp
  have hselected :
      (∑ i : Fin (actualPhysicalRankTwoList
        N cap z0 Q lower).length, if i ∈ S then f i else 0) =
      ∑ i ∈ S, f i := by
    calc
      _ = ∑ i ∈ (Finset.univ.filter (fun i => i ∈ S)), f i := by
        simp only [Finset.sum_filter]
      _ = ∑ i ∈ S, f i := by rw [hfilter]
  have hsum :
      (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
        f i) =
      (∑ i ∈ S, f i) +
      ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
        if i ∈ S then 0 else f i := by
    calc
      _ =
        (∑ i : Fin (actualPhysicalRankTwoList
          N cap z0 Q lower).length, if i ∈ S then f i else 0) +
        (∑ i : Fin (actualPhysicalRankTwoList
          N cap z0 Q lower).length, if i ∈ S then 0 else f i) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          by_cases h : i ∈ S <;> simp [h]
      _ = _ := by rw [hselected]
  simpa [S, f, otherFinUnitReceiptsAtQ] using hsum

/-- The complete single-Q Fin count equals double tags plus excess
q/tag multiplicity on these same slots plus every OTHER receipt. -/
theorem actual_fin_two_tags_excess_and_rest
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (Q : ℝ) :
    (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      actualAllTaggedAtFin N cap precision tau z0 lower
        (fun _ => (1 : ℝ)) Q i) =
    (2 : ℝ) *
      ((u4OverlapSlotsAtQ N cap precision tau z0 lower Q).card : ℝ) +
    (∑ s ∈ u4OverlapSlotsAtQ N cap precision tau z0 lower Q,
      (((originalReceiptsAtPhysicalSlot
        N cap precision tau z0 lower s.1).card - 2 : ℕ) : ℝ)) +
    otherFinUnitReceiptsAtQ N cap precision tau z0 lower Q := by
  rw [actual_fin_unit_overlap_partition
    N cap precision tau z0 lower Q]
  rw [u4_overlap_fin_two_plus_extra_exact
    N cap precision tau z0 lower hN Q]
  ring

/-- Sum separately at every ACTUAL Q. Nothing merges Q fibres. -/
theorem all_observed_fin_two_tags_excess_and_rest
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) :
    allObservedFinWeight N cap precision tau z0 lower
      (fun _ => (1 : ℝ)) =
    ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
      ((2 : ℝ) *
          ((u4OverlapSlotsAtQ N cap precision tau z0 lower Q).card : ℝ) +
        (∑ s ∈ u4OverlapSlotsAtQ N cap precision tau z0 lower Q,
          (((originalReceiptsAtPhysicalSlot
            N cap precision tau z0 lower s.1).card - 2 : ℕ) : ℝ)) +
        otherFinUnitReceiptsAtQ N cap precision tau z0 lower Q) := by
  unfold allObservedFinWeight
  apply Finset.sum_congr rfl
  intro Q hQ
  exact actual_fin_two_tags_excess_and_rest
    N cap precision tau z0 lower hN Q

/-- FULL original U3+U4 count, including all other Fin positions and
all four outside-source rejection terms; nothing is claimed paid. -/
theorem original_u34_count_full_overlap_balance
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (hzcap : z0 ≤ (cap : ℝ)) :
    currentChenUpsilon3 N + currentChenUpsilon4 N =
    (∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
      ((2 : ℝ) *
          ((u4OverlapSlotsAtQ N cap precision tau z0 lower Q).card : ℝ) +
        (∑ s ∈ u4OverlapSlotsAtQ N cap precision tau z0 lower Q,
          (((originalReceiptsAtPhysicalSlot
            N cap precision tau z0 lower s.1).card - 2 : ℕ) : ℝ)) +
        otherFinUnitReceiptsAtQ N cap precision tau z0 lower Q)) +
    originalFourOutsidePositionLanes N cap precision tau z0 lower
      (fun _ => (1 : ℝ)) := by
  have h := original_source_four_lanes_all_tagged_fin
    N cap precision tau z0 lower hzcap (fun _ => (1 : ℝ))
  have hcount :
      (∑ z ∈ originalTagged N, (1 : ℝ)) =
        currentChenUpsilon3 N + currentChenUpsilon4 N := by
    calc
      _ = ((originalTagged N).card : ℝ) := by simp
      _ = _ := (original_U34_eq_tagged_card N).symm
  rw [hcount] at h
  change currentChenUpsilon3 N + currentChenUpsilon4 N =
    allObservedFinWeight N cap precision tau z0 lower
      (fun _ => (1 : ℝ)) +
    originalFourOutsidePositionLanes N cap precision tau z0 lower
      (fun _ => (1 : ℝ)) at h
  rw [all_observed_fin_two_tags_excess_and_rest
    N cap precision tau z0 lower hN] at h
  exact h

/-- The Chen -1/4 term with all four disjoint arithmetic liabilities.
It is NOT a signed Euler or root-7/2 historical payment inequality. -/
theorem original_negative_quarter_full_overlap_balance
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (hzcap : z0 ≤ (cap : ℝ)) :
    originalU34SignedQuarter N =
    -(1 / 4 : ℝ) *
      ((∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
        ((2 : ℝ) *
            ((u4OverlapSlotsAtQ N cap precision tau z0 lower Q).card : ℝ) +
          (∑ s ∈ u4OverlapSlotsAtQ N cap precision tau z0 lower Q,
            (((originalReceiptsAtPhysicalSlot
              N cap precision tau z0 lower s.1).card - 2 : ℕ) : ℝ)) +
          otherFinUnitReceiptsAtQ N cap precision tau z0 lower Q)) +
      originalFourOutsidePositionLanes N cap precision tau z0 lower
        (fun _ => (1 : ℝ))) := by
  rw [originalU34SignedQuarter,
    original_u34_count_full_overlap_balance
      N cap precision tau z0 lower hN hzcap]
  ring

end
end ImbalancedChen.Part5OriginalH430GlobalU4OverlapRemainder
