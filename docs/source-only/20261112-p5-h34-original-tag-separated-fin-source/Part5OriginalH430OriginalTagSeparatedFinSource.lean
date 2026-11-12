import ImbalancedChen.Part5OriginalH430FourLaneFullTaggedFin

/-!
P5.6 / h34 — separate the ORIGINAL U3 and U4 tagged (p,q)
arithmetic contributions after their complete pushforward to the TRUE
physical-Q-dependent rank-two Fin positions.

Unlike a single representative per physical slot, this separation
preserves BOTH original tags on an overlapping prime-receiver pair and
every q in the slot fibre. Both branches carry their own four ORIGINAL
outside-source rejection terms. No claim identifies an observed Fin
position with a unique causal selected/inherited owner, nor pays the
root 7/2 norm or the remaining source debts.

Manuscript-internal finite identities only.
SOURCE_ONLY / CANDIDATE_UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430OriginalTagSeparatedFinSource

noncomputable section
open scoped Classical BigOperators

open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430PhysicalSlotListPositions
open Part5OriginalH430FixedQSlotInjection
open Part5OriginalH430FixedQPositionFilterLedger
open Part5OriginalH430FullTaggedActualFinPushforward
open Part5OriginalH430FourLaneFullTaggedFin
open Part5OriginalH430NegativeQuarterActualPositionDirection
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430SequentialTaggedReceiptDebt

/-- The original U3 arithmetic label, not a newly selected history owner. -/
def onlyU3 (w : TaggedReceiver → ℝ) : TaggedReceiver → ℝ
  | .inl x => w (.inl x)
  | .inr _ => 0

/-- The original U4 arithmetic label, kept distinct even on band overlap. -/
def onlyU4 (w : TaggedReceiver → ℝ) : TaggedReceiver → ℝ
  | .inl _ => 0
  | .inr x => w (.inr x)

/-- Every original tagged receiver has exactly one of the two labels.
This is a statement about the SUM tag, not about distinct physical slots. -/
theorem receipt_weight_split (w : TaggedReceiver → ℝ)
    (z : TaggedReceiver) :
    w z = onlyU3 w z + onlyU4 w z := by
  cases z <;> simp [onlyU3, onlyU4]

/-- The two real original prime-receiver bands are counted separately.
In particular an (p,q) in both bands appears twice, with different tags. -/
/-- Even a common original (p,q) is two DISTINCT tagged receipts.
The lemma deliberately asserts no equality between their physical Qs. -/
theorem overlap_retains_both_original_tags (N : ℕ) (x : TaggedPair)
    (h3 : x ∈ originalPairs N .U3)
    (h4 : x ∈ originalPairs N .U4) :
    (Sum.inl x : TaggedReceiver) ∈ originalTagged N ∧
    (Sum.inr x : TaggedReceiver) ∈ originalTagged N ∧
    (Sum.inl x : TaggedReceiver) ≠ Sum.inr x := by
  constructor
  · simp [originalTagged, h3]
  constructor
  · simp [originalTagged, h4]
  · simp

/-- Full original arithmetic weight at the TRUE Fin positions for
each of the original observed physical Q values, with no Q merging. -/
def allObservedFinWeight
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) : ℝ :=
  ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
    ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      actualAllTaggedAtFin N cap precision tau z0 lower w Q i

/-- At ONE actual Fin occurrence, all q/tag weights split without
quotienting receipts or assuming that different tagged roots have
different historical positions. -/
theorem actual_fin_weight_split
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) (Q : ℝ)
    (i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) :
    actualAllTaggedAtFin N cap precision tau z0 lower w Q i =
      actualAllTaggedAtFin N cap precision tau z0 lower (onlyU3 w) Q i +
      actualAllTaggedAtFin N cap precision tau z0 lower (onlyU4 w) Q i := by
  classical
  unfold actualAllTaggedAtFin
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hpos :
      fixedQSlotPositionMap N cap precision tau z0 lower Q s = i
  · simp only [hpos, ite_true]
    unfold actualSlotTaggedWeight
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    exact receipt_weight_split w z
  · simp [hpos]

/-- Separating U3/U4 commutes with summing all actual observed Q
fibres and all real rank-two Fin list occurrences. -/
theorem all_observed_fin_weight_split
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    allObservedFinWeight N cap precision tau z0 lower w =
      allObservedFinWeight N cap precision tau z0 lower (onlyU3 w) +
      allObservedFinWeight N cap precision tau z0 lower (onlyU4 w) := by
  classical
  unfold allObservedFinWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Q hQ
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact actual_fin_weight_split N cap precision tau z0 lower w Q i

/-- The actual original U3-tag projection of the source, not an
arbitrary selected mask, equals its full Fin source plus its FOUR literal
outside-source rejection lanes. Nothing here pays either term. -/
theorem original_U3_four_lane_fin_source
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (w : TaggedReceiver → ℝ) :
    (∑ z ∈ originalTagged N, onlyU3 w z) =
      allObservedFinWeight N cap precision tau z0 lower (onlyU3 w) +
      originalFourOutsidePositionLanes N cap precision tau z0 lower
        (onlyU3 w) := by
  have h := original_source_four_lanes_all_tagged_fin
    N cap precision tau z0 lower hzcap (onlyU3 w)
  simpa only [allObservedFinWeight] using h

/-- Same projected identity for original U4: overlapping original pairs are
not collapsed into U3, and all q-receipts keep their U4 tag. -/
theorem original_U4_four_lane_fin_source
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (w : TaggedReceiver → ℝ) :
    (∑ z ∈ originalTagged N, onlyU4 w z) =
      allObservedFinWeight N cap precision tau z0 lower (onlyU4 w) +
      originalFourOutsidePositionLanes N cap precision tau z0 lower
        (onlyU4 w) := by
  have h := original_source_four_lanes_all_tagged_fin
    N cap precision tau z0 lower hzcap (onlyU4 w)
  simpa only [allObservedFinWeight] using h

/-- The four actual outside-source lanes themselves split exactly by
the original U3/U4 tag. No cancellation, sign or smallness is used:
this follows from the three exact arithmetic source identities and
the Fin-position pushforward. -/
theorem original_four_lanes_split_by_tag
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (w : TaggedReceiver → ℝ) :
    originalFourOutsidePositionLanes N cap precision tau z0 lower w =
      originalFourOutsidePositionLanes N cap precision tau z0 lower (onlyU3 w) +
      originalFourOutsidePositionLanes N cap precision tau z0 lower (onlyU4 w) := by
  classical
  have hwhole := original_source_four_lanes_all_tagged_fin
    N cap precision tau z0 lower hzcap w
  have h3 := original_source_four_lanes_all_tagged_fin
    N cap precision tau z0 lower hzcap (onlyU3 w)
  have h4 := original_source_four_lanes_all_tagged_fin
    N cap precision tau z0 lower hzcap (onlyU4 w)
  change (∑ z ∈ originalTagged N, w z) =
    allObservedFinWeight N cap precision tau z0 lower w +
    originalFourOutsidePositionLanes N cap precision tau z0 lower w at hwhole
  change (∑ z ∈ originalTagged N, onlyU3 w z) =
    allObservedFinWeight N cap precision tau z0 lower (onlyU3 w) +
    originalFourOutsidePositionLanes N cap precision tau z0 lower (onlyU3 w) at h3
  change (∑ z ∈ originalTagged N, onlyU4 w z) =
    allObservedFinWeight N cap precision tau z0 lower (onlyU4 w) +
    originalFourOutsidePositionLanes N cap precision tau z0 lower (onlyU4 w) at h4
  have hsum :
      (∑ z ∈ originalTagged N, w z) =
        (∑ z ∈ originalTagged N, onlyU3 w z) +
        (∑ z ∈ originalTagged N, onlyU4 w z) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    exact receipt_weight_split w z
  have hfin := all_observed_fin_weight_split
    N cap precision tau z0 lower w
  linarith only [hwhole, h3, h4, hsum, hfin]

/-- Exact original Chen -1/4 term with BOTH original arithmetic tags
on the true Fin positions, and BOTH tags' real outside-source debts.
This is a signed SOURCE identity, not a paid history/7/2 inequality. -/
theorem original_negative_quarter_two_tag_fin_source
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) :
    originalU34SignedQuarter N =
      -(1 / 4 : ℝ) *
        ((allObservedFinWeight N cap precision tau z0 lower
            (onlyU3 (fun _ => (1 : ℝ))) +
          allObservedFinWeight N cap precision tau z0 lower
            (onlyU4 (fun _ => (1 : ℝ)))) +
         (originalFourOutsidePositionLanes N cap precision tau z0 lower
            (onlyU3 (fun _ => (1 : ℝ))) +
          originalFourOutsidePositionLanes N cap precision tau z0 lower
            (onlyU4 (fun _ => (1 : ℝ))))) := by
  have h := original_negative_quarter_four_lanes_all_tagged_fin
    N cap precision tau z0 lower hzcap
  change originalU34SignedQuarter N =
    -(1 / 4 : ℝ) *
      (allObservedFinWeight N cap precision tau z0 lower
          (fun _ => (1 : ℝ)) +
       originalFourOutsidePositionLanes N cap precision tau z0 lower
          (fun _ => (1 : ℝ))) at h
  rw [all_observed_fin_weight_split,
    original_four_lanes_split_by_tag N cap precision tau z0 lower
      hzcap (fun _ => (1 : ℝ))] at h
  exact h

end
end ImbalancedChen.Part5OriginalH430OriginalTagSeparatedFinSource
