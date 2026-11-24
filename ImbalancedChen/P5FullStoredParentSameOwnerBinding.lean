import ImbalancedChen.P5SubdivisionStoredParentArchive
import ImbalancedChen.P5LicensedRawOwnerActualGain
import ImbalancedChen.P1HistoricalFifthTypedKeyPartition

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_CREDIT.
The independent72 checkpoint literal blocks retain all292633 source
positions and BOTH stored parent floors. Per-child fields are reconstructed
from that position's original raw row; the NPZ stores no child d/A/B array.
The old Jensen/Taylor branch is not proved by the child argument. Its
unpaid excess is explicit, and is subtracted exactly once.
-/
namespace ImbalancedChen.P5FullStoredParentSameOwnerBinding
open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness P1HistoricalFifthIndexedOwnerArchive
open P5OriginalChildIntegerWireBinding P5OldFifthExact64ChildTiling
open P5OriginalGenericWireFloorReceiver P5HistoricalMask56FullSourceChildren
open P5SubdivisionStoredParentTypes
open ImbalancedChen.Certificates.P2DirectedLogRounding

theorem archiveIndex_lt (i : ArchiveIndex) : i.val < 292633 := by
  simpa only [P1HistoricalFifthTypedArchiveShape.rows_toList_length] using i.isLt

/-- The complete source-index/child family has64 children per parent. -/
theorem full_source_child_card : Fintype.card (ArchiveIndex × ChildIndex) = 292633 * 64 := by
  rw [Fintype.card_prod, archiveIndex_card, childIndex_card]

/-- Positional lookup, with neither row-value deduplication nor key sort. -/
def storedAt (i : ArchiveIndex) : StoredParent :=
  P5SubdivisionStoredParentArchive.rows[i.val]'(by
    simpa only [P5SubdivisionStoredParentArchive.rows_size] using archiveIndex_lt i)

def childSumZ (i : ArchiveIndex) : ℤ :=
  ∑ c : ChildIndex, originalExactFloor (originalFields (archiveRow i) c)

/-- Only finite original integer field identities occur here. This CLOSED
decision source has NOT been executed or accepted by a compiler/checker.
In particular, the new field is max(old,complete64child), not old+child. -/
theorem proposed_all_stored_parent_replacements :
    ∀ i : ArchiveIndex,
      (storedAt i).newQ80 = max (storedAt i).oldQ80 (childSumZ i) := by
  decide

theorem stored_sourceIndex_exact (i : ArchiveIndex) :
    (storedAt i).sourceIndex = i.val := by
  exact P5SubdivisionStoredParentArchive.source_index_at
    ⟨i.val, by simpa only [P5SubdivisionStoredParentArchive.rows_size] using archiveIndex_lt i⟩

/-- This is an unpaid OLD-proof branch, not an owner-boundary cost and
not a proof of the saved parent Taylor/Jensen floor. -/
def oldBranchDefectZ (i : ArchiveIndex) : ℤ :=
  max 0 ((storedAt i).oldQ80 - childSumZ i)

theorem oldBranchDefect_nonneg (i : ArchiveIndex) : 0 ≤ oldBranchDefectZ i :=
  le_max_left _ _

theorem stored_new_minus_old_defect_eq_children (i : ArchiveIndex) :
    (storedAt i).newQ80 - oldBranchDefectZ i = childSumZ i := by
  rw [proposed_all_stored_parent_replacements i]
  unfold oldBranchDefectZ
  by_cases h : (storedAt i).oldQ80 ≤ childSumZ i
  · rw [max_eq_right h, max_eq_left (sub_nonpos.mpr h), sub_zero]
  · have hc : childSumZ i ≤ (storedAt i).oldQ80 := (lt_of_not_ge h).le
    rw [max_eq_left hc, max_eq_right (sub_nonneg.mpr hc)]
    omega

def storedNewQ (i : ArchiveIndex) : ℚ := (storedAt i).newQ80 / dyadicScale 80

def oldBranchDefectQ (i : ArchiveIndex) : ℚ := oldBranchDefectZ i / dyadicScale 80

theorem stored_minus_old_defect_eq_wire64 (i : ArchiveIndex) :
    storedNewQ i - oldBranchDefectQ i = indexedWireFloor64 i := by
  rw [storedNewQ, oldBranchDefectQ, ← sub_div]
  have heq : ((storedAt i).newQ80 : ℚ) - (oldBranchDefectZ i : ℚ) = (childSumZ i : ℚ) := by
    exact_mod_cast stored_new_minus_old_defect_eq_children i
  rw [heq]
  simp only [childSumZ, indexedWireFloor64, rowFloorQ, Int.cast_sum, Finset.sum_div]

/-- Actual lower endpoints, for every raw row, not only the two examples. -/
theorem original_lo_eq_actual (raw : FifthWireRow) (c : ChildIndex) (k : Fin 5) :
    (originalFields raw c).lo k = childLeftNumer raw c k := by
  have hw : wireWidth k = (width k : ℤ) := by fin_cases k <;> decide
  simp [originalFields, wireLo, childLeftNumer, hw]

/-- Full original parent fields and independent reconstructed child fields
are kept separate at the SAME source position; parent d/A/B are untouched. -/
theorem full_parent_and_child_field_binding (i : ArchiveIndex) (c : ChildIndex) :
    (storedAt i).sourceIndex = i.val ∧
    (originalFields (archiveRow i) c).n = 1600 ∧
    (originalFields (archiveRow i) c).mask = (archiveRow i).mask ∧
    (∀ k : Fin 5, (originalFields (archiveRow i) c).lo k =
      childLeftNumer (archiveRow i) c k) ∧
    (∀ k : Fin 5, (originalFields (archiveRow i) c).hi k =
      childRightNumer (archiveRow i) c k) ∧
    (originalFields (archiveRow i) c).d = originalD (archiveRow i) c ∧
    (originalFields (archiveRow i) c).A = (originalAB (archiveRow i) c).num ∧
    (originalFields (archiveRow i) c).B = (originalAB (archiveRow i) c).den := by
  exact ⟨stored_sourceIndex_exact i, rfl, rfl, original_lo_eq_actual (archiveRow i) c,
    original_hi_eq_actual (archiveRow i) c, rfl, rfl, rfl⟩

noncomputable section
open Set MeasureTheory
open scoped Classical
open P2OriginalFourthCapProducerInterface P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1FifthUnitBoxGainDecomposition P1FifthPositivePartActualOwner
open P5LicensedRawOwnerActualGain

/-- Distinct original source positions have disjoint actual owner pieces.
The independent full-source key proof, rather than deduplication, prevents
charging the same physical parent point twice in the indexed sum. -/
theorem distinct_source_rawOwnerDomains_disjoint
    (i k : ArchiveIndex) (hne : i ≠ k) (e : ℚ) (q : ℕ) (chi omega : ℝ)
    (j l : Label5 (refinedMesh q)) :
    Disjoint (rawOwnerDomain (archiveRow i) e chi (refinedMesh q) omega j)
      (rawOwnerDomain (archiveRow k) e chi (refinedMesh q) omega l) :=
  (P1HistoricalFifthTypedKeyPartition.indexed_raw_boxes_disjoint i k hne).mono
    inter_subset_left inter_subset_left

/-- Each actual licensed source parent contributes64 children exactly
once. Stored old/new and strict owner costs remain independent. -/
theorem stored_parent_minus_defects_le_same_actual_gain
    (i : ArchiveIndex) (hi : i ∈ mask56Indices) (e : ℚ) (he : 0 ≤ e)
    (q : ℕ) (chi omega : ℝ) (hw : 0 < omega) (hwr : omega < (19 / 96 : ℝ))
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry) :
    (storedNewQ i : ℝ) - (oldBranchDefectQ i : ℝ) -
        indexedActualReserve64 i e q chi omega ≤
      ∑ j ∈ licensedOwners i e q chi omega,
        rawOwnerIntegral (archiveRow i) e chi (refinedMesh q) omega j rows4 licensed4 := by
  have heq : (storedNewQ i : ℝ) - (oldBranchDefectQ i : ℝ) =
      (indexedWireFloor64 i : ℝ) := by
    exact_mod_cast stored_minus_old_defect_eq_wire64 i
  rw [heq]
  exact each_parent64_wire_minus_reserve_le_actual i hi e he q chi omega hw hwr
    rows4 licensed4 hgeometry

/-- The full licensed index sum preserves original multiplicities.
The right side is still the indexed same-owner sum, not an unproved
global common-policy fifth saving or a numerical total. -/
theorem full_licensed_stored_sum_minus_defects
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (hw : 0 < omega) (hwr : omega < (19 / 96 : ℝ))
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (hgeometry : ∀ r ∈ rows4, licensed4 r → r.Geometry) :
    (∑ i ∈ mask56Indices, (storedNewQ i : ℝ)) -
      (∑ i ∈ mask56Indices, (oldBranchDefectQ i : ℝ)) -
      (∑ i ∈ mask56Indices, indexedActualReserve64 i e q chi omega) ≤
      ∑ i ∈ mask56Indices, ∑ j ∈ licensedOwners i e q chi omega,
        rawOwnerIntegral (archiveRow i) e chi (refinedMesh q) omega j rows4 licensed4 := by
  have hs := Finset.sum_le_sum (fun i hi => stored_parent_minus_defects_le_same_actual_gain
    i hi e he q chi omega hw hwr rows4 licensed4 hgeometry)
  simpa only [Finset.sum_sub_distrib] using hs

end
end ImbalancedChen.P5FullStoredParentSameOwnerBinding
