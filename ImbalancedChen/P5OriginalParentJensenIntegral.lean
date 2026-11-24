import ImbalancedChen.P5OriginalParentBoxJensen
import ImbalancedChen.P5OriginalParentJensenArchiveGeometry
import ImbalancedChen.P5OriginalParentSameReserveTransport

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Every original source index supplies its OWN parent vertices, frozen old
planes and original parent A/B.  R04's old one-term/1/3-tail Q80 floor is
connected to that original parent's actual positive integral, then to its
actual fourth ancestor and licensed fifth owners.  Only the ALREADY USED
indexedActualReserve64 is subtracted. No hFloor, assumed Jensen bound,
new reserve, Taylor claim or saved-old-field equality occurs.
-/
namespace ImbalancedChen.P5OriginalParentJensenIntegral
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalFifthRawBoxSelectorEquivalence
open P1OriginalFifthGrid400RefinedFullBoxCover P1FifthUnitBoxGainDecomposition
open P1FifthUnitBoxLiteralGainLower P1LiteralVariableFifthCompactSupplier
open P5OldFifthFrozenUpperSurrogate P5OldFifthFrozenGapConcavity
open P5OldFifthFiveCoordinateTree P5OldFifthChildGapIntegral P5OldFifthPointwiseQ
open P5NamedFifthPayloadSemantics P5OriginalParentJensenRawFields
open P5OriginalParentJensenArchiveScalars P5OriginalParentJensenGeometry
open P5OriginalParentJensenArchiveGeometry P5OriginalParentBoxJensen
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthTypedBaseGeometry
open P1OriginalFifthActualB13IntegralError P1OriginalFifthAdoptedOwnerBank
open P5HistoricalActualReserve64Budget P5OriginalFourthFifthSourceInputs
open P5OriginalParentSameReserveTransport

abbrev Point := Fin 5 → ℝ
def parentLeft (raw : FifthWireRow) : Point := fun k => (raw.lower k : ℝ)
def parentRight (raw : FifthWireRow) : Point := fun k => (raw.upper k : ℝ)

theorem parent_box_eq_original (raw : FifthWireRow) :
    box (parentLeft raw) (parentRight raw) = raw.originalBox := by
  ext t
  simp [box, logPrimeBox, FifthWireRow.originalBox, parentLeft, parentRight]

theorem parent_span_pos (i : ArchiveIndex) (k : Fin 5) :
    parentLeft (archiveRow i) k < parentRight (archiveRow i) k := by
  have hw : parentRight (archiveRow i) k - parentLeft (archiveRow i) k = 1 / 400 := by
    simp only [parentLeft, parentRight, FifthWireRow.lower, FifthWireRow.upper,
      archiveRow_grid]
    push_cast
    ring
  linarith

/-- Exact original parent normalization: volume times reciprocal endpoint
weight = 4*n/(prod_i(lo_i+1)*(lo_5+1)), with the ORIGINAL n=400.
The producer's 32-fold coordinate/grid rescaling has already been
preserved by R04; it is not a subdivision 1600 prefactor. -/
theorem parent_volume_mul_prefactor (i : ArchiveIndex) :
    boxVolume (parentLeft (archiveRow i)) (parentRight (archiveRow i)) *
        prefactor (parentRight (archiveRow i)) =
      (parentPrefactorQ (archiveRow i) : ℝ) := by
  have hH : ∀ k : Fin 5, ((archiveRow i).lo k : ℝ) + 1 ≠ 0 := by
    intro k
    have hk := (archiveRow_baseGeometry i).2.2.1 k
    have hp : (1 : ℝ) ≤ ((archiveRow i).lo k : ℝ) := by exact_mod_cast hk
    linarith
  simp only [boxVolume, prefactor, parentLeft, parentRight, parentPrefactorQ,
    FifthWireRow.lower, FifthWireRow.upper, archiveRow_grid, Fin.prod_univ_succ]
  push_cast
  field_simp [hH 0, hH 1, hH 2, hH 3, hH 4]
  <;> ring

/-- The actual whole-parent Jensen certificate at every one of the292633
original positions.  All geometry and scalar inputs are supplied by S03
and R04's closed original-row sources, not by a caller licence. -/
theorem original_parent_Jensen_floor_le_whole (i : ArchiveIndex) :
    (originalParentJensenFloorQ (archiveRow i) : ℝ) ≤
      ∫ t in (archiveRow i).originalBox,
        frozenUpperPositiveKernel (sourcePicks (archiveRow i)) (archiveRow i) t := by
  obtain ⟨_hB, _hd, hb, hb4, he0, he, _hp, _hn, _hdd, _hden, _hwire, _hfloor⟩ :=
    archiveRow_original_parent_scalars i
  have hbR : (2 : ℝ) < (parentBQ (archiveRow i) : ℝ) := by exact_mod_cast hb
  have hb4R : (parentBQ (archiveRow i) : ℝ) ≤ 4 := by exact_mod_cast hb4
  have heR : (parentEQ (archiveRow i) : ℝ) ∈
      Icc (0 : ℝ) ((parentBQ (archiveRow i) : ℝ) - 2) := by
    constructor
    · exact_mod_cast he0
    · exact_mod_cast he
  have hnew : ∀ t ∈ Icc (parentLeft (archiveRow i)) (parentRight (archiveRow i)),
      residual (rawCandidate 0 (archiveRow i) t) t ≤ (parentBQ (archiveRow i) : ℝ) := by
    intro t ht
    apply archiveRow_parent_new_ratio i t
    intro k
    exact ⟨ht.1 k, ht.2 k⟩
  have heq : (parentEQ (archiveRow i) : ℝ) =
      ((∑ w : Word, frozenGap (sourcePicks (archiveRow i)) (archiveRow i)
        (vertex (parentLeft (archiveRow i)) (parentRight (archiveRow i)) (wordChoice w))) / 32) /
          parentRight (archiveRow i) 4 := by
    simpa only [vertex, parentLeft, parentRight, parentVertex] using archiveRow_parentEQ_eq i
  have hJ := integral_frozenKernel_ge_Jensen
    (sourcePicks (archiveRow i)) (archiveRow i)
    (parentLeft (archiveRow i)) (parentRight (archiveRow i))
    (parent_span_pos i) (archiveRow_parent_lower_pos i) hbR hb4R hnew
    (parentEQ (archiveRow i) : ℝ) heR heq
  rw [parent_box_eq_original, parent_volume_mul_prefactor] at hJ
  exact (each_original_parent_Jensen_floor_le_Q i).trans hJ

/-- Original positive integral, independently defined before the stored
floor.  Frozen old-plane domination is only one-sided; no equality with
the actual dynamic ancestor or signed-kernel positivity is assumed. -/
theorem original_parent_Jensen_floor_le_parentIntegral (i : ArchiveIndex) :
    (originalParentJensenFloorQ (archiveRow i) : ℝ) ≤ parentIntegral (archiveRow i) := by
  have hleft := archiveRow_parent_lower_pos i
  have hF : IntegrableOn
      (frozenUpperPositiveKernel (sourcePicks (archiveRow i)) (archiveRow i))
      (archiveRow i).originalBox := by
    rw [← parent_box_eq_original]
    exact integrableOn_frozenKernel _ _ _ _ hleft
  have hg := archiveRow_baseGeometry i
  have hP := positiveKernel_integrableOn_of_subset (archiveRow i) 0
    (fixedParent (archiveRow i))
    (fixedParent_subset_positiveCube _ hg.1 hg.2.2.1)
  rw [archive_fixedParent_eq_raw] at hP
  have hm := setIntegral_mono_on hF hP (measurableSet_originalBox (archiveRow i))
    (fun t ht => frozenUpperPositiveKernel_le_literalPositiveRawKernel
      (sourcePicks (archiveRow i)) (archiveRow i) t
        (fun k => (hleft k).trans_le (ht k).1))
  change (∫ t in (archiveRow i).originalBox,
      frozenUpperPositiveKernel (sourcePicks (archiveRow i)) (archiveRow i) t) ≤
    ∫ t in (archiveRow i).originalBox, positiveKernel (archiveRow i) 0 t at hm
  unfold parentIntegral
  rw [archive_fixedParent_eq_raw]
  exact (original_parent_Jensen_floor_le_whole i).trans hm

/-- The ACTUAL original Jensen floor, for every original source, is now
attached to the SAME original fourth ancestor and the SAME licensed owner
sum.  The original reserve64 is charged once; its existing R05 schedule
can therefore be reused alongside the complete64/Taylor alternatives. -/
theorem each_original_parent_Jensen_sub_reserve
    (i : ArchiveIndex) (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (hw : 0 < omega) (hwr : omega < (19 / 96 : ℝ)) :
    (originalParentJensenFloorQ (archiveRow i) : ℝ) -
        indexedActualReserve64 i e q chi omega ≤
      ∑ j ∈ licensedOwners i e q chi omega,
        rawOwnerIntegral (archiveRow i) e chi (refinedMesh q) omega j
          originalRows4 originalAdmission4 :=
  (sub_le_sub_right (original_parent_Jensen_floor_le_parentIntegral i) _).trans
    (original_parentIntegral_sub_reserve_le_actual_owner_sum i e he q chi omega hw hwr)

/-- Full original source-index sum, with no mask filter, new floor licence,
oldBranchDefect subtraction or duplicate reserve. This is still the
Jensen alternative, not the stored maximum of Jensen and Taylor. -/
theorem full_original_Jensen_floor_sub_reserve
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (hw : 0 < omega) (hwr : omega < (19 / 96 : ℝ)) :
    (∑ i : ArchiveIndex, (originalParentJensenFloorQ (archiveRow i) : ℝ)) -
        (∑ i : ArchiveIndex, indexedActualReserve64 i e q chi omega) ≤
      P5OriginalFifthArchiveActualMean.archiveFifthIntegral
        originalRows4 originalAdmission4 e q chi omega := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset ArchiveIndex))
    (fun i _ => each_original_parent_Jensen_sub_reserve i e he q chi omega hw hwr)
  have hsum := P5FullArchiveOwnerIntegralAssembly.archiveFifthIntegral_eq_indexed_owner_sum
    originalRows4 originalAdmission4 e q chi omega
  rw [P1HistoricalFifthTypedBaseGeometry.licensedIndices_eq_univ] at hsum
  rw [hsum]
  simpa only [Finset.sum_sub_distrib] using hs

end
end ImbalancedChen.P5OriginalParentJensenIntegral
