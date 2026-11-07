import ImbalancedChen.Data.P1HistoricalFifthSavedTableData
import ImbalancedChen.P1HistoricalFifthTypedArchiveShape
import ImbalancedChen.P1OriginalFifthAdoptedOwnerBank
import Mathlib

/-!
Full archived typed-source index space, with explicit rejected rows/owners.
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.

The independent original 143-block literal table is imported, never replaced
by two named parents or a newly invented row model. Array order and source
multiplicity are retained by Fin indices, not erased by a row toFinset.
The typed literals' identity with independent archived NPY bytes remains a
separate authenticity obligation; a source SHA is not a Lean equality proof.
-/
namespace ImbalancedChen.P1HistoricalFifthIndexedOwnerArchive
noncomputable section
open Set
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1HistoricalFifthTableParser P1HistoricalFifthTypedArchiveShape
open P1OriginalCoarseFifthContinuation P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalFifthAdoptedOwnerBank

abbrev ArchiveIndex := Fin Data.P1HistoricalFifthSavedTableData.rows.toList.length

def archiveRow (i : ArchiveIndex) : FifthWireRow :=
  Data.P1HistoricalFifthSavedTableData.rows.toList[i.val]

theorem archiveIndex_card : Fintype.card ArchiveIndex = 292633 := by
  simpa only [ArchiveIndex, Fintype.card_fin] using rows_toList_length

theorem archiveRow_source_member (i : ArchiveIndex) :
    archiveRow i ∈ Data.P1HistoricalFifthSavedTableData.rows.toList := List.getElem_mem i.isLt

/-- All ten original signed fields, including the three opaque statistics,
remain attached to the SAME source row index. They are not interpreted as
policy caps, licences, gains or a numerical floor. -/
theorem archiveRow_ten_columns (i : ArchiveIndex) :
    namedRow (archiveRow i) =
      [("n", (archiveRow i).grid), ("l1", (archiveRow i).lo 0),
       ("l2", (archiveRow i).lo 1), ("l3", (archiveRow i).lo 2),
       ("l4", (archiveRow i).lo 3), ("l5", (archiveRow i).lo 4),
       ("mask", (archiveRow i).mask), ("vertex_gap_sum", (archiveRow i).vertexGapSum),
       ("A", (archiveRow i).ratioA), ("B", (archiveRow i).ratioB)] := namedRow_exact _

/-- The precise already-proved B13 row geometry. Rejection is retained as
an explicit source-index remainder, not asserted absent on the archive. -/
def baseGeometry (raw : FifthWireRow) : Prop :=
  raw.grid = 400 ∧ 0 ≤ raw.mask ∧ (∀ k, 1 ≤ raw.lo k) ∧ raw.lo 0 ≤ 77

def licensedIndices : Finset ArchiveIndex := Finset.univ.filter (fun i => baseGeometry (archiveRow i))

def residualIndices : Finset ArchiveIndex := Finset.univ \ licensedIndices

theorem licensedIndex_geometry (i : ArchiveIndex) (hi : i ∈ licensedIndices) :
    baseGeometry (archiveRow i) := (Finset.mem_filter.mp hi).2

theorem residualIndex_iff (i : ArchiveIndex) :
    i ∈ residualIndices ↔ ¬ baseGeometry (archiveRow i) := by
  simp [residualIndices, licensedIndices]

theorem full_source_index_partition : licensedIndices ∪ residualIndices = Finset.univ := by
  ext i
  simp [residualIndices]

theorem source_index_partition_disjoint : Disjoint licensedIndices residualIndices := by
  apply Finset.disjoint_left.mpr
  intro i hi hir
  exact (Finset.mem_sdiff.mp hir).2 hi

/-- The actual full decoder has a source INDEX witness, not merely a
possibly deduplicated raw-row value. -/
def fullArchiveDecoded (q : ℕ) : Finset (FifthRow (refinedMesh q)) :=
  decodeTableAt Data.P1HistoricalFifthSavedTableData.rows (refinedMesh q)

theorem fullArchiveDecoded_iff_source_index (q : ℕ) (r : FifthRow (refinedMesh q)) :
    r ∈ fullArchiveDecoded q ↔ ∃ i : ArchiveIndex, r ∈ decodeFifthRows (archiveRow i) (refinedMesh q) := by
  rw [fullArchiveDecoded, mem_decodeTableAt]
  constructor
  · rintro ⟨wire, hwire, hr⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hwire
    have heq : archiveRow i = wire := hi
    exact ⟨i, heq.symm ▸ hr⟩
  · rintro ⟨i, hi⟩
    exact ⟨archiveRow i, archiveRow_source_member i, hi⟩

/-- Every actual source owner retains its original mask. Additional full
and complement-square licences are tested on the TRUE variable row. -/
def sourceOwnerRow (i : ArchiveIndex) (q : ℕ) (j : Label5 (refinedMesh q)) : FifthRow (refinedMesh q) :=
  ⟨j, maskSlots 5 (archiveRow i).mask.toNat⟩

def licensedOwners (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    Finset (Label5 (refinedMesh q)) :=
  (adoptedOwners (archiveRow i) e q chi omega).filter
    (fun j => gateCheck 0 (refinedMesh q) (sourceOwnerRow i q j) = true ∧
      gateCheck e (refinedMesh q) (sourceOwnerRow i q j) = true)

def missingOwners (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    Finset (Label5 (refinedMesh q)) := decodedLabels (archiveRow i) q \ licensedOwners i e q chi omega

theorem licensedOwner_adopted (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ)
    (j : Label5 (refinedMesh q)) (hj : j ∈ licensedOwners i e q chi omega) :
    j ∈ adoptedOwners (archiveRow i) e q chi omega := (Finset.mem_filter.mp hj).1

theorem licensedOwner_decoded (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ)
    (j : Label5 (refinedMesh q)) (hj : j ∈ licensedOwners i e q chi omega) :
    sourceOwnerRow i q j ∈ decodeFifthRows (archiveRow i) (refinedMesh q) := by
  obtain ⟨r, hr, hcell⟩ := adoptedOwners_original_decoded (archiveRow i) e q chi omega j
    (licensedOwner_adopted i e q chi omega j hj)
  have hmask := decodeFifthRows_selected_eq (archiveRow i) (refinedMesh q) r hr
  have heq : r = sourceOwnerRow i q j := by
    cases r
    simp only [sourceOwnerRow, FifthRow.mk.injEq] at *
    exact ⟨hcell, hmask⟩
  exact heq ▸ hr

theorem licensedOwner_gate_zero (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ)
    (j : Label5 (refinedMesh q)) (hj : j ∈ licensedOwners i e q chi omega) :
    gateCheck 0 (refinedMesh q) (sourceOwnerRow i q j) = true := (Finset.mem_filter.mp hj).2.1

theorem licensedOwner_gate_buffer (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ)
    (j : Label5 (refinedMesh q)) (hj : j ∈ licensedOwners i e q chi omega) :
    gateCheck e (refinedMesh q) (sourceOwnerRow i q j) = true := (Finset.mem_filter.mp hj).2.2

theorem licensedOwner_selected_zero (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ)
    (j : Label5 (refinedMesh q)) (hj : j ∈ licensedOwners i e q chi omega) :
    j ∈ selectedFifthCells 0 chi (refinedMesh q) omega (licensedOwners i e q chi omega) := by
  have ha := adoptedOwners_selected_zero (archiveRow i) e q chi omega j
    (licensedOwner_adopted i e q chi omega j hj)
  exact (mem_selectedFifthCells 0 chi (refinedMesh q) omega _ j).mpr
    ⟨hj, ((mem_selectedFifthCells 0 chi (refinedMesh q) omega _ j).mp ha).2⟩

theorem licensedOwner_selected_buffer (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ)
    (j : Label5 (refinedMesh q)) (hj : j ∈ licensedOwners i e q chi omega) :
    j ∈ selectedFifthCells e chi (refinedMesh q) omega (licensedOwners i e q chi omega) := by
  have ha := adoptedOwners_selected_buffer (archiveRow i) e q chi omega j
    (licensedOwner_adopted i e q chi omega j hj)
  exact (mem_selectedFifthCells e chi (refinedMesh q) omega _ j).mpr
    ⟨hj, ((mem_selectedFifthCells e chi (refinedMesh q) omega _ j).mp ha).2⟩

theorem licensedOwner_firstStop_zero (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ)
    (j : Label5 (refinedMesh q)) (hj : j ∈ licensedOwners i e q chi omega) :
    P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck 0 (refinedMesh q) j = true :=
  adoptedOwners_firstStop_zero (archiveRow i) e q chi omega j
    (licensedOwner_adopted i e q chi omega j hj)

theorem licensedOwner_firstStop_buffer (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ)
    (j : Label5 (refinedMesh q)) (hj : j ∈ licensedOwners i e q chi omega) :
    P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck (e : ℝ) (refinedMesh q) j = true :=
  adoptedOwners_firstStop_buffer (archiveRow i) e q chi omega j
    (licensedOwner_adopted i e q chi omega j hj)

/-- Global source owner labels are compiled from ALL licensed source
indices. Per-row masks are retained independently in licensedRows below. -/
def globalOwners (e : ℚ) (q : ℕ) (chi omega : ℝ) : Finset (Label5 (refinedMesh q)) :=
  licensedIndices.biUnion (fun i => licensedOwners i e q chi omega)

def licensedRows (e : ℚ) (q : ℕ) (chi omega : ℝ) : Finset (FifthRow (refinedMesh q)) :=
  licensedIndices.biUnion (fun i =>
    (licensedOwners i e q chi omega).image (sourceOwnerRow i q))

theorem licensedRows_source_index (e : ℚ) (q : ℕ) (chi omega : ℝ) (r : FifthRow (refinedMesh q))
    (hr : r ∈ licensedRows e q chi omega) :
    ∃ i ∈ licensedIndices, r.cell ∈ licensedOwners i e q chi omega ∧
      r = sourceOwnerRow i q r.cell ∧ r ∈ decodeFifthRows (archiveRow i) (refinedMesh q) := by
  obtain ⟨i, hi, hrImage⟩ := Finset.mem_biUnion.mp hr
  obtain ⟨j, hj, hrj⟩ := Finset.mem_image.mp hrImage
  have hrj' : r = sourceOwnerRow i q j := hrj.symm
  subst r
  exact ⟨i, hi, hj, rfl, licensedOwner_decoded i e q chi omega j hj⟩

theorem globalOwner_selected_zero (e : ℚ) (q : ℕ) (chi omega : ℝ)
    (j : Label5 (refinedMesh q)) (hj : j ∈ globalOwners e q chi omega) :
    j ∈ selectedFifthCells 0 chi (refinedMesh q) omega (globalOwners e q chi omega) := by
  obtain ⟨i, _hi, hij⟩ := Finset.mem_biUnion.mp hj
  have hadopt := adoptedOwners_selected_zero (archiveRow i) e q chi omega j
    (licensedOwner_adopted i e q chi omega j hij)
  have hg := (mem_selectedFifthCells 0 chi (refinedMesh q) omega _ j).mp hadopt
  exact (mem_selectedFifthCells 0 chi (refinedMesh q) omega _ j).mpr ⟨hj, hg.2⟩

theorem globalOwner_selected_buffer (e : ℚ) (q : ℕ) (chi omega : ℝ)
    (j : Label5 (refinedMesh q)) (hj : j ∈ globalOwners e q chi omega) :
    j ∈ selectedFifthCells e chi (refinedMesh q) omega (globalOwners e q chi omega) := by
  obtain ⟨i, _hi, hij⟩ := Finset.mem_biUnion.mp hj
  have hadopt := adoptedOwners_selected_buffer (archiveRow i) e q chi omega j
    (licensedOwner_adopted i e q chi omega j hij)
  have hg := (mem_selectedFifthCells e chi (refinedMesh q) omega _ j).mp hadopt
  exact (mem_selectedFifthCells e chi (refinedMesh q) omega _ j).mpr ⟨hj, hg.2⟩

/-- The entire remainder is explicit, including individual rejected
original labels within a positive/licensed raw source row. -/
theorem all_decoded_owner_partition (i : ArchiveIndex) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    licensedOwners i e q chi omega ∪ missingOwners i e q chi omega = decodedLabels (archiveRow i) q := by
  have hsub : licensedOwners i e q chi omega ⊆ decodedLabels (archiveRow i) q := by
    intro j hj
    have hd := licensedOwner_decoded i e q chi omega j hj
    exact Finset.mem_image.mpr ⟨sourceOwnerRow i q j, hd, rfl⟩
  ext j
  simp only [Finset.mem_union, missingOwners, Finset.mem_sdiff]
  constructor
  · rintro (h | h)
    · exact hsub h
    · exact h.1
  · intro h
    by_cases hj : j ∈ licensedOwners i e q chi omega
    · exact Or.inl hj
    · exact Or.inr ⟨h, hj⟩

end
end ImbalancedChen.P1HistoricalFifthIndexedOwnerArchive
