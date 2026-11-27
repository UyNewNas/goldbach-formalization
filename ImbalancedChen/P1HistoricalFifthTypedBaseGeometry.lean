import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryRows
import ImbalancedChen.P1HistoricalFifthIndexedOwnerArchive
import ImbalancedChen.P1HistoricalFifthCommonPolicyInputs
import ImbalancedChen.P1HistoricalFifthTypedArchiveRange
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlock000
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks001010
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks011020
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks021030
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks031040
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks041050
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks051060
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks061070
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks071080
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks081090
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks091100
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks101110
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks111120
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks121130
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks131140
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks141142
import Mathlib

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
The full independent143-block typed table retains the original positive
lower-key range. All143 original closed obligations are supplied by imports.
Core and block000 have source-bound normal/kernel/full-owned acceptance.
The remaining block owners and this full aggregation await acceptance.
These five-key bounds complement the frozen grid/mask range proof.
No archived-NPY authenticity or owner-gate licence follows.
-/
namespace ImbalancedChen.P1HistoricalFifthTypedBaseGeometry
open P1OriginalPrefixRowDecodeSoundness P1HistoricalFifthTypedArchiveShape
open P1HistoricalFifthTypedArchiveRange P1HistoricalFifthIndexedOwnerArchive
open P1HistoricalFifthCommonPolicyInputs




theorem rows_baseGeometry (row : FifthWireRow)
    (hr : row ∈ Data.P1HistoricalFifthSavedTableData.rows.toList) : baseGeometry row :=
  ⟨rows_grid_eq400 row hr, rows_mask_nonnegative row hr,
    fun k => (rows_lower_key_bounds row hr k).1, (rows_lower_key_bounds row hr 0).2⟩

theorem archiveRow_baseGeometry (i : ArchiveIndex) : baseGeometry (archiveRow i) :=
  rows_baseGeometry _ (archiveRow_source_member i)

theorem archiveRow_grid (i : ArchiveIndex) : (archiveRow i).grid = 400 :=
  (archiveRow_baseGeometry i).1

theorem archiveRow_mask_nonnegative (i : ArchiveIndex) : 0 ≤ (archiveRow i).mask :=
  (archiveRow_baseGeometry i).2.1

noncomputable section
open scoped Classical BigOperators

theorem licensedIndices_eq_univ : licensedIndices = Finset.univ := by
  ext i
  simp [licensedIndices, archiveRow_baseGeometry i]

/-- The geometric rejection set is empty on this actual typed table.
Strict selected/firstStop/full/complement gate rejection is not this set. -/
theorem residualIndices_eq_empty : residualIndices = ∅ := by
  rw [residualIndices, licensedIndices_eq_univ]
  exact Finset.sdiff_self _

theorem all_archive_indices_licensed (i : ArchiveIndex) : i ∈ licensedIndices := by
  rw [licensedIndices_eq_univ]
  exact Finset.mem_univ _

theorem globalOwners_eq_full_index_bank (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    globalOwners e q chi omega =
      Finset.univ.biUnion (fun i : ArchiveIndex => licensedOwners i e q chi omega) := by
  rw [globalOwners, licensedIndices_eq_univ]

theorem common_rows5_eq_full_index_bank
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    (sourceData rows4 licensed4 e q chi omega).rows5 =
      Finset.univ.biUnion (fun i : ArchiveIndex =>
        (licensedOwners i e q chi omega).image (sourceOwnerRow i q)) := by
  simp only [sourceData, licensedRows, licensedIndices_eq_univ]

end
end ImbalancedChen.P1HistoricalFifthTypedBaseGeometry
