import ImbalancedChen.P4AOriginalFull87ArchiveSourceIndex
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The frozen selected 87-row numerical archive was reconciled in source-order,
but its TOTAL was a List sum, not the sum indexed by the ORIGINAL source Cell
type. We use the existing original globalIndex bijection, not a new arbitrary
owner or a replacement numerical certificate, to transport *every* Cell weight.
The unweighted specialization is then the exact previously certified six-stage
rational aggregate.

This does NOT identify a numerical label with an N-dependent physical
occurrence, authenticate a geometric witness or prove a signed saving.
-/

namespace ImbalancedChen.P4AOriginalFull87CellIndexedArchiveWeight
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87ArchiveSourceIndex
open P4AOriginalFull87ArchivedStageNumericReconcile

/-- All 87 ORIGINAL Cell constructors are used once, by their existing
bijective globalIndex. In particular, the adopted ascending seed remains
index 7 and the winner9 seed remains index 41. Weights may differ by Cell:
no equality of actual members, parents or signs is inferred. -/
theorem original_cell_archive_weight_transport
    (weight : Fin 87 → ℚ) :
    (∑ c : Cell,
        weight (globalIndex c) * (archivedRecordForOriginalCell c).2) =
      ∑ i : Fin 87, weight i * (sourceIndexRecord i).2 := by
  simpa only [archivedRecordForOriginalCell] using
    (globalIndex_bijective.sum_comp
      (fun i : Fin 87 => weight i * (sourceIndexRecord i).2))

/-- The length-87 indexed sum is exactly the existing ORIGINAL archived
List sum. The index conversion uses the already proved literal row count,
not an independently supplied permutation. -/
private theorem original_indexed_fin_sum :
    (∑ i : Fin 87, (sourceIndexRecord i).2) =
      (sourceIndexedRecords.map Prod.snd).sum := by
  have h :
      (∑ i : Fin sourceIndexedRecords.length,
          (sourceIndexedRecords.get i).2) =
        (sourceIndexedRecords.map Prod.snd).sum := by
    calc
      _ = (List.ofFn (fun i : Fin sourceIndexedRecords.length =>
            (sourceIndexedRecords.get i).2)).sum := by
              symm
              exact List.sum_ofFn
      _ = _ := by
            exact congrArg List.sum
              (List.ofFn_get_eq_map sourceIndexedRecords Prod.snd)
  simpa [sourceIndexRecord, source_indexed_records_length] using h

/-- The ORIGINAL Cell-indexed frozen 87-row selected aggregate has the
exact six-stage selected numerical value. This is only a numerical archive
reindexing: actual Source membership, same-N parent and gain transfer remain
unproved and may not be discharged from this equality. -/
theorem original_cell_archive_selected_sum_exact :
    (∑ c : Cell, (archivedRecordForOriginalCell c).2) =
      ((3111307568597708509491143 : ℚ) /
        79228162514264337593543950336) := by
  have htransport :=
    original_cell_archive_weight_transport (fun _ => (1 : ℚ))
  simp only [one_mul] at htransport
  calc
    _ = (∑ i : Fin 87, (sourceIndexRecord i).2) := htransport
    _ = (sourceIndexedRecords.map Prod.snd).sum :=
      original_indexed_fin_sum
    _ = selectedEighthArchiveTotal :=
      source_indexed_selected_total
    _ = _ := selected_eighth_total_exact

end
end ImbalancedChen.P4AOriginalFull87CellIndexedArchiveWeight
