import ImbalancedChen.P4AOriginalFull87SourceDictionary
import ImbalancedChen.P4AOriginalFull87ArchivedStageNumericReconcile
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Finite link from the FROZEN selected archive's 87 numeric labels to the
ORIGINAL affine-source Cell index. This is NOT a map to actual N-dependent
states/prime occurrences, and it supplies neither new source membership nor
a claim about signed arithmetic savings.

The input archive has its own order: 9seed, 9-00..9-10, 9-12, 50A, 50D.
The original source dictionary uses the 0..12 winner9 index, including the
adopted duplicate cell 11. Therefore moving 9seed from the first archived
position to ORIGINAL source index 11 is indispensable. Similarly ascending
ID 7 is the radial whole-cell replacement, not a fifteenth "new" cell.
Every row retains the archived rational value; refined stages use final,
never final+increment.
-/

namespace ImbalancedChen.P4AOriginalFull87ArchiveSourceIndex
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87ArchivedStageNumericReconcile

/-- Align unequal winner9 archive labels to ORIGINAL indices 0..12.
Physical affine-row/geometry correspondence is still awaiting replay:
the mapping here is the recorded original cell-name convention. -/
def unequalSourceOrder : List MomentArchiveRow :=
  ((unequalRows.drop 1).take 11) ++ (unequalRows.take 1) ++
    (unequalRows.drop 12)

/-- A finite commutative sum identity for the nontrivial winner9 reorder.
No signed sieve monotonicity, cap inequality or geometry assumption is used. -/
theorem unequal_source_reorder_sum :
    (unequalSourceOrder.map MomentArchiveRow.final).sum =
      (unequalRows.map MomentArchiveRow.final).sum := by
  have hparts : unequalRows =
      unequalRows.take 1 ++ (unequalRows.drop 1).take 11 ++
        unequalRows.drop 12 := by
    rfl
  have hsum := congrArg
    (fun xs : List MomentArchiveRow =>
      (xs.map MomentArchiveRow.final).sum) hparts
  simp only [List.map_append, List.sum_append] at hsum
  simp only [unequalSourceOrder, List.map_append, List.sum_append]
  linarith

/-- Source-dictionary order:
ascending 0..6, adopted seed 7, ascending 8..14,
descending 0..14, winner9 0..12 (seed at 11), 50A/50D,
ascending-pair 0..12, H3 0..11, H5 0..6 and H7 0..9.
Only the FROZEN NUMERIC source is encoded here. -/
def sourceIndexedRecords : List (String × ℚ) :=
  (ascendingRows.take 7) ++
  [("a07-radial-whole", radialWhole)] ++
  (ascendingRows.drop 7) ++
  descendingRows ++
  (unequalSourceOrder.map (fun r => (r.label, r.final))) ++
  (thirdRows.map (fun r => (r.label, r.final))) ++
  (historyRows.map (fun r => (r.label, r.final)))

theorem source_indexed_records_length : sourceIndexedRecords.length = 87 := by
  decide

/-- The 87 retained ARCHIVE KEYS are unambiguous; this is not a statement
that 87 physical N-dependent prime occurrences are distinct. -/
theorem source_indexed_labels_nodup :
    (sourceIndexedRecords.map Prod.fst).Nodup := by
  decide

/-- Exact numeric effect of moving the adopted winner9 record to position
11. The selected total is unchanged and no moment increment is paid twice. -/
theorem source_indexed_selected_total :
    (sourceIndexedRecords.map Prod.snd).sum =
      selectedEighthArchiveTotal := by
  have ha := congrArg
    (fun xs : List (String × ℚ) => (xs.map Prod.snd).sum)
    (List.take_append_drop 7 ascendingRows)
  simp only [List.map_append, List.sum_append] at ha
  unfold sourceIndexedRecords selectedEighthArchiveTotal
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.map_map, Function.comp_def, Prod.snd]
  rw [unequal_source_reorder_sum]
  linarith

/-- The same exact selected rational sum as the frozen six-stage ledger. -/
theorem source_indexed_selected_rational :
    (sourceIndexedRecords.map Prod.snd).sum =
      ((3111307568597708509491143 : ℚ) /
        79228162514264337593543950336) := by
  rw [source_indexed_selected_total, selected_eighth_total_exact]

/-- A total, bounds-checked accessor to the 87 numerical positions. -/
def sourceIndexRecord (i : Fin 87) : String × ℚ :=
  sourceIndexedRecords.get ⟨i.val, by
    simpa [source_indexed_records_length] using i.isLt⟩

/-- Link the existing ORIGINAL Cell constructors, not a caller-supplied
Cell or surrogate parent, to the exact source-ordered archive table.
This label/value is not evidence that a physical prime tuple belongs to
Source c, actualParent, or the old/new ordinary continuation. -/
def archivedRecordForOriginalCell (c : Cell) : String × ℚ :=
  sourceIndexRecord (globalIndex c)

/-- Concrete cross-checks of the historically hazardous source positions. -/
theorem ascending_adopted_seven_is_radial :
    (archivedRecordForOriginalCell (.remaining .seed)).1 =
      "a07-radial-whole" := by
  decide

theorem unequal_zero_not_archived_seed :
    (archivedRecordForOriginalCell (.remaining (.nine (0 : Fin 13)))).1 =
      "u-9-00" := by
  decide

theorem unequal_eleven_is_archived_seed :
    (archivedRecordForOriginalCell (.remaining (.nine (11 : Fin 13)))).1 =
      "u-9seed" := by
  decide

theorem unequal_twelve_keeps_original_id :
    (archivedRecordForOriginalCell (.remaining (.nine (12 : Fin 13)))).1 =
      "u-9-12" := by
  decide

theorem history_h3_zero_keeps_failure_class :
    (archivedRecordForOriginalCell (.h3 (0 : Fin 12))).1 = "h3-00" := by
  decide

theorem history_h5_zero_keeps_failure_class :
    (archivedRecordForOriginalCell (.remaining (.h5 (0 : Fin 7)))).1 =
      "h5-00" := by
  decide

theorem history_h7_nine_keeps_failure_class :
    (archivedRecordForOriginalCell (.remaining (.h7 (9 : Fin 10)))).1 =
      "h7-09" := by
  decide

end
end ImbalancedChen.P4AOriginalFull87ArchiveSourceIndex
