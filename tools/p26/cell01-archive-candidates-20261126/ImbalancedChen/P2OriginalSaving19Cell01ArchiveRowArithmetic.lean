import ImbalancedChen.P2OriginalSaving19Cell01ArchiveBridge
import ImbalancedChen.P2OriginalSaving19Cell01AllRowArithmetic

/-!
SOURCE CANDIDATE / NOT COMPILED. Bind the existing all144 row-arithmetic
certificates to exactly the Archive selectors used by the cell01 floor
bridge. The ten-clause RowDataChecksFor predicate is unchanged. No original
data check, parser result, floor or integral bound is assumed.
-/
namespace ImbalancedChen.P2OriginalSaving19Cell01ArchiveRowArithmetic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19Archive
open P2OriginalSaving19MomentFloorConsumer (originalRowCount)
open P2OriginalSaving19RowNumericsPure (RowDataChecksFor)
open P2OriginalSaving19Cell01ArchiveBridge

theorem all_original_archive_row_data_checks (r : Fin 144) :
    RowDataChecksFor (archiveRawVertex (cell01RowIndex r))
      (archiveGeometryRow (cell01RowIndex r)) := by
  rw [archiveRawVertex_one, archiveGeometryRow_one]
  exact P2OriginalSaving19Cell01AllRowArithmetic.all_raw_row_data_checks r

/-- Expose the exact original dependent row bound and three-level vertex access. -/
theorem all_original_archive_row_data_checks_at_one
    (r : Fin (originalRowCount (1 : Fin 13))) :
    RowDataChecksFor
      (fun (i : Fin 9) (j : Fin 8) =>
        (((geometry (1 : Fin 13)).vertices[
          ((geometry (1 : Fin 13)).rows[r.val]!).vertexIds[i.val]!]!)[j.val]!))
      ((geometry (1 : Fin 13)).rows[r.val]!) := by
  exact all_original_archive_row_data_checks r

#print axioms all_original_archive_row_data_checks
#print axioms all_original_archive_row_data_checks_at_one

end ImbalancedChen.P2OriginalSaving19Cell01ArchiveRowArithmetic

