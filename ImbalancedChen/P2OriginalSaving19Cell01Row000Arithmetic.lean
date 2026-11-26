import ImbalancedChen.P2OriginalSaving19Cell01Row000Determinant
import ImbalancedChen.P2OriginalSaving19Cell01Row000Physical
import ImbalancedChen.P2OriginalSaving19Cell01Row000Gap
import ImbalancedChen.P2OriginalSaving19Cell01Row000Means
import ImbalancedChen.P2OriginalSaving19Cell01Row000Maxima
import ImbalancedChen.P2OriginalSaving19Cell01Row000Jensen

/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact closed arithmetic for the actual decoded cell01 row0.
Original nine-vertex order, original field values, and the finite arithmetic
specifications are retained. This owner states no integral bound. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row000
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open scoped BigOperators
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000 Arithmetic_row_data_checks_before"
  err.flush

theorem row_data_checks :
    RowDataChecksFor vertices row := by
  exact ⟨det_ne, all_physical, gap_sum_positive, volume_eq, mean_gap_eq,
    weighted_means_eq, factor_le_maxima, factor_maxima_attained,
    jensen_eq, old_floor_eq⟩

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000 Arithmetic_bounded_row_data_checks_before"
  err.flush

theorem bounded_row_data_checks :
    RowDataChecksFor
      (P2OriginalSaving19Geometry01BoundedAccess.boundedRowVertex (0 : Fin 144))
      (P2OriginalSaving19Geometry01BoundedAccess.boundedRow (0 : Fin 144)) := by
  rw [boundedRowVertex_eq, boundedRow_eq]
  exact row_data_checks

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000 Arithmetic_complete"
  err.flush

#print axioms row_data_checks
#print axioms bounded_row_data_checks

end ImbalancedChen.P2OriginalSaving19Cell01Row000
