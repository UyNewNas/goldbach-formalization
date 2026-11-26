import ImbalancedChen.P2OriginalSaving19Cell01Row000Input

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
  err.putStrLn "P26_CELL01_ROW000 Means_weighted_means_eq_before"
  err.flush

theorem weighted_means_eq :
    ∀ j : Fin 10, meansOf row j = computedMeanOf vertices j := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000 Means_complete"
  err.flush

#print axioms weighted_means_eq

end ImbalancedChen.P2OriginalSaving19Cell01Row000
