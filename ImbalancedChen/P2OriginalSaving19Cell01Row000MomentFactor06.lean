import ImbalancedChen.P2OriginalSaving19Cell01Row000MomentEncoding
import ImbalancedChen.P2OriginalSaving19Cell01Row000OldFloor

/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact degree-one through degree-six moments for one actual factor,
followed by its original Q80 integer and both floor inequalities. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row000MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row000
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor06_moment1_before"
  err.flush

theorem factor06_moment1 : prefixMoment (6 : Fin 10) 1 = (543633614813 : ℚ) / 2272406173800 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor06_moment2_before"
  err.flush

theorem factor06_moment2 : prefixMoment (6 : Fin 10) 2 = (165153792975015765321769 : ℚ) / 2840106400298395693542000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor06_moment3_before"
  err.flush

theorem factor06_moment3 : prefixMoment (6 : Fin 10) 3 = (37013012121408205943866146532833797 : ℚ) / 2581550127314787414496069435839840000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor06_moment4_before"
  err.flush

theorem factor06_moment4 : prefixMoment (6 : Fin 10) 4 = (6827849391385098987594434259158662783110875761 : ℚ) / 1906557395367397154439007535596679006301362400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor06_moment5_before"
  err.flush

theorem factor06_moment5 : prefixMoment (6 : Fin 10) 5 = (1098267445421408712675858909926628999648471462442983458093 : ℚ) / 1213092382862337827635450783841692659394898205911131833600000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor06_moment6_before"
  err.flush

theorem factor06_moment6 : prefixMoment (6 : Fin 10) 6 = (159515761916573344625642752867675468855994125617557536505276262146809 : ℚ) / 689159655051532448755019654236977920262776813833749908204588569920000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor06_first_moment_before"
  err.flush

theorem factor06_first_moment :
    prefixMoment (6 : Fin 10) 1 = 1 - meansOf row (6 : Fin 10) / topsOf row (6 : Fin 10) := by
  rw [factor06_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor06_gap_before"
  err.flush

theorem factor06_gap_value :
    gapEvaluator (prefixMoment (6 : Fin 10)) = (23967697361466587136608983160329341334602928550963407897680881585504477693 : ℚ) / 30629318002290331055778651299421240900567858392611107031315047552000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor06_moment1, factor06_moment2, factor06_moment3, factor06_moment4, factor06_moment5, factor06_moment6]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor06_saved_Q80_before"
  err.flush

theorem factor06_saved_Q80 :
    momentRow.factorFloorsQ80[6]! = factorFloorQ80 (prefixMoment (6 : Fin 10)) := by
  unfold factorFloorQ80
  rw [factor06_gap_value]
  decide +kernel

theorem factor06_Q80_lower :
    ((momentRow.factorFloorsQ80[6]! : ℤ) : ℚ) ≤
      gapEvaluator (prefixMoment (6 : Fin 10)) * (2 : ℚ)^80 := by
  rw [factor06_gap_value]
  decide +kernel

theorem factor06_Q80_upper :
    gapEvaluator (prefixMoment (6 : Fin 10)) * (2 : ℚ)^80 <
      ((momentRow.factorFloorsQ80[6]! : ℤ) : ℚ) + 1 := by
  rw [factor06_gap_value]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor06_complete"
  err.flush

#print axioms factor06_moment1
#print axioms factor06_moment2
#print axioms factor06_moment3
#print axioms factor06_moment4
#print axioms factor06_moment5
#print axioms factor06_moment6
#print axioms factor06_first_moment
#print axioms factor06_gap_value
#print axioms factor06_saved_Q80
#print axioms factor06_Q80_lower
#print axioms factor06_Q80_upper

end ImbalancedChen.P2OriginalSaving19Cell01Row000MomentFloor
