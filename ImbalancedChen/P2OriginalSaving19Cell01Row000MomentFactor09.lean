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
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor09_moment1_before"
  err.flush

theorem factor09_moment1 : prefixMoment (9 : Fin 10) 1 = (637423394429 : ℚ) / 3279803153760 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor09_moment2_before"
  err.flush

theorem factor09_moment2 : prefixMoment (9 : Fin 10) 2 = (16617027845447462070301 : ℚ) / 430284349096561688085504 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor09_moment3_before"
  err.flush

theorem factor09_moment3 : prefixMoment (9 : Fin 10) 3 = (24307075490644068413247995929571801 : ℚ) / 3104745523397038028981495958626009088 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor09_moment4_before"
  err.flush

theorem factor09_moment4 : prefixMoment (9 : Fin 10) 4 = (42794646561015434345018298879770031710468456849 : ℚ) / 26475680814075602709850028287039125616280535564288 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor09_moment5_before"
  err.flush

theorem factor09_moment5 : prefixMoment (9 : Fin 10) 5 = (1115039856012564968445028939478488744679298546541452253691 : ℚ) / 3285649459587232441988499864579421314062313129797704677851136 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor09_moment6_before"
  err.flush

theorem factor09_moment6 : prefixMoment (9 : Fin 10) 6 = (28854788559718412048913029397732136778553848876095638669751091467256527 : ℚ) / 398722488009049651349370519755460000848721507490033217229334644886150840320 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor09_first_moment_before"
  err.flush

theorem factor09_first_moment :
    prefixMoment (9 : Fin 10) 1 = 1 - meansOf row (9 : Fin 10) / topsOf row (9 : Fin 10) := by
  rw [factor09_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor09_gap_before"
  err.flush

theorem factor09_gap_value :
    gapEvaluator (prefixMoment (9 : Fin 10)) = (21870840438061484501602173959134774469504010791636283476147781869731544803 : ℚ) / 33675885811575139472075212817184121693304181375847400103828939601870848000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor09_moment1, factor09_moment2, factor09_moment3, factor09_moment4, factor09_moment5, factor09_moment6]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor09_saved_Q80_before"
  err.flush

theorem factor09_saved_Q80 :
    momentRow.factorFloorsQ80[9]! = factorFloorQ80 (prefixMoment (9 : Fin 10)) := by
  unfold factorFloorQ80
  rw [factor09_gap_value]
  decide +kernel

theorem factor09_Q80_lower :
    ((momentRow.factorFloorsQ80[9]! : ℤ) : ℚ) ≤
      gapEvaluator (prefixMoment (9 : Fin 10)) * (2 : ℚ)^80 := by
  rw [factor09_gap_value]
  decide +kernel

theorem factor09_Q80_upper :
    gapEvaluator (prefixMoment (9 : Fin 10)) * (2 : ℚ)^80 <
      ((momentRow.factorFloorsQ80[9]! : ℤ) : ℚ) + 1 := by
  rw [factor09_gap_value]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor09_complete"
  err.flush

#print axioms factor09_moment1
#print axioms factor09_moment2
#print axioms factor09_moment3
#print axioms factor09_moment4
#print axioms factor09_moment5
#print axioms factor09_moment6
#print axioms factor09_first_moment
#print axioms factor09_gap_value
#print axioms factor09_saved_Q80
#print axioms factor09_Q80_lower
#print axioms factor09_Q80_upper

end ImbalancedChen.P2OriginalSaving19Cell01Row000MomentFloor
