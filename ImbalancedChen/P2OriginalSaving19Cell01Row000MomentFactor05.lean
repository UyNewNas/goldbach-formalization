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
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor05_moment1_before"
  err.flush

theorem factor05_moment1 : prefixMoment (5 : Fin 10) 1 = (609131079027 : ℚ) / 2651182519300 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor05_moment2_before"
  err.flush

theorem factor05_moment2 : prefixMoment (5 : Fin 10) 2 = (848850144369433717420611 : ℚ) / 15463291251412168719478000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor05_moment3_before"
  err.flush

theorem factor05_moment3 : prefixMoment (5 : Fin 10) 3 = (55714509062657434850058281424914553 : ℚ) / 4099600745658856314838233902092540000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor05_moment4_before"
  err.flush

theorem factor05_moment4 : prefixMoment (5 : Fin 10) 4 = (196533304809299162995755545694907079794487463141 : ℚ) / 56517707131600027160273623228264322642467314400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor05_moment5_before"
  err.flush

theorem factor05_moment5 : prefixMoment (5 : Fin 10) 5 = (38508543864772171692798481030604042902942422375404445270597 : ℚ) / 41954852009900182261082341806141665643478067772491207017600000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor05_moment6_before"
  err.flush

theorem factor05_moment6 : prefixMoment (5 : Fin 10) 6 = (27757036789103014637308115088443383919236949822576424368836960080892071 : ℚ) / 111229970248465833748465453294350373333374439331369377458018607439680000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor05_first_moment_before"
  err.flush

theorem factor05_first_moment :
    prefixMoment (5 : Fin 10) 1 = 1 - meansOf row (5 : Fin 10) / topsOf row (5 : Fin 10) := by
  rw [factor05_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor05_gap_before"
  err.flush

theorem factor05_gap_value :
    gapEvaluator (prefixMoment (5 : Fin 10)) = (620556456826077916580024765268513693874941196620249229085537766796573542211 : ℚ) / 347593657026455730463954541544844916666795122910529304556308148249000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor05_moment1, factor05_moment2, factor05_moment3, factor05_moment4, factor05_moment5, factor05_moment6]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor05_saved_Q80_before"
  err.flush

theorem factor05_saved_Q80 :
    momentRow.factorFloorsQ80[5]! = factorFloorQ80 (prefixMoment (5 : Fin 10)) := by
  unfold factorFloorQ80
  rw [factor05_gap_value]
  decide +kernel

theorem factor05_Q80_lower :
    ((momentRow.factorFloorsQ80[5]! : ℤ) : ℚ) ≤
      gapEvaluator (prefixMoment (5 : Fin 10)) * (2 : ℚ)^80 := by
  rw [factor05_gap_value]
  decide +kernel

theorem factor05_Q80_upper :
    gapEvaluator (prefixMoment (5 : Fin 10)) * (2 : ℚ)^80 <
      ((momentRow.factorFloorsQ80[5]! : ℤ) : ℚ) + 1 := by
  rw [factor05_gap_value]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor05_complete"
  err.flush

#print axioms factor05_moment1
#print axioms factor05_moment2
#print axioms factor05_moment3
#print axioms factor05_moment4
#print axioms factor05_moment5
#print axioms factor05_moment6
#print axioms factor05_first_moment
#print axioms factor05_gap_value
#print axioms factor05_saved_Q80
#print axioms factor05_Q80_lower
#print axioms factor05_Q80_upper

end ImbalancedChen.P2OriginalSaving19Cell01Row000MomentFloor
