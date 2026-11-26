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
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor07_moment1_before"
  err.flush

theorem factor07_moment1 : prefixMoment (7 : Fin 10) 1 = (244982897903 : ℚ) / 1874205217920 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor07_moment2_before"
  err.flush

theorem factor07_moment2 : prefixMoment (7 : Fin 10) 2 = (6933006418909812591551 : ℚ) / 386390971876641015803904 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor07_moment3_before"
  err.flush

theorem factor07_moment3 : prefixMoment (7 : Fin 10) 3 = (67908408628315052104775562468989 : ℚ) / 26333671841759293322995129465700352 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor07_moment4_before"
  err.flush

theorem factor07_moment4 : prefixMoment (7 : Fin 10) 4 = (68264666367902228611587929532213599004704279 : ℚ) / 176443070992825222652528203053317510453451030528 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor07_moment5_before"
  err.flush

theorem factor07_moment5 : prefixMoment (7 : Fin 10) 5 = (27972458958764009068538188622830778415392090094394082459 : ℚ) / 462966734048814838049135797739484535681706893361490337726464 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor07_moment6_before"
  err.flush

theorem factor07_moment6 : prefixMoment (7 : Fin 10) 6 = (2124583466748130221818706615026110460635328634718135907913644132707 : ℚ) / 216923667169417424365902516367500914396450870957534549938650464617758720 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor07_first_moment_before"
  err.flush

theorem factor07_first_moment :
    prefixMoment (7 : Fin 10) 1 = 1 - meansOf row (7 : Fin 10) / topsOf row (7 : Fin 10) := by
  rw [factor07_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor07_gap_before"
  err.flush

theorem factor07_gap_value :
    gapEvaluator (prefixMoment (7 : Fin 10)) = (49691896714388778435440106401015319695376814966287869328184674019708222333 : ℚ) / 86769466867766969746361006547000365758580348383013819975460185847103488000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor07_moment1, factor07_moment2, factor07_moment3, factor07_moment4, factor07_moment5, factor07_moment6]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor07_saved_Q80_before"
  err.flush

theorem factor07_saved_Q80 :
    momentRow.factorFloorsQ80[7]! = factorFloorQ80 (prefixMoment (7 : Fin 10)) := by
  unfold factorFloorQ80
  rw [factor07_gap_value]
  decide +kernel

theorem factor07_Q80_lower :
    ((momentRow.factorFloorsQ80[7]! : ℤ) : ℚ) ≤
      gapEvaluator (prefixMoment (7 : Fin 10)) * (2 : ℚ)^80 := by
  rw [factor07_gap_value]
  decide +kernel

theorem factor07_Q80_upper :
    gapEvaluator (prefixMoment (7 : Fin 10)) * (2 : ℚ)^80 <
      ((momentRow.factorFloorsQ80[7]! : ℤ) : ℚ) + 1 := by
  rw [factor07_gap_value]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor07_complete"
  err.flush

#print axioms factor07_moment1
#print axioms factor07_moment2
#print axioms factor07_moment3
#print axioms factor07_moment4
#print axioms factor07_moment5
#print axioms factor07_moment6
#print axioms factor07_first_moment
#print axioms factor07_gap_value
#print axioms factor07_saved_Q80
#print axioms factor07_Q80_lower
#print axioms factor07_Q80_upper

end ImbalancedChen.P2OriginalSaving19Cell01Row000MomentFloor
