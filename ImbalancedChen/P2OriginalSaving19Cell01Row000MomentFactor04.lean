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
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor04_moment1_before"
  err.flush

theorem factor04_moment1 : prefixMoment (4 : Fin 10) 1 = (9543791717 : ℚ) / 58469909400 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor04_moment2_before"
  err.flush

theorem factor04_moment2 : prefixMoment (4 : Fin 10) 2 = (206073431199583464211 : ℚ) / 7521206671537258392000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor04_moment3_before"
  err.flush

theorem factor04_moment3 : prefixMoment (4 : Fin 10) 3 = (414736979822518600075988477911 : ℚ) / 87952854532691811380925936960000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor04_moment4_before"
  err.flush

theorem factor04_moment4 : prefixMoment (4 : Fin 10) 4 = (11097250601054431684565533037766138132901 : ℚ) / 13370748133594460828868033897619409702400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor04_moment5_before"
  err.flush

theorem factor04_moment5 : prefixMoment (4 : Fin 10) 5 = (32633576161189450730545137889419488730679181870327 : ℚ) / 218900200954816421881613597033982013074626509516800000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor04_moment6_before"
  err.flush

theorem factor04_moment6 : prefixMoment (4 : Fin 10) 6 = (349126365775342029580219026338192899274799875684551388123191 : ℚ) / 12799074917469909681050124544385037025703027450285533777920000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor04_first_moment_before"
  err.flush

theorem factor04_first_moment :
    prefixMoment (4 : Fin 10) 1 = 1 - meansOf row (4 : Fin 10) / topsOf row (4 : Fin 10) := by
  rw [factor04_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor04_gap_before"
  err.flush

theorem factor04_gap_value :
    gapEvaluator (prefixMoment (4 : Fin 10)) = (21537580515376919679386371728256223735145408866078810116665519491 : ℚ) / 39997109117093467753281639201203240705321960782142293056000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor04_moment1, factor04_moment2, factor04_moment3, factor04_moment4, factor04_moment5, factor04_moment6]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor04_saved_Q80_before"
  err.flush

theorem factor04_saved_Q80 :
    momentRow.factorFloorsQ80[4]! = factorFloorQ80 (prefixMoment (4 : Fin 10)) := by
  unfold factorFloorQ80
  rw [factor04_gap_value]
  decide +kernel

theorem factor04_Q80_lower :
    ((momentRow.factorFloorsQ80[4]! : ℤ) : ℚ) ≤
      gapEvaluator (prefixMoment (4 : Fin 10)) * (2 : ℚ)^80 := by
  rw [factor04_gap_value]
  decide +kernel

theorem factor04_Q80_upper :
    gapEvaluator (prefixMoment (4 : Fin 10)) * (2 : ℚ)^80 <
      ((momentRow.factorFloorsQ80[4]! : ℤ) : ℚ) + 1 := by
  rw [factor04_gap_value]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor04_complete"
  err.flush

#print axioms factor04_moment1
#print axioms factor04_moment2
#print axioms factor04_moment3
#print axioms factor04_moment4
#print axioms factor04_moment5
#print axioms factor04_moment6
#print axioms factor04_first_moment
#print axioms factor04_gap_value
#print axioms factor04_saved_Q80
#print axioms factor04_Q80_lower
#print axioms factor04_Q80_upper

end ImbalancedChen.P2OriginalSaving19Cell01Row000MomentFloor
