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
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor08_moment1_before"
  err.flush

theorem factor08_moment1 : prefixMoment (8 : Fin 10) 1 = (637462578749 : ℚ) / 3279859131360 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor08_moment2_before"
  err.flush

theorem factor08_moment2 : prefixMoment (8 : Fin 10) 2 = (182809615143613059054911 : ℚ) / 4733289405488852443597824 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor08_moment3_before"
  err.flush

theorem factor08_moment3 : prefixMoment (8 : Fin 10) 3 = (2210135855746103981916511038895051 : ℚ) / 282264045053857425305854043960475648 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor08_moment4_before"
  err.flush

theorem factor08_moment4 : prefixMoment (8 : Fin 10) 4 = (3292688539410271729200676165579553053384764053 : ℚ) / 2036729872373910382638077959283727608647768866816 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor08_moment5_before"
  err.flush

theorem factor08_moment5 : prefixMoment (8 : Fin 10) 5 = (41268814413544150404055068831932550123847982670243646716167 : ℚ) / 121579404674350484110809771134492446737538246198852626658885632 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor08_moment6_before"
  err.flush

theorem factor08_moment6 : prefixMoment (8 : Fin 10) 6 = (28865083840612859606938475182644936643394232139779632284637708977492687 : ℚ) / 398763320606481102487876017939376798091063258082546597902067007997104619520 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor08_first_moment_before"
  err.flush

theorem factor08_first_moment :
    prefixMoment (8 : Fin 10) 1 = 1 - meansOf row (8 : Fin 10) / topsOf row (8 : Fin 10) := by
  rw [factor08_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor08_gap_before"
  err.flush

theorem factor08_gap_value :
    gapEvaluator (prefixMoment (8 : Fin 10)) = (89928790611998262769060088593109506210492664267083530902806968026845694039 : ℚ) / 138459486321694827252734728451172499337174742389773124271551044443439104000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor08_moment1, factor08_moment2, factor08_moment3, factor08_moment4, factor08_moment5, factor08_moment6]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor08_saved_Q80_before"
  err.flush

theorem factor08_saved_Q80 :
    momentRow.factorFloorsQ80[8]! = factorFloorQ80 (prefixMoment (8 : Fin 10)) := by
  unfold factorFloorQ80
  rw [factor08_gap_value]
  decide +kernel

theorem factor08_Q80_lower :
    ((momentRow.factorFloorsQ80[8]! : ℤ) : ℚ) ≤
      gapEvaluator (prefixMoment (8 : Fin 10)) * (2 : ℚ)^80 := by
  rw [factor08_gap_value]
  decide +kernel

theorem factor08_Q80_upper :
    gapEvaluator (prefixMoment (8 : Fin 10)) * (2 : ℚ)^80 <
      ((momentRow.factorFloorsQ80[8]! : ℤ) : ℚ) + 1 := by
  rw [factor08_gap_value]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor08_complete"
  err.flush

#print axioms factor08_moment1
#print axioms factor08_moment2
#print axioms factor08_moment3
#print axioms factor08_moment4
#print axioms factor08_moment5
#print axioms factor08_moment6
#print axioms factor08_first_moment
#print axioms factor08_gap_value
#print axioms factor08_saved_Q80
#print axioms factor08_Q80_lower
#print axioms factor08_Q80_upper

end ImbalancedChen.P2OriginalSaving19Cell01Row000MomentFloor
