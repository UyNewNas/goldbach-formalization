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
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor03_moment1_before"
  err.flush

theorem factor03_moment1 : prefixMoment (3 : Fin 10) 1 = (602725187399 : ℚ) / 3810873707200 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor03_moment2_before"
  err.flush

theorem factor03_moment2 : prefixMoment (3 : Fin 10) 2 = (817259078993095111842459 : ℚ) / 31950068506902196930048000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor03_moment3_before"
  err.flush

theorem factor03_moment3 : prefixMoment (3 : Fin 10) 3 = (102855583295687340261314523513921093 : ℚ) / 24351535203238468800527296166789120000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor03_moment4_before"
  err.flush

theorem factor03_moment4 : prefixMoment (3 : Fin 10) 4 = (13200897477100169434184389207573516673078599977 : ℚ) / 18560125047195337808703398891584800651005132800000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor03_moment5_before"
  err.flush

theorem factor03_moment5 : prefixMoment (3 : Fin 10) 5 = (766247107028763108836709756717635666551442439778115178069 : ℚ) / 6279469874700272534773166829744865124630507560408344166400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor03_moment6_before"
  err.flush

theorem factor03_moment6 : prefixMoment (3 : Fin 10) 6 = (20910638847898995553983399400065584936302879058948290927481888021445039 : ℚ) / 981140932266639630421095726689709300894250747454989953648112728801280000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor03_first_moment_before"
  err.flush

theorem factor03_first_moment :
    prefixMoment (3 : Fin 10) 1 = 1 - meansOf row (3 : Fin 10) / topsOf row (3 : Fin 10) := by
  rw [factor03_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor03_gap_before"
  err.flush

theorem factor03_gap_value :
    gapEvaluator (prefixMoment (3 : Fin 10)) = (282001588349901055156018397722803104670015687840390878020176286849770289189 : ℚ) / 707553556923057425784444033670463438144892365953117755034696679424000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor03_moment1, factor03_moment2, factor03_moment3, factor03_moment4, factor03_moment5, factor03_moment6]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor03_saved_Q80_before"
  err.flush

theorem factor03_saved_Q80 :
    momentRow.factorFloorsQ80[3]! = factorFloorQ80 (prefixMoment (3 : Fin 10)) := by
  unfold factorFloorQ80
  rw [factor03_gap_value]
  decide +kernel

theorem factor03_Q80_lower :
    ((momentRow.factorFloorsQ80[3]! : ℤ) : ℚ) ≤
      gapEvaluator (prefixMoment (3 : Fin 10)) * (2 : ℚ)^80 := by
  rw [factor03_gap_value]
  decide +kernel

theorem factor03_Q80_upper :
    gapEvaluator (prefixMoment (3 : Fin 10)) * (2 : ℚ)^80 <
      ((momentRow.factorFloorsQ80[3]! : ℤ) : ℚ) + 1 := by
  rw [factor03_gap_value]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor03_complete"
  err.flush

#print axioms factor03_moment1
#print axioms factor03_moment2
#print axioms factor03_moment3
#print axioms factor03_moment4
#print axioms factor03_moment5
#print axioms factor03_moment6
#print axioms factor03_first_moment
#print axioms factor03_gap_value
#print axioms factor03_saved_Q80
#print axioms factor03_Q80_lower
#print axioms factor03_Q80_upper

end ImbalancedChen.P2OriginalSaving19Cell01Row000MomentFloor
