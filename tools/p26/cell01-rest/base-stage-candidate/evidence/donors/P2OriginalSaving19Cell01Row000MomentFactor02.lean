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
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor02_moment1_before"
  err.flush

theorem factor02_moment1 : prefixMoment (2 : Fin 10) 1 = (129924459799 : ℚ) / 993989031000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor02_moment2_before"
  err.flush

theorem factor02_moment2 : prefixMoment (2 : Fin 10) 2 = (37915898258617839729259 : ℚ) / 2173631226246301714200000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor02_moment3_before"
  err.flush

theorem factor02_moment3 : prefixMoment (2 : Fin 10) 3 = (512328326326703605506452995034209 : ℚ) / 216056559632790320823129694020000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor02_moment4_before"
  err.flush

theorem factor02_moment4 : prefixMoment (2 : Fin 10) 4 = (33274240844666847008049299244540341573665391 : ℚ) / 101521892893006638860912854192780430184000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor02_moment5_before"
  err.flush

theorem factor02_moment5 : prefixMoment (2 : Fin 10) 5 = (14294755819117829265700108196781211513245539052999432529 : ℚ) / 310807875661376803364811192080740409542620520048320000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor02_moment6_before"
  err.flush

theorem factor02_moment6 : prefixMoment (2 : Fin 10) 6 = (2021698456742613672973402349720132697806670426115990430586581275039 : ℚ) / 308939619155820412902466216314290033443812523923545669977920000000000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor02_first_moment_before"
  err.flush

theorem factor02_first_moment :
    prefixMoment (2 : Fin 10) 1 = 1 - meansOf row (2 : Fin 10) / topsOf row (2 : Fin 10) := by
  rw [factor02_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor02_gap_before"
  err.flush

theorem factor02_gap_value :
    gapEvaluator (prefixMoment (2 : Fin 10)) = (25318845759382897881087096217429929107412164963634088221417823304406331 : ℚ) / 107270701095770976702245213998017372723546015251231135409000000000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor02_moment1, factor02_moment2, factor02_moment3, factor02_moment4, factor02_moment5, factor02_moment6]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor02_saved_Q80_before"
  err.flush

theorem factor02_saved_Q80 :
    momentRow.factorFloorsQ80[2]! = factorFloorQ80 (prefixMoment (2 : Fin 10)) := by
  unfold factorFloorQ80
  rw [factor02_gap_value]
  decide +kernel

theorem factor02_Q80_lower :
    ((momentRow.factorFloorsQ80[2]! : ℤ) : ℚ) ≤
      gapEvaluator (prefixMoment (2 : Fin 10)) * (2 : ℚ)^80 := by
  rw [factor02_gap_value]
  decide +kernel

theorem factor02_Q80_upper :
    gapEvaluator (prefixMoment (2 : Fin 10)) * (2 : ℚ)^80 <
      ((momentRow.factorFloorsQ80[2]! : ℤ) : ℚ) + 1 := by
  rw [factor02_gap_value]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor02_complete"
  err.flush

#print axioms factor02_moment1
#print axioms factor02_moment2
#print axioms factor02_moment3
#print axioms factor02_moment4
#print axioms factor02_moment5
#print axioms factor02_moment6
#print axioms factor02_first_moment
#print axioms factor02_gap_value
#print axioms factor02_saved_Q80
#print axioms factor02_Q80_lower
#print axioms factor02_Q80_upper

end ImbalancedChen.P2OriginalSaving19Cell01Row000MomentFloor
