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
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor01_moment1_before"
  err.flush

theorem factor01_moment1 : prefixMoment (1 : Fin 10) 1 = (440685361133 : ℚ) / 2897236141800 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor01_moment2_before"
  err.flush

theorem factor01_moment2 : prefixMoment (1 : Fin 10) 2 = (462083181168022697263051 : ℚ) / 18466749974974729355928000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor01_moment3_before"
  err.flush

theorem factor01_moment3 : prefixMoment (1 : Fin 10) 3 = (47471291410413813981887415877211809 : ℚ) / 10700507089816206286333607535718080000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor01_moment4_before"
  err.flush

theorem factor01_moment4 : prefixMoment (1 : Fin 10) 4 = (68126124139537426039105935387138823193361220021 : ℚ) / 80604929278126894087538226627594065058429734400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor01_moment5_before"
  err.flush

theorem factor01_moment5 : prefixMoment (1 : Fin 10) 5 = (11278933146327695422651996555177060072833271745908438333703 : ℚ) / 65388824007310222091959015288872503250609683472647326617600000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor01_moment6_before"
  err.flush

theorem factor01_moment6 : prefixMoment (1 : Fin 10) 6 = (7118269464286697957004930078580910611232535759110570427739317221475391 : ℚ) / 189446864183778682849408462259260183789904357842011966401659867975680000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor01_first_moment_before"
  err.flush

theorem factor01_first_moment :
    prefixMoment (1 : Fin 10) 1 = 1 - meansOf row (1 : Fin 10) / topsOf row (1 : Fin 10) := by
  rw [factor01_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor01_gap_before"
  err.flush

theorem factor01_gap_value :
    gapEvaluator (prefixMoment (1 : Fin 10)) = (798533439813214905148570530822200714166126007173045016556056034219916498871 : ℚ) / 592021450574308383904401444560188074343451118256287395005187087424000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor01_moment1, factor01_moment2, factor01_moment3, factor01_moment4, factor01_moment5, factor01_moment6]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor01_saved_Q80_before"
  err.flush

theorem factor01_saved_Q80 :
    momentRow.factorFloorsQ80[1]! = factorFloorQ80 (prefixMoment (1 : Fin 10)) := by
  unfold factorFloorQ80
  rw [factor01_gap_value]
  decide +kernel

theorem factor01_Q80_lower :
    ((momentRow.factorFloorsQ80[1]! : ℤ) : ℚ) ≤
      gapEvaluator (prefixMoment (1 : Fin 10)) * (2 : ℚ)^80 := by
  rw [factor01_gap_value]
  decide +kernel

theorem factor01_Q80_upper :
    gapEvaluator (prefixMoment (1 : Fin 10)) * (2 : ℚ)^80 <
      ((momentRow.factorFloorsQ80[1]! : ℤ) : ℚ) + 1 := by
  rw [factor01_gap_value]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor01_complete"
  err.flush

#print axioms factor01_moment1
#print axioms factor01_moment2
#print axioms factor01_moment3
#print axioms factor01_moment4
#print axioms factor01_moment5
#print axioms factor01_moment6
#print axioms factor01_first_moment
#print axioms factor01_gap_value
#print axioms factor01_saved_Q80
#print axioms factor01_Q80_lower
#print axioms factor01_Q80_upper

end ImbalancedChen.P2OriginalSaving19Cell01Row000MomentFloor
