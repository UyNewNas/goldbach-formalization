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
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor00_moment1_before"
  err.flush

theorem factor00_moment1 : prefixMoment (0 : Fin 10) 1 = (468977592653 : ℚ) / 2897236141800 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor00_moment2_before"
  err.flush

theorem factor00_moment2 : prefixMoment (0 : Fin 10) 2 = (515957322048527686863691 : ℚ) / 18466749974974729355928000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor00_moment3_before"
  err.flush

theorem factor00_moment3 : prefixMoment (0 : Fin 10) 3 = (54957780057794762008107465995627569 : ℚ) / 10700507089816206286333607535718080000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor00_moment4_before"
  err.flush

theorem factor00_moment4 : prefixMoment (0 : Fin 10) 4 = (80977507542953469211442351409765160550194145461 : ℚ) / 80604929278126894087538226627594065058429734400000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor00_moment5_before"
  err.flush

theorem factor00_moment5 : prefixMoment (0 : Fin 10) 5 = (13657630876678659894044635103222641073315089459265856219623 : ℚ) / 65388824007310222091959015288872503250609683472647326617600000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor00_moment6_before"
  err.flush

theorem factor00_moment6 : prefixMoment (0 : Fin 10) 6 = (8728341230223819730362447902595445795308896287137520723149055169277631 : ℚ) / 189446864183778682849408462259260183789904357842011966401659867975680000000 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor00_first_moment_before"
  err.flush

theorem factor00_first_moment :
    prefixMoment (0 : Fin 10) 1 = 1 - meansOf row (0 : Fin 10) / topsOf row (0 : Fin 10) := by
  rw [factor00_moment1]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor00_gap_before"
  err.flush

theorem factor00_gap_value :
    gapEvaluator (prefixMoment (0 : Fin 10)) = (752341720215405007206986705008399271479084523295922076075637104501689839511 : ℚ) / 592021450574308383904401444560188074343451118256287395005187087424000000000000 := by
  unfold gapEvaluator
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [factor00_moment1, factor00_moment2, factor00_moment3, factor00_moment4, factor00_moment5, factor00_moment6]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor00_saved_Q80_before"
  err.flush

theorem factor00_saved_Q80 :
    momentRow.factorFloorsQ80[0]! = factorFloorQ80 (prefixMoment (0 : Fin 10)) := by
  unfold factorFloorQ80
  rw [factor00_gap_value]
  decide +kernel

theorem factor00_Q80_lower :
    ((momentRow.factorFloorsQ80[0]! : ℤ) : ℚ) ≤
      gapEvaluator (prefixMoment (0 : Fin 10)) * (2 : ℚ)^80 := by
  rw [factor00_gap_value]
  decide +kernel

theorem factor00_Q80_upper :
    gapEvaluator (prefixMoment (0 : Fin 10)) * (2 : ℚ)^80 <
      ((momentRow.factorFloorsQ80[0]! : ℤ) : ℚ) + 1 := by
  rw [factor00_gap_value]
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT factor00_complete"
  err.flush

#print axioms factor00_moment1
#print axioms factor00_moment2
#print axioms factor00_moment3
#print axioms factor00_moment4
#print axioms factor00_moment5
#print axioms factor00_moment6
#print axioms factor00_first_moment
#print axioms factor00_gap_value
#print axioms factor00_saved_Q80
#print axioms factor00_Q80_lower
#print axioms factor00_Q80_upper

end ImbalancedChen.P2OriginalSaving19Cell01Row000MomentFloor
