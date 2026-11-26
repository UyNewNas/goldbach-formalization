import ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock000_015
import ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock016_031
import ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock032_047
import ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock048_063
import ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock064_079
import ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock080_095
import ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock096_111
import ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock112_127
import ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock128_143
import Mathlib.Tactic.FinCases

/-!
SOURCE CANDIDATE / NOT COMPILED. The original cell01 Fin 144 aggregation.
Every branch uses one closed 16-row block theorem at the original ordinal.
No floor target, arithmetic condition, moment identity, or integral bound is
assumed. No assertion of kernel acceptance follows from this candidate source.
-/
namespace ImbalancedChen.P2OriginalSaving19Cell01AllOriginalFloorBridge

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19OriginalFloorTransport
open P2OriginalSaving19Cell01OriginalFloorInterface

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ALL_ORIGINAL_FLOOR_before_144_branches"
  err.flush

/-- All original rows, without a smaller subset guard or a floor premise. -/
theorem all_original_floor_and_bounds :
    ∀ r : Fin 144, OriginalFloorAndBoundsAt r := by
  intro r
  fin_cases r
  · exact P2OriginalSaving19Cell01OriginalFloorBlock000_015.all_original_floor_and_bounds (0 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock000_015.all_original_floor_and_bounds (1 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock000_015.all_original_floor_and_bounds (2 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock000_015.all_original_floor_and_bounds (3 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock000_015.all_original_floor_and_bounds (4 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock000_015.all_original_floor_and_bounds (5 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock000_015.all_original_floor_and_bounds (6 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock000_015.all_original_floor_and_bounds (7 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock000_015.all_original_floor_and_bounds (8 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock000_015.all_original_floor_and_bounds (9 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock000_015.all_original_floor_and_bounds (10 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock000_015.all_original_floor_and_bounds (11 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock000_015.all_original_floor_and_bounds (12 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock000_015.all_original_floor_and_bounds (13 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock000_015.all_original_floor_and_bounds (14 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock000_015.all_original_floor_and_bounds (15 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock016_031.all_original_floor_and_bounds (0 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock016_031.all_original_floor_and_bounds (1 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock016_031.all_original_floor_and_bounds (2 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock016_031.all_original_floor_and_bounds (3 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock016_031.all_original_floor_and_bounds (4 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock016_031.all_original_floor_and_bounds (5 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock016_031.all_original_floor_and_bounds (6 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock016_031.all_original_floor_and_bounds (7 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock016_031.all_original_floor_and_bounds (8 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock016_031.all_original_floor_and_bounds (9 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock016_031.all_original_floor_and_bounds (10 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock016_031.all_original_floor_and_bounds (11 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock016_031.all_original_floor_and_bounds (12 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock016_031.all_original_floor_and_bounds (13 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock016_031.all_original_floor_and_bounds (14 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock016_031.all_original_floor_and_bounds (15 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock032_047.all_original_floor_and_bounds (0 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock032_047.all_original_floor_and_bounds (1 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock032_047.all_original_floor_and_bounds (2 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock032_047.all_original_floor_and_bounds (3 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock032_047.all_original_floor_and_bounds (4 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock032_047.all_original_floor_and_bounds (5 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock032_047.all_original_floor_and_bounds (6 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock032_047.all_original_floor_and_bounds (7 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock032_047.all_original_floor_and_bounds (8 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock032_047.all_original_floor_and_bounds (9 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock032_047.all_original_floor_and_bounds (10 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock032_047.all_original_floor_and_bounds (11 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock032_047.all_original_floor_and_bounds (12 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock032_047.all_original_floor_and_bounds (13 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock032_047.all_original_floor_and_bounds (14 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock032_047.all_original_floor_and_bounds (15 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock048_063.all_original_floor_and_bounds (0 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock048_063.all_original_floor_and_bounds (1 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock048_063.all_original_floor_and_bounds (2 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock048_063.all_original_floor_and_bounds (3 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock048_063.all_original_floor_and_bounds (4 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock048_063.all_original_floor_and_bounds (5 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock048_063.all_original_floor_and_bounds (6 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock048_063.all_original_floor_and_bounds (7 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock048_063.all_original_floor_and_bounds (8 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock048_063.all_original_floor_and_bounds (9 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock048_063.all_original_floor_and_bounds (10 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock048_063.all_original_floor_and_bounds (11 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock048_063.all_original_floor_and_bounds (12 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock048_063.all_original_floor_and_bounds (13 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock048_063.all_original_floor_and_bounds (14 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock048_063.all_original_floor_and_bounds (15 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock064_079.all_original_floor_and_bounds (0 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock064_079.all_original_floor_and_bounds (1 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock064_079.all_original_floor_and_bounds (2 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock064_079.all_original_floor_and_bounds (3 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock064_079.all_original_floor_and_bounds (4 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock064_079.all_original_floor_and_bounds (5 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock064_079.all_original_floor_and_bounds (6 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock064_079.all_original_floor_and_bounds (7 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock064_079.all_original_floor_and_bounds (8 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock064_079.all_original_floor_and_bounds (9 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock064_079.all_original_floor_and_bounds (10 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock064_079.all_original_floor_and_bounds (11 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock064_079.all_original_floor_and_bounds (12 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock064_079.all_original_floor_and_bounds (13 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock064_079.all_original_floor_and_bounds (14 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock064_079.all_original_floor_and_bounds (15 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock080_095.all_original_floor_and_bounds (0 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock080_095.all_original_floor_and_bounds (1 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock080_095.all_original_floor_and_bounds (2 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock080_095.all_original_floor_and_bounds (3 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock080_095.all_original_floor_and_bounds (4 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock080_095.all_original_floor_and_bounds (5 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock080_095.all_original_floor_and_bounds (6 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock080_095.all_original_floor_and_bounds (7 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock080_095.all_original_floor_and_bounds (8 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock080_095.all_original_floor_and_bounds (9 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock080_095.all_original_floor_and_bounds (10 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock080_095.all_original_floor_and_bounds (11 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock080_095.all_original_floor_and_bounds (12 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock080_095.all_original_floor_and_bounds (13 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock080_095.all_original_floor_and_bounds (14 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock080_095.all_original_floor_and_bounds (15 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock096_111.all_original_floor_and_bounds (0 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock096_111.all_original_floor_and_bounds (1 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock096_111.all_original_floor_and_bounds (2 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock096_111.all_original_floor_and_bounds (3 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock096_111.all_original_floor_and_bounds (4 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock096_111.all_original_floor_and_bounds (5 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock096_111.all_original_floor_and_bounds (6 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock096_111.all_original_floor_and_bounds (7 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock096_111.all_original_floor_and_bounds (8 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock096_111.all_original_floor_and_bounds (9 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock096_111.all_original_floor_and_bounds (10 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock096_111.all_original_floor_and_bounds (11 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock096_111.all_original_floor_and_bounds (12 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock096_111.all_original_floor_and_bounds (13 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock096_111.all_original_floor_and_bounds (14 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock096_111.all_original_floor_and_bounds (15 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock112_127.all_original_floor_and_bounds (0 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock112_127.all_original_floor_and_bounds (1 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock112_127.all_original_floor_and_bounds (2 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock112_127.all_original_floor_and_bounds (3 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock112_127.all_original_floor_and_bounds (4 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock112_127.all_original_floor_and_bounds (5 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock112_127.all_original_floor_and_bounds (6 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock112_127.all_original_floor_and_bounds (7 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock112_127.all_original_floor_and_bounds (8 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock112_127.all_original_floor_and_bounds (9 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock112_127.all_original_floor_and_bounds (10 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock112_127.all_original_floor_and_bounds (11 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock112_127.all_original_floor_and_bounds (12 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock112_127.all_original_floor_and_bounds (13 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock112_127.all_original_floor_and_bounds (14 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock112_127.all_original_floor_and_bounds (15 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock128_143.all_original_floor_and_bounds (0 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock128_143.all_original_floor_and_bounds (1 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock128_143.all_original_floor_and_bounds (2 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock128_143.all_original_floor_and_bounds (3 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock128_143.all_original_floor_and_bounds (4 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock128_143.all_original_floor_and_bounds (5 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock128_143.all_original_floor_and_bounds (6 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock128_143.all_original_floor_and_bounds (7 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock128_143.all_original_floor_and_bounds (8 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock128_143.all_original_floor_and_bounds (9 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock128_143.all_original_floor_and_bounds (10 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock128_143.all_original_floor_and_bounds (11 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock128_143.all_original_floor_and_bounds (12 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock128_143.all_original_floor_and_bounds (13 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock128_143.all_original_floor_and_bounds (14 : Fin 16)
  · exact P2OriginalSaving19Cell01OriginalFloorBlock128_143.all_original_floor_and_bounds (15 : Fin 16)

theorem all_original_floor_formula (r : Fin 144) :
    OriginalFloorChecksFor (rawGeometryRow r) (rawMomentRow r) (rawOriginalMoments r) :=
  (all_original_floor_and_bounds r).1

theorem all_original_Q80_bounds (r : Fin 144) :
    OriginalQ80BoundsFor (rawMomentRow r) (rawOriginalMoments r) :=
  (all_original_floor_and_bounds r).2

#print axioms all_original_floor_and_bounds
#print axioms all_original_floor_formula
#print axioms all_original_Q80_bounds

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ALL_ORIGINAL_FLOOR_144_branches_complete"
  err.flush

end ImbalancedChen.P2OriginalSaving19Cell01AllOriginalFloorBridge
