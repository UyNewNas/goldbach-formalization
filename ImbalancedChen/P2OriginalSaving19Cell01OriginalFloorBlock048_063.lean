import ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorInterface
import ImbalancedChen.P2OriginalSaving19Cell01Row048Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row049Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row050Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row051Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row052Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row053Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row054Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row055Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row056Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row057Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row058Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row059Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row060Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row061Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row062Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row063Finite
import Mathlib.Tactic.FinCases

/-!
SOURCE CANDIDATE / NOT COMPILED. Closed original rationalMoment/floor transports
for the original cell01 ordinals 48 through 63, in that order.
The original finite facts and raw bindings are imported unchanged. No encoded
moment arithmetic is recomputed, and no original floor target is a premise.
This is a 16-row block, not an assertion for all 144 rows or any integral.
-/
namespace ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock048_063

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19OriginalFloorTransport
open P2OriginalSaving19Cell01OriginalFloorInterface

namespace Row048

open P2OriginalSaving19Cell01Row048
open P2OriginalSaving19Cell01Row048MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW048_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (48 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (48 : Fin 144)) vertices
    (rawGeometryRow (48 : Fin 144)) row
    (rawMomentRow (48 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row048

namespace Row049

open P2OriginalSaving19Cell01Row049
open P2OriginalSaving19Cell01Row049MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW049_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (49 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (49 : Fin 144)) vertices
    (rawGeometryRow (49 : Fin 144)) row
    (rawMomentRow (49 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row049

namespace Row050

open P2OriginalSaving19Cell01Row050
open P2OriginalSaving19Cell01Row050MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW050_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (50 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (50 : Fin 144)) vertices
    (rawGeometryRow (50 : Fin 144)) row
    (rawMomentRow (50 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row050

namespace Row051

open P2OriginalSaving19Cell01Row051
open P2OriginalSaving19Cell01Row051MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW051_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (51 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (51 : Fin 144)) vertices
    (rawGeometryRow (51 : Fin 144)) row
    (rawMomentRow (51 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row051

namespace Row052

open P2OriginalSaving19Cell01Row052
open P2OriginalSaving19Cell01Row052MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW052_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (52 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (52 : Fin 144)) vertices
    (rawGeometryRow (52 : Fin 144)) row
    (rawMomentRow (52 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row052

namespace Row053

open P2OriginalSaving19Cell01Row053
open P2OriginalSaving19Cell01Row053MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW053_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (53 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (53 : Fin 144)) vertices
    (rawGeometryRow (53 : Fin 144)) row
    (rawMomentRow (53 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row053

namespace Row054

open P2OriginalSaving19Cell01Row054
open P2OriginalSaving19Cell01Row054MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW054_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (54 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (54 : Fin 144)) vertices
    (rawGeometryRow (54 : Fin 144)) row
    (rawMomentRow (54 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row054

namespace Row055

open P2OriginalSaving19Cell01Row055
open P2OriginalSaving19Cell01Row055MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW055_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (55 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (55 : Fin 144)) vertices
    (rawGeometryRow (55 : Fin 144)) row
    (rawMomentRow (55 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row055

namespace Row056

open P2OriginalSaving19Cell01Row056
open P2OriginalSaving19Cell01Row056MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW056_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (56 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (56 : Fin 144)) vertices
    (rawGeometryRow (56 : Fin 144)) row
    (rawMomentRow (56 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row056

namespace Row057

open P2OriginalSaving19Cell01Row057
open P2OriginalSaving19Cell01Row057MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW057_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (57 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (57 : Fin 144)) vertices
    (rawGeometryRow (57 : Fin 144)) row
    (rawMomentRow (57 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row057

namespace Row058

open P2OriginalSaving19Cell01Row058
open P2OriginalSaving19Cell01Row058MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW058_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (58 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (58 : Fin 144)) vertices
    (rawGeometryRow (58 : Fin 144)) row
    (rawMomentRow (58 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row058

namespace Row059

open P2OriginalSaving19Cell01Row059
open P2OriginalSaving19Cell01Row059MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW059_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (59 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (59 : Fin 144)) vertices
    (rawGeometryRow (59 : Fin 144)) row
    (rawMomentRow (59 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row059

namespace Row060

open P2OriginalSaving19Cell01Row060
open P2OriginalSaving19Cell01Row060MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW060_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (60 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (60 : Fin 144)) vertices
    (rawGeometryRow (60 : Fin 144)) row
    (rawMomentRow (60 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row060

namespace Row061

open P2OriginalSaving19Cell01Row061
open P2OriginalSaving19Cell01Row061MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW061_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (61 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (61 : Fin 144)) vertices
    (rawGeometryRow (61 : Fin 144)) row
    (rawMomentRow (61 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row061

namespace Row062

open P2OriginalSaving19Cell01Row062
open P2OriginalSaving19Cell01Row062MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW062_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (62 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (62 : Fin 144)) vertices
    (rawGeometryRow (62 : Fin 144)) row
    (rawMomentRow (62 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row062

namespace Row063

open P2OriginalSaving19Cell01Row063
open P2OriginalSaving19Cell01Row063MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW063_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (63 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (63 : Fin 144)) vertices
    (rawGeometryRow (63 : Fin 144)) row
    (rawMomentRow (63 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row063

/-- This map retains the original ordinal; it does not reorder the rows. -/
def originalOrdinal (i : Fin 16) : Fin 144 :=
  ⟨48 + i.val, by have hi := i.isLt; omega⟩

theorem originalOrdinal_value (i : Fin 16) :
    (originalOrdinal i).val = 48 + i.val := rfl

theorem all_original_floor_and_bounds (i : Fin 16) :
    OriginalFloorAndBoundsAt (originalOrdinal i) := by
  fin_cases i
  · exact Row048.raw_original_floor_and_bounds
  · exact Row049.raw_original_floor_and_bounds
  · exact Row050.raw_original_floor_and_bounds
  · exact Row051.raw_original_floor_and_bounds
  · exact Row052.raw_original_floor_and_bounds
  · exact Row053.raw_original_floor_and_bounds
  · exact Row054.raw_original_floor_and_bounds
  · exact Row055.raw_original_floor_and_bounds
  · exact Row056.raw_original_floor_and_bounds
  · exact Row057.raw_original_floor_and_bounds
  · exact Row058.raw_original_floor_and_bounds
  · exact Row059.raw_original_floor_and_bounds
  · exact Row060.raw_original_floor_and_bounds
  · exact Row061.raw_original_floor_and_bounds
  · exact Row062.raw_original_floor_and_bounds
  · exact Row063.raw_original_floor_and_bounds

#print axioms originalOrdinal_value
#print axioms all_original_floor_and_bounds

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_048_063_complete"
  err.flush

end ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock048_063
