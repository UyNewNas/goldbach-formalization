import ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorInterface
import ImbalancedChen.P2OriginalSaving19Cell01Row128Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row129Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row130Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row131Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row132Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row133Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row134Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row135Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row136Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row137Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row138Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row139Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row140Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row141Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row142Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row143Finite
import Mathlib.Tactic.FinCases

/-!
SOURCE CANDIDATE / NOT COMPILED. Closed original rationalMoment/floor transports
for the original cell01 ordinals 128 through 143, in that order.
The original finite facts and raw bindings are imported unchanged. No encoded
moment arithmetic is recomputed, and no original floor target is a premise.
This is a 16-row block, not an assertion for all 144 rows or any integral.
-/
namespace ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock128_143

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19OriginalFloorTransport
open P2OriginalSaving19Cell01OriginalFloorInterface

namespace Row128

open P2OriginalSaving19Cell01Row128
open P2OriginalSaving19Cell01Row128MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW128_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (128 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (128 : Fin 144)) vertices
    (rawGeometryRow (128 : Fin 144)) row
    (rawMomentRow (128 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row128

namespace Row129

open P2OriginalSaving19Cell01Row129
open P2OriginalSaving19Cell01Row129MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW129_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (129 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (129 : Fin 144)) vertices
    (rawGeometryRow (129 : Fin 144)) row
    (rawMomentRow (129 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row129

namespace Row130

open P2OriginalSaving19Cell01Row130
open P2OriginalSaving19Cell01Row130MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW130_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (130 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (130 : Fin 144)) vertices
    (rawGeometryRow (130 : Fin 144)) row
    (rawMomentRow (130 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row130

namespace Row131

open P2OriginalSaving19Cell01Row131
open P2OriginalSaving19Cell01Row131MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW131_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (131 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (131 : Fin 144)) vertices
    (rawGeometryRow (131 : Fin 144)) row
    (rawMomentRow (131 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row131

namespace Row132

open P2OriginalSaving19Cell01Row132
open P2OriginalSaving19Cell01Row132MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW132_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (132 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (132 : Fin 144)) vertices
    (rawGeometryRow (132 : Fin 144)) row
    (rawMomentRow (132 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row132

namespace Row133

open P2OriginalSaving19Cell01Row133
open P2OriginalSaving19Cell01Row133MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW133_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (133 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (133 : Fin 144)) vertices
    (rawGeometryRow (133 : Fin 144)) row
    (rawMomentRow (133 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row133

namespace Row134

open P2OriginalSaving19Cell01Row134
open P2OriginalSaving19Cell01Row134MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW134_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (134 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (134 : Fin 144)) vertices
    (rawGeometryRow (134 : Fin 144)) row
    (rawMomentRow (134 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row134

namespace Row135

open P2OriginalSaving19Cell01Row135
open P2OriginalSaving19Cell01Row135MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW135_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (135 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (135 : Fin 144)) vertices
    (rawGeometryRow (135 : Fin 144)) row
    (rawMomentRow (135 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row135

namespace Row136

open P2OriginalSaving19Cell01Row136
open P2OriginalSaving19Cell01Row136MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW136_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (136 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (136 : Fin 144)) vertices
    (rawGeometryRow (136 : Fin 144)) row
    (rawMomentRow (136 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row136

namespace Row137

open P2OriginalSaving19Cell01Row137
open P2OriginalSaving19Cell01Row137MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW137_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (137 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (137 : Fin 144)) vertices
    (rawGeometryRow (137 : Fin 144)) row
    (rawMomentRow (137 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row137

namespace Row138

open P2OriginalSaving19Cell01Row138
open P2OriginalSaving19Cell01Row138MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW138_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (138 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (138 : Fin 144)) vertices
    (rawGeometryRow (138 : Fin 144)) row
    (rawMomentRow (138 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row138

namespace Row139

open P2OriginalSaving19Cell01Row139
open P2OriginalSaving19Cell01Row139MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW139_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (139 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (139 : Fin 144)) vertices
    (rawGeometryRow (139 : Fin 144)) row
    (rawMomentRow (139 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row139

namespace Row140

open P2OriginalSaving19Cell01Row140
open P2OriginalSaving19Cell01Row140MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW140_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (140 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (140 : Fin 144)) vertices
    (rawGeometryRow (140 : Fin 144)) row
    (rawMomentRow (140 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row140

namespace Row141

open P2OriginalSaving19Cell01Row141
open P2OriginalSaving19Cell01Row141MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW141_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (141 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (141 : Fin 144)) vertices
    (rawGeometryRow (141 : Fin 144)) row
    (rawMomentRow (141 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row141

namespace Row142

open P2OriginalSaving19Cell01Row142
open P2OriginalSaving19Cell01Row142MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW142_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (142 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (142 : Fin 144)) vertices
    (rawGeometryRow (142 : Fin 144)) row
    (rawMomentRow (142 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row142

namespace Row143

open P2OriginalSaving19Cell01Row143
open P2OriginalSaving19Cell01Row143MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW143_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (143 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (143 : Fin 144)) vertices
    (rawGeometryRow (143 : Fin 144)) row
    (rawMomentRow (143 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row143

/-- This map retains the original ordinal; it does not reorder the rows. -/
def originalOrdinal (i : Fin 16) : Fin 144 :=
  ⟨128 + i.val, by have hi := i.isLt; omega⟩

theorem originalOrdinal_value (i : Fin 16) :
    (originalOrdinal i).val = 128 + i.val := rfl

theorem all_original_floor_and_bounds (i : Fin 16) :
    OriginalFloorAndBoundsAt (originalOrdinal i) := by
  fin_cases i
  · exact Row128.raw_original_floor_and_bounds
  · exact Row129.raw_original_floor_and_bounds
  · exact Row130.raw_original_floor_and_bounds
  · exact Row131.raw_original_floor_and_bounds
  · exact Row132.raw_original_floor_and_bounds
  · exact Row133.raw_original_floor_and_bounds
  · exact Row134.raw_original_floor_and_bounds
  · exact Row135.raw_original_floor_and_bounds
  · exact Row136.raw_original_floor_and_bounds
  · exact Row137.raw_original_floor_and_bounds
  · exact Row138.raw_original_floor_and_bounds
  · exact Row139.raw_original_floor_and_bounds
  · exact Row140.raw_original_floor_and_bounds
  · exact Row141.raw_original_floor_and_bounds
  · exact Row142.raw_original_floor_and_bounds
  · exact Row143.raw_original_floor_and_bounds

#print axioms originalOrdinal_value
#print axioms all_original_floor_and_bounds

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_128_143_complete"
  err.flush

end ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock128_143
