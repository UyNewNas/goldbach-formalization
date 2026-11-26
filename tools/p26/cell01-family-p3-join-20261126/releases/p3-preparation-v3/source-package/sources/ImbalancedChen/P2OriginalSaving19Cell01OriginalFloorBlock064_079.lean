import ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorInterface
import ImbalancedChen.P2OriginalSaving19Cell01Row064Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row065Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row066Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row067Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row068Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row069Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row070Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row071Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row072Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row073Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row074Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row075Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row076Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row077Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row078Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row079Finite
import Mathlib.Tactic.FinCases

/-!
SOURCE CANDIDATE / NOT COMPILED. Closed original rationalMoment/floor transports
for the original cell01 ordinals 64 through 79, in that order.
The original finite facts and raw bindings are imported unchanged. No encoded
moment arithmetic is recomputed, and no original floor target is a premise.
This is a 16-row block, not an assertion for all 144 rows or any integral.
-/
namespace ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock064_079

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19OriginalFloorTransport
open P2OriginalSaving19Cell01OriginalFloorInterface

namespace Row064

open P2OriginalSaving19Cell01Row064
open P2OriginalSaving19Cell01Row064MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW064_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (64 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (64 : Fin 144)) vertices
    (rawGeometryRow (64 : Fin 144)) row
    (rawMomentRow (64 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row064

namespace Row065

open P2OriginalSaving19Cell01Row065
open P2OriginalSaving19Cell01Row065MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW065_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (65 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (65 : Fin 144)) vertices
    (rawGeometryRow (65 : Fin 144)) row
    (rawMomentRow (65 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row065

namespace Row066

open P2OriginalSaving19Cell01Row066
open P2OriginalSaving19Cell01Row066MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW066_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (66 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (66 : Fin 144)) vertices
    (rawGeometryRow (66 : Fin 144)) row
    (rawMomentRow (66 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row066

namespace Row067

open P2OriginalSaving19Cell01Row067
open P2OriginalSaving19Cell01Row067MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW067_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (67 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (67 : Fin 144)) vertices
    (rawGeometryRow (67 : Fin 144)) row
    (rawMomentRow (67 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row067

namespace Row068

open P2OriginalSaving19Cell01Row068
open P2OriginalSaving19Cell01Row068MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW068_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (68 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (68 : Fin 144)) vertices
    (rawGeometryRow (68 : Fin 144)) row
    (rawMomentRow (68 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row068

namespace Row069

open P2OriginalSaving19Cell01Row069
open P2OriginalSaving19Cell01Row069MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW069_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (69 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (69 : Fin 144)) vertices
    (rawGeometryRow (69 : Fin 144)) row
    (rawMomentRow (69 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row069

namespace Row070

open P2OriginalSaving19Cell01Row070
open P2OriginalSaving19Cell01Row070MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW070_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (70 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (70 : Fin 144)) vertices
    (rawGeometryRow (70 : Fin 144)) row
    (rawMomentRow (70 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row070

namespace Row071

open P2OriginalSaving19Cell01Row071
open P2OriginalSaving19Cell01Row071MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW071_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (71 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (71 : Fin 144)) vertices
    (rawGeometryRow (71 : Fin 144)) row
    (rawMomentRow (71 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row071

namespace Row072

open P2OriginalSaving19Cell01Row072
open P2OriginalSaving19Cell01Row072MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW072_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (72 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (72 : Fin 144)) vertices
    (rawGeometryRow (72 : Fin 144)) row
    (rawMomentRow (72 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row072

namespace Row073

open P2OriginalSaving19Cell01Row073
open P2OriginalSaving19Cell01Row073MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW073_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (73 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (73 : Fin 144)) vertices
    (rawGeometryRow (73 : Fin 144)) row
    (rawMomentRow (73 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row073

namespace Row074

open P2OriginalSaving19Cell01Row074
open P2OriginalSaving19Cell01Row074MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW074_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (74 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (74 : Fin 144)) vertices
    (rawGeometryRow (74 : Fin 144)) row
    (rawMomentRow (74 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row074

namespace Row075

open P2OriginalSaving19Cell01Row075
open P2OriginalSaving19Cell01Row075MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW075_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (75 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (75 : Fin 144)) vertices
    (rawGeometryRow (75 : Fin 144)) row
    (rawMomentRow (75 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row075

namespace Row076

open P2OriginalSaving19Cell01Row076
open P2OriginalSaving19Cell01Row076MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW076_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (76 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (76 : Fin 144)) vertices
    (rawGeometryRow (76 : Fin 144)) row
    (rawMomentRow (76 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row076

namespace Row077

open P2OriginalSaving19Cell01Row077
open P2OriginalSaving19Cell01Row077MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW077_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (77 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (77 : Fin 144)) vertices
    (rawGeometryRow (77 : Fin 144)) row
    (rawMomentRow (77 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row077

namespace Row078

open P2OriginalSaving19Cell01Row078
open P2OriginalSaving19Cell01Row078MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW078_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (78 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (78 : Fin 144)) vertices
    (rawGeometryRow (78 : Fin 144)) row
    (rawMomentRow (78 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row078

namespace Row079

open P2OriginalSaving19Cell01Row079
open P2OriginalSaving19Cell01Row079MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW079_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (79 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (79 : Fin 144)) vertices
    (rawGeometryRow (79 : Fin 144)) row
    (rawMomentRow (79 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row079

/-- This map retains the original ordinal; it does not reorder the rows. -/
def originalOrdinal (i : Fin 16) : Fin 144 :=
  ⟨64 + i.val, by have hi := i.isLt; omega⟩

theorem originalOrdinal_value (i : Fin 16) :
    (originalOrdinal i).val = 64 + i.val := rfl

theorem all_original_floor_and_bounds (i : Fin 16) :
    OriginalFloorAndBoundsAt (originalOrdinal i) := by
  fin_cases i
  · exact Row064.raw_original_floor_and_bounds
  · exact Row065.raw_original_floor_and_bounds
  · exact Row066.raw_original_floor_and_bounds
  · exact Row067.raw_original_floor_and_bounds
  · exact Row068.raw_original_floor_and_bounds
  · exact Row069.raw_original_floor_and_bounds
  · exact Row070.raw_original_floor_and_bounds
  · exact Row071.raw_original_floor_and_bounds
  · exact Row072.raw_original_floor_and_bounds
  · exact Row073.raw_original_floor_and_bounds
  · exact Row074.raw_original_floor_and_bounds
  · exact Row075.raw_original_floor_and_bounds
  · exact Row076.raw_original_floor_and_bounds
  · exact Row077.raw_original_floor_and_bounds
  · exact Row078.raw_original_floor_and_bounds
  · exact Row079.raw_original_floor_and_bounds

#print axioms originalOrdinal_value
#print axioms all_original_floor_and_bounds

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_064_079_complete"
  err.flush

end ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock064_079
