import ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorInterface
import ImbalancedChen.P2OriginalSaving19Cell01Row000OriginalFloorBridge
import ImbalancedChen.P2OriginalSaving19Cell01Row001Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row002Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row003Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row004Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row005Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row006Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row007Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row008Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row009Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row010Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row011Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row012Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row013Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row014Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row015Finite
import Mathlib.Tactic.FinCases

/-!
SOURCE CANDIDATE / NOT COMPILED. Closed original rationalMoment/floor transports
for the original cell01 ordinals 0 through 15, in that order.
The original finite facts and raw bindings are imported unchanged. No encoded
moment arithmetic is recomputed, and no original floor target is a premise.
This is a 16-row block, not an assertion for all 144 rows or any integral.
-/
namespace ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock000_015

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19OriginalFloorTransport
open P2OriginalSaving19Cell01OriginalFloorInterface

namespace Row000

open P2OriginalSaving19Cell01Row000
open P2OriginalSaving19Cell01Row000MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW000_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  ⟨P2OriginalSaving19Cell01Row000OriginalFloorBridge.original_floor_formula,
    P2OriginalSaving19Cell01Row000OriginalFloorBridge.original_Q80_bounds⟩

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (0 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (0 : Fin 144)) vertices
    (rawGeometryRow (0 : Fin 144)) row
    (rawMomentRow (0 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row000

namespace Row001

open P2OriginalSaving19Cell01Row001
open P2OriginalSaving19Cell01Row001MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW001_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (1 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (1 : Fin 144)) vertices
    (rawGeometryRow (1 : Fin 144)) row
    (rawMomentRow (1 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row001

namespace Row002

open P2OriginalSaving19Cell01Row002
open P2OriginalSaving19Cell01Row002MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW002_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (2 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (2 : Fin 144)) vertices
    (rawGeometryRow (2 : Fin 144)) row
    (rawMomentRow (2 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row002

namespace Row003

open P2OriginalSaving19Cell01Row003
open P2OriginalSaving19Cell01Row003MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW003_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (3 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (3 : Fin 144)) vertices
    (rawGeometryRow (3 : Fin 144)) row
    (rawMomentRow (3 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row003

namespace Row004

open P2OriginalSaving19Cell01Row004
open P2OriginalSaving19Cell01Row004MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW004_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (4 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (4 : Fin 144)) vertices
    (rawGeometryRow (4 : Fin 144)) row
    (rawMomentRow (4 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row004

namespace Row005

open P2OriginalSaving19Cell01Row005
open P2OriginalSaving19Cell01Row005MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW005_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (5 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (5 : Fin 144)) vertices
    (rawGeometryRow (5 : Fin 144)) row
    (rawMomentRow (5 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row005

namespace Row006

open P2OriginalSaving19Cell01Row006
open P2OriginalSaving19Cell01Row006MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW006_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (6 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (6 : Fin 144)) vertices
    (rawGeometryRow (6 : Fin 144)) row
    (rawMomentRow (6 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row006

namespace Row007

open P2OriginalSaving19Cell01Row007
open P2OriginalSaving19Cell01Row007MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW007_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (7 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (7 : Fin 144)) vertices
    (rawGeometryRow (7 : Fin 144)) row
    (rawMomentRow (7 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row007

namespace Row008

open P2OriginalSaving19Cell01Row008
open P2OriginalSaving19Cell01Row008MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW008_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (8 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (8 : Fin 144)) vertices
    (rawGeometryRow (8 : Fin 144)) row
    (rawMomentRow (8 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row008

namespace Row009

open P2OriginalSaving19Cell01Row009
open P2OriginalSaving19Cell01Row009MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW009_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (9 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (9 : Fin 144)) vertices
    (rawGeometryRow (9 : Fin 144)) row
    (rawMomentRow (9 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row009

namespace Row010

open P2OriginalSaving19Cell01Row010
open P2OriginalSaving19Cell01Row010MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW010_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (10 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (10 : Fin 144)) vertices
    (rawGeometryRow (10 : Fin 144)) row
    (rawMomentRow (10 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row010

namespace Row011

open P2OriginalSaving19Cell01Row011
open P2OriginalSaving19Cell01Row011MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW011_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (11 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (11 : Fin 144)) vertices
    (rawGeometryRow (11 : Fin 144)) row
    (rawMomentRow (11 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row011

namespace Row012

open P2OriginalSaving19Cell01Row012
open P2OriginalSaving19Cell01Row012MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW012_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (12 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (12 : Fin 144)) vertices
    (rawGeometryRow (12 : Fin 144)) row
    (rawMomentRow (12 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row012

namespace Row013

open P2OriginalSaving19Cell01Row013
open P2OriginalSaving19Cell01Row013MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW013_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (13 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (13 : Fin 144)) vertices
    (rawGeometryRow (13 : Fin 144)) row
    (rawMomentRow (13 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row013

namespace Row014

open P2OriginalSaving19Cell01Row014
open P2OriginalSaving19Cell01Row014MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW014_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (14 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (14 : Fin 144)) vertices
    (rawGeometryRow (14 : Fin 144)) row
    (rawMomentRow (14 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row014

namespace Row015

open P2OriginalSaving19Cell01Row015
open P2OriginalSaving19Cell01Row015MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW015_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (15 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (15 : Fin 144)) vertices
    (rawGeometryRow (15 : Fin 144)) row
    (rawMomentRow (15 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row015

/-- This map retains the original ordinal; it does not reorder the rows. -/
def originalOrdinal (i : Fin 16) : Fin 144 :=
  ⟨0 + i.val, by have hi := i.isLt; omega⟩

theorem originalOrdinal_value (i : Fin 16) :
    (originalOrdinal i).val = 0 + i.val := rfl

theorem all_original_floor_and_bounds (i : Fin 16) :
    OriginalFloorAndBoundsAt (originalOrdinal i) := by
  fin_cases i
  · exact Row000.raw_original_floor_and_bounds
  · exact Row001.raw_original_floor_and_bounds
  · exact Row002.raw_original_floor_and_bounds
  · exact Row003.raw_original_floor_and_bounds
  · exact Row004.raw_original_floor_and_bounds
  · exact Row005.raw_original_floor_and_bounds
  · exact Row006.raw_original_floor_and_bounds
  · exact Row007.raw_original_floor_and_bounds
  · exact Row008.raw_original_floor_and_bounds
  · exact Row009.raw_original_floor_and_bounds
  · exact Row010.raw_original_floor_and_bounds
  · exact Row011.raw_original_floor_and_bounds
  · exact Row012.raw_original_floor_and_bounds
  · exact Row013.raw_original_floor_and_bounds
  · exact Row014.raw_original_floor_and_bounds
  · exact Row015.raw_original_floor_and_bounds

#print axioms originalOrdinal_value
#print axioms all_original_floor_and_bounds

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_000_015_complete"
  err.flush

end ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock000_015
