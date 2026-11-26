import ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorInterface
import ImbalancedChen.P2OriginalSaving19Cell01Row016Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row017Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row018Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row019Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row020Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row021Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row022Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row023Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row024Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row025Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row026Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row027Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row028Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row029Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row030Finite
import ImbalancedChen.P2OriginalSaving19Cell01Row031Finite
import Mathlib.Tactic.FinCases

/-!
SOURCE CANDIDATE / NOT COMPILED. Closed original rationalMoment/floor transports
for the original cell01 ordinals 16 through 31, in that order.
The original finite facts and raw bindings are imported unchanged. No encoded
moment arithmetic is recomputed, and no original floor target is a premise.
This is a 16-row block, not an assertion for all 144 rows or any integral.
-/
namespace ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock016_031

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open P2OriginalSaving19OriginalFloorTransport
open P2OriginalSaving19Cell01OriginalFloorInterface

namespace Row016

open P2OriginalSaving19Cell01Row016
open P2OriginalSaving19Cell01Row016MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW016_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (16 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (16 : Fin 144)) vertices
    (rawGeometryRow (16 : Fin 144)) row
    (rawMomentRow (16 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row016

namespace Row017

open P2OriginalSaving19Cell01Row017
open P2OriginalSaving19Cell01Row017MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW017_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (17 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (17 : Fin 144)) vertices
    (rawGeometryRow (17 : Fin 144)) row
    (rawMomentRow (17 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row017

namespace Row018

open P2OriginalSaving19Cell01Row018
open P2OriginalSaving19Cell01Row018MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW018_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (18 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (18 : Fin 144)) vertices
    (rawGeometryRow (18 : Fin 144)) row
    (rawMomentRow (18 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row018

namespace Row019

open P2OriginalSaving19Cell01Row019
open P2OriginalSaving19Cell01Row019MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW019_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (19 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (19 : Fin 144)) vertices
    (rawGeometryRow (19 : Fin 144)) row
    (rawMomentRow (19 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row019

namespace Row020

open P2OriginalSaving19Cell01Row020
open P2OriginalSaving19Cell01Row020MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW020_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (20 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (20 : Fin 144)) vertices
    (rawGeometryRow (20 : Fin 144)) row
    (rawMomentRow (20 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row020

namespace Row021

open P2OriginalSaving19Cell01Row021
open P2OriginalSaving19Cell01Row021MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW021_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (21 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (21 : Fin 144)) vertices
    (rawGeometryRow (21 : Fin 144)) row
    (rawMomentRow (21 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row021

namespace Row022

open P2OriginalSaving19Cell01Row022
open P2OriginalSaving19Cell01Row022MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW022_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (22 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (22 : Fin 144)) vertices
    (rawGeometryRow (22 : Fin 144)) row
    (rawMomentRow (22 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row022

namespace Row023

open P2OriginalSaving19Cell01Row023
open P2OriginalSaving19Cell01Row023MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW023_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (23 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (23 : Fin 144)) vertices
    (rawGeometryRow (23 : Fin 144)) row
    (rawMomentRow (23 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row023

namespace Row024

open P2OriginalSaving19Cell01Row024
open P2OriginalSaving19Cell01Row024MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW024_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (24 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (24 : Fin 144)) vertices
    (rawGeometryRow (24 : Fin 144)) row
    (rawMomentRow (24 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row024

namespace Row025

open P2OriginalSaving19Cell01Row025
open P2OriginalSaving19Cell01Row025MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW025_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (25 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (25 : Fin 144)) vertices
    (rawGeometryRow (25 : Fin 144)) row
    (rawMomentRow (25 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row025

namespace Row026

open P2OriginalSaving19Cell01Row026
open P2OriginalSaving19Cell01Row026MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW026_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (26 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (26 : Fin 144)) vertices
    (rawGeometryRow (26 : Fin 144)) row
    (rawMomentRow (26 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row026

namespace Row027

open P2OriginalSaving19Cell01Row027
open P2OriginalSaving19Cell01Row027MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW027_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (27 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (27 : Fin 144)) vertices
    (rawGeometryRow (27 : Fin 144)) row
    (rawMomentRow (27 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row027

namespace Row028

open P2OriginalSaving19Cell01Row028
open P2OriginalSaving19Cell01Row028MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW028_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (28 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (28 : Fin 144)) vertices
    (rawGeometryRow (28 : Fin 144)) row
    (rawMomentRow (28 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row028

namespace Row029

open P2OriginalSaving19Cell01Row029
open P2OriginalSaving19Cell01Row029MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW029_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (29 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (29 : Fin 144)) vertices
    (rawGeometryRow (29 : Fin 144)) row
    (rawMomentRow (29 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row029

namespace Row030

open P2OriginalSaving19Cell01Row030
open P2OriginalSaving19Cell01Row030MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW030_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (30 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (30 : Fin 144)) vertices
    (rawGeometryRow (30 : Fin 144)) row
    (rawMomentRow (30 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row030

namespace Row031

open P2OriginalSaving19Cell01Row031
open P2OriginalSaving19Cell01Row031MomentFloor

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_ROW031_before_transport"
  err.flush

theorem typed_original_floor_and_bounds :
    OriginalFloorChecksFor row momentRow (originalMoments vertices row) ∧
      OriginalQ80BoundsFor momentRow (originalMoments vertices row) :=
  original_floor_and_bounds_of_encoding vertices row momentRow
    gapNats deviationNats deviationDenominators gapScale
    deviationDenominators_ne gapScale_ne gap_encoding deviation_encoding
    prefix_floor_checks all_Q80_bounds

theorem raw_original_floor_and_bounds : OriginalFloorAndBoundsAt (31 : Fin 144) :=
  original_floor_and_bounds_of_bindings (rawVertices (31 : Fin 144)) vertices
    (rawGeometryRow (31 : Fin 144)) row
    (rawMomentRow (31 : Fin 144)) momentRow
    (fun i j => raw_vertices_eq i j) raw_row_eq raw_moment_row_eq
    typed_original_floor_and_bounds

#print axioms typed_original_floor_and_bounds
#print axioms raw_original_floor_and_bounds

end Row031

/-- This map retains the original ordinal; it does not reorder the rows. -/
def originalOrdinal (i : Fin 16) : Fin 144 :=
  ⟨16 + i.val, by have hi := i.isLt; omega⟩

theorem originalOrdinal_value (i : Fin 16) :
    (originalOrdinal i).val = 16 + i.val := rfl

theorem all_original_floor_and_bounds (i : Fin 16) :
    OriginalFloorAndBoundsAt (originalOrdinal i) := by
  fin_cases i
  · exact Row016.raw_original_floor_and_bounds
  · exact Row017.raw_original_floor_and_bounds
  · exact Row018.raw_original_floor_and_bounds
  · exact Row019.raw_original_floor_and_bounds
  · exact Row020.raw_original_floor_and_bounds
  · exact Row021.raw_original_floor_and_bounds
  · exact Row022.raw_original_floor_and_bounds
  · exact Row023.raw_original_floor_and_bounds
  · exact Row024.raw_original_floor_and_bounds
  · exact Row025.raw_original_floor_and_bounds
  · exact Row026.raw_original_floor_and_bounds
  · exact Row027.raw_original_floor_and_bounds
  · exact Row028.raw_original_floor_and_bounds
  · exact Row029.raw_original_floor_and_bounds
  · exact Row030.raw_original_floor_and_bounds
  · exact Row031.raw_original_floor_and_bounds

#print axioms originalOrdinal_value
#print axioms all_original_floor_and_bounds

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ORIGINAL_BLOCK_016_031_complete"
  err.flush

end ImbalancedChen.P2OriginalSaving19Cell01OriginalFloorBlock016_031
