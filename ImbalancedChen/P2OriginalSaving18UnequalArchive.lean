import Lean
import ImbalancedChen.P2OriginalFull87PullingCell
import ImbalancedChen.P4AOriginalFull87ArchiveSourceIndex

/-! Literal primitive inputs of the fifteen unequal-parent moment certificates.
The local order is the original source order 9-00..9-10,9seed,9-12,50A,50D.
Nine family member 11 is represented by the sole original seed witness. -/
namespace ImbalancedChen.P2OriginalSaving18UnequalArchive
open Lean Elab Term
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary
open P2OriginalSaving19Archive
  (SourceJson Geometry MomentRecord decodeGeometry decodeMomentRecord parseInteger)
open P2OriginalSaving16OriginalArchive (QPoint evalQ)
open P2OriginalFull87PullingCell (Data Checks rowVertices)

elab "originalUnequalText% " nm:str : term => do
  let raw ← liftIO <| IO.FS.readFile ("../goldbach-research/" ++ nm.getString)
  elabTerm (Syntax.mkStrLit raw) (some (mkConst ``String))

noncomputable section
inductive Kind where | nine (i : Fin 13) | fiftyA | fiftyD deriving DecidableEq, Fintype

def originalCell : Kind → Cell
  | .nine i => .remaining (.nine i)
  | .fiftyA => .remaining .fiftyA
  | .fiftyD => .remaining .fiftyD

def geometricText : Kind → String
  | .nine i => ![originalUnequalText% "eighth-unequal-parent-nine-20261009-family-cell-00.witness.json",
    originalUnequalText% "eighth-unequal-parent-nine-20261009-family-cell-01.witness.json",
    originalUnequalText% "eighth-unequal-parent-nine-20261009-family-cell-02.witness.json",
    originalUnequalText% "eighth-unequal-parent-nine-20261009-family-cell-03.witness.json",
    originalUnequalText% "eighth-unequal-parent-nine-20261009-family-cell-04.witness.json",
    originalUnequalText% "eighth-unequal-parent-nine-20261009-family-cell-05.witness.json",
    originalUnequalText% "eighth-unequal-parent-nine-20261009-family-cell-06.witness.json",
    originalUnequalText% "eighth-unequal-parent-nine-20261009-family-cell-07.witness.json",
    originalUnequalText% "eighth-unequal-parent-nine-20261009-family-cell-08.witness.json",
    originalUnequalText% "eighth-unequal-parent-nine-20261009-family-cell-09.witness.json",
    originalUnequalText% "eighth-unequal-parent-nine-20261009-family-cell-10.witness.json",
    originalUnequalText% "eighth-unequal-parent-nine-20261009-minorant-cell.witness.json",
    originalUnequalText% "eighth-unequal-parent-nine-20261009-family-cell-12.witness.json"] i
  | .fiftyA => originalUnequalText% "eighth-unequal-parent-fifty-20261009.witness.json"
  | .fiftyD => originalUnequalText% "eighth-unequal-parent-fifty-desc-20261009.witness.json"

def momentText : Kind → String
  | .nine i => ![originalUnequalText% "eighth-unequal-moment-refinement-20261009-9-00.witness.json",
    originalUnequalText% "eighth-unequal-moment-refinement-20261009-9-01.witness.json",
    originalUnequalText% "eighth-unequal-moment-refinement-20261009-9-02.witness.json",
    originalUnequalText% "eighth-unequal-moment-refinement-20261009-9-03.witness.json",
    originalUnequalText% "eighth-unequal-moment-refinement-20261009-9-04.witness.json",
    originalUnequalText% "eighth-unequal-moment-refinement-20261009-9-05.witness.json",
    originalUnequalText% "eighth-unequal-moment-refinement-20261009-9-06.witness.json",
    originalUnequalText% "eighth-unequal-moment-refinement-20261009-9-07.witness.json",
    originalUnequalText% "eighth-unequal-moment-refinement-20261009-9-08.witness.json",
    originalUnequalText% "eighth-unequal-moment-refinement-20261009-9-09.witness.json",
    originalUnequalText% "eighth-unequal-moment-refinement-20261009-9-10.witness.json",
    originalUnequalText% "eighth-unequal-moment-refinement-20261009-9seed.witness.json",
    originalUnequalText% "eighth-unequal-moment-refinement-20261009-9-12.witness.json"] i
  | .fiftyA => originalUnequalText% "eighth-unequal-moment-refinement-20261009-50A.witness.json"
  | .fiftyD => originalUnequalText% "eighth-unequal-moment-refinement-20261009-50D.witness.json"

structure Moments where
  dim : ℕ
  perSimplex : ℕ
  factorCount : ℕ
  logDegree : ℕ
  expDegree : ℕ
  denomLog : ℤ
  denomFinal : ℤ
  rows : Array MomentRecord
  deriving Inhabited

def decodeMoments (j : SourceJson) : Except String Moments := do
  return {
    dim := ← j.getObjValAs? Nat "dimension"
    perSimplex := ← j.getObjValAs? Nat "vertices_per_simplex"
    factorCount := ← j.getObjValAs? Nat "factor_count"
    logDegree := ← j.getObjValAs? Nat "log_degree"
    expDegree := ← j.getObjValAs? Nat "exp_degree"
    denomLog := ← parseInteger (← j.getObjValAs? String "log_floor_denominator")
    denomFinal := ← parseInteger (← j.getObjValAs? String "final_floor_denominator")
    rows := ← (← (← j.getObjVal? "records").getArr?).mapM decodeMomentRecord }

def geometryParse (c : Kind) : Except String Geometry := SourceJson.parse (geometricText c) >>= decodeGeometry
def momentParse (c : Kind) : Except String Moments := SourceJson.parse (momentText c) >>= decodeMoments
def geometry (c : Kind) := (geometryParse c).toOption.getD default
def moments (c : Kind) := (momentParse c).toOption.getD default
def data (c : Kind) : Data := ⟨(geometry c).vertices, (geometry c).facetVertices,
  (geometry c).faces, (geometry c).rows.map (·.vertexIds)⟩

abbrev Row (c : Kind) := Fin (data c).rows.size
def momentRow (c : Kind) (s : Row c) := (moments c).rows.getD s.val default
def geometryRow (c : Kind) (s : Row c) := (geometry c).rows.getD s.val default

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem original_parse_tags : ∀ c, (geometryParse c).toOption.isSome = true ∧
    (momentParse c).toOption.isSome = true := by decide

theorem geometry_parsed (c : Kind) : geometryParse c = .ok (geometry c) := by
  cases h : geometryParse c with
  | ok a => simp [geometry,h]
  | error e => have hh := (original_parse_tags c).1; simp [h] at hh

theorem moments_parsed (c : Kind) : momentParse c = .ok (moments c) := by
  cases h : momentParse c with
  | ok a => simp [moments,h]
  | error e => have hh := (original_parse_tags c).2; simp [h] at hh

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem original_headers : ∀ c, (geometry c).dimension = 8 ∧ (geometry c).physicalJacobian = 1 ∧
    (moments c).dim = 8 ∧ (moments c).perSimplex = 9 ∧ (moments c).factorCount = 10 ∧
    (moments c).logDegree = 6 ∧ (moments c).expDegree = 3 ∧ (moments c).denomLog = 2^80 ∧
    (moments c).denomFinal = 2^96 ∧ (moments c).rows.size = (data c).rows.size ∧
    ∀ s : Row c, (momentRow c s).simplexId = s.val ∧
      (geometryRow c s).simplexId = s.val ∧ (momentRow c s).factorFloorsQ80.size = 10 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem original_geometry : ∀ c : Kind, Checks (originalCell c) (data c) := by decide

abbrev Affine := Fin 9 → ℚ
def R : Kind → Affine
  | .nine _ => ![1/2,1/2,0,0,1/2,0,0,0,0]
  | .fiftyA => ![1/2,0,1/2,0,0,1/2,1/2,0,0]
  | .fiftyD => ![57/64,0,-3/2,0,0,-3/2,-3/2,0,0]
def M : Kind → Affine
  | .nine _ => ![1/2-1/1000000,0,1/2,0,1/2,0,0,0,1/2]
  | .fiftyA => ![1/2-1/1000000,0,0,0,1/2,1/2,1/2,0,1/2]
  | .fiftyD => ![57/64-1/1000000,0,-3/2,-3/2,0,0,0,0,-3/2]
def coord (j : Fin 8) : Affine := Pi.single j.succ 1
def totalRow : Affine := ∑ j : Fin 8, coord j
def gapRow (c : Kind) : Affine := M c - R c
def factors (c : Kind) : Fin 10 → Affine :=
  ![R c - totalRow, M c - totalRow, coord 0, coord 1, coord 2, coord 3, coord 4, coord 5, coord 6, coord 7]

def gapsQ (c : Kind) (s : Row c) (i : Fin 9) := evalQ (gapRow c) (rowVertices (data c) s i)
def factorsQ (c : Kind) (s : Row c) (i : Fin 9) (j : Fin 10) :=
  evalQ (factors c j) (rowVertices (data c) s i)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem original_positive_inputs : ∀ (c : Kind) (s : Row c),
    (∀ i, 0 ≤ gapsQ c s i) ∧ 0 < ∑ i, gapsQ c s i ∧
    ∀ i j, (53/13824 : ℚ) ≤ factorsQ c s i j := by decide

def selectedQ (c : Kind) : ℚ := (P4AOriginalFull87ArchiveSourceIndex.archivedRecordForOriginalCell (originalCell c)).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem original_selected_records : ∀ c, selectedQ c =
    ∑ s : Row c, ((momentRow c s).newFloorQ96 : ℚ)/(2 : ℚ)^96 := by decide

theorem original_stage18_total : (∑ c : Kind, selectedQ c) =
    (1033407531585213315823239 : ℚ)/2^96 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem original_stage18_count : (∑ c : Kind, (data c).rows.size) = 60820 := by decide

end
end ImbalancedChen.P2OriginalSaving18UnequalArchive
