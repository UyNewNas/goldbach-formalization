import Lean
import ImbalancedChen.P2OriginalSaving16Q96FloorCore
import ImbalancedChen.P2OriginalSaving19SourceJson
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / NOT COMPILED / ZERO FORMAL CREDIT.

Mechanical relocation of exactly nine original saving16 decoder/schema
commands from P2OriginalSaving16FiniteArchive. All command bytes, field and
error strings, rational operations, and both deriving clauses are unchanged.
The original namespace, open declarations, noncomputable context and six
imports are retained conservatively. No decoder algorithm is rewritten.

This owner imports neither the finite archive nor OriginalInput. It reads no
witness and contains no theorem, closed guard or new assumption. Inhabited
records are data defaults only; they do not establish parse success or any
archive, geometry, Q96 or integral claim. The new owner and every generated
declaration still require actual strict compilation, replay and full audit.
-/
namespace ImbalancedChen.P2OriginalSaving16OriginalArchive

open Lean Elab Term
open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16JensenFloor (q96Floor)
open scoped BigOperators

noncomputable section

def parseInteger (s : String) : Except String Int :=
  match SourceJson.intChars s.toList with
  | some z => .ok z
  | none => .error "invalid original integer"

def parseRational (s : String) : Except String ℚ := do
  let chars := s.toList
  let numerator := chars.takeWhile (fun c => c != '/')
  match chars.dropWhile (fun c => c != '/') with
  | [] => return (← parseInteger (String.ofList numerator) : ℤ)
  | '/' :: denominator =>
    let n ← parseInteger (String.ofList numerator)
    let d ← parseInteger (String.ofList denominator)
    if d = 0 then throw "zero original rational denominator"
    return (n : ℚ) / (d : ℚ)
  | _ => throw "invalid original rational"

def rationalField (j : SourceJson) (key : String) : Except String ℚ := do
  parseRational (← j.getObjValAs? String key)

def rationalArray (j : SourceJson) : Except String (Array ℚ) := do
  (← j.getArr?).mapM fun v => do parseRational (← v.getStr?)

def rationalArrayField (j : SourceJson) (key : String) : Except String (Array ℚ) := do
  rationalArray (← j.getObjVal? key)

structure SimplexRecord where
  simplexId : Nat
  vertexIds : Array Nat
  physicalVolume : ℚ
  meanGap : ℚ
  factorMaxima : Array ℚ
  gapWeightedMeans : Array ℚ
  maxBound : ℚ
  jensenBound : ℚ
  maxFloor : ℤ
  jensenFloor : ℤ
  deriving Inhabited, DecidableEq

def decodeSimplex (j : SourceJson) : Except String SimplexRecord := do
  return {
    simplexId := ← j.getObjValAs? Nat "simplex_id"
    vertexIds := ← j.getObjValAs? (Array Nat) "vertex_ids"
    physicalVolume := ← rationalField j "physical_volume"
    meanGap := ← rationalField j "mean_gap"
    factorMaxima := ← rationalArrayField j "factor_maxima"
    gapWeightedMeans := ← rationalArrayField j "gap_weighted_means"
    maxBound := ← rationalField j "max_bound"
    jensenBound := ← rationalField j "jensen_bound"
    maxFloor := ← parseInteger (← j.getObjValAs? String "max_floor_Q96")
    jensenFloor := ← parseInteger (← j.getObjValAs? String "jensen_floor_Q96") }

/-- Geometry is retained in its original source order, including every
active-basis and face-ledger record. They are not treated as proof fields. -/
structure CellRecord where
  cellId : Nat
  dimension : Nat
  physicalJacobian : Nat
  leftMasks : Array Nat
  rightMasks : Array Nat
  facetOriginalIndices : Array Nat
  positiveNormalBalance : Array ℚ
  normalRank : Nat
  active8 : Array SourceJson
  vertices : Array (Array ℚ)
  vertexValues : Array SourceJson
  allOriginalMinima : Array ℚ
  facetVertices : Array (Array Nat)
  faceLedger : Array SourceJson
  simplices : Array SimplexRecord
  physicalVolume : ℚ
  integralGap : ℚ
  deriving Inhabited

def decodeCell (j : SourceJson) : Except String CellRecord := do
  return {
    cellId := ← j.getObjValAs? Nat "cell_id"
    dimension := ← j.getObjValAs? Nat "dimension"
    physicalJacobian := ← j.getObjValAs? Nat "physical_jacobian"
    leftMasks := ← j.getObjValAs? (Array Nat) "left_masks"
    rightMasks := ← j.getObjValAs? (Array Nat) "right_masks"
    facetOriginalIndices := ← j.getObjValAs? (Array Nat) "facet_original_indices"
    positiveNormalBalance := ← rationalArrayField j "positive_normal_balance"
    normalRank := ← j.getObjValAs? Nat "normal_rank"
    active8 := ← (← j.getObjVal? "active8_enumeration").getArr?
    vertices := ← (← (← j.getObjVal? "vertices").getArr?).mapM rationalArray
    vertexValues := ← (← j.getObjVal? "vertex_values").getArr?
    allOriginalMinima := ← rationalArrayField j "all_original_constraint_minima"
    facetVertices := ← j.getObjValAs? (Array (Array Nat)) "facet_vertices"
    faceLedger := ← (← j.getObjVal? "face_ledger").getArr?
    simplices := ← (← (← j.getObjVal? "simplices").getArr?).mapM decodeSimplex
    physicalVolume := ← rationalField j "physical_volume"
    integralGap := ← rationalField j "integral_gap" }

end
end ImbalancedChen.P2OriginalSaving16OriginalArchive
