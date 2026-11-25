import Lean
import ImbalancedChen.P2OriginalSaving16Q96FloorCore
import ImbalancedChen.P2OriginalSaving19SourceJson
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / NOT COMPILED / ZERO FORMAL CREDIT.

Mechanical relocation of the original saving16 archive's 37 source commands:
35 named declarations, the original text-reader elaborator, and its original
simplex-validity Decidable instance. Their namespace, declaration text, pure
parser, rational operations, separate Q96 floors, and closed proof bodies
are unchanged. The original owner retains the actual atlas and closure
bridge declarations and imports this module.

The reader still reads all fourteen ORIGINAL texts from
../goldbach-research at user compilation, and emits only String literals.
No JSON parsing, determinant evaluation, numerical generation, or theorem
construction has been performed during this extraction. The existing
39,741-simplex checks and aggregate guards remain UNEVALUATED. Their truth,
elaboration, kernel reduction, memory use, and runtime are not certified.

This finite layer imports no project atlas or custom native dependency.
It does not establish the real-integral or source-ownership endpoint.
-/
namespace ImbalancedChen.P2OriginalSaving16OriginalArchive

open Lean Elab Term
open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16JensenFloor (q96Floor)
open scoped BigOperators

elab "originalSaving16Text% " n:num : term => do
  let c := n.getNat
  unless c < 15 && c != 7 do
    throwError "saving16 selects source IDs0..14 except7"
  let suffix := if c < 10 then "0" ++ toString c else toString c
  let path := "../goldbach-research/eighth-prefix-family-20261009-cell-" ++
    suffix ++ ".witness.json"
  let raw ← IO.FS.readFile path
  elabTerm (Syntax.mkStrLit raw) (some (mkConst ``String))

noncomputable section

def originalText : Fin 14 → String :=
  ![originalSaving16Text% 0, originalSaving16Text% 1, originalSaving16Text% 2,
    originalSaving16Text% 3, originalSaving16Text% 4, originalSaving16Text% 5,
    originalSaving16Text% 6, originalSaving16Text% 8, originalSaving16Text% 9,
    originalSaving16Text% 10, originalSaving16Text% 11, originalSaving16Text% 12,
    originalSaving16Text% 13, originalSaving16Text% 14]

def originalId : Fin 14 → Nat := ![0,1,2,3,4,5,6,8,9,10,11,12,13,14]

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

def parsedCell (i : Fin 14) : Except String CellRecord := do
  decodeCell (← SourceJson.parse (originalText i))

/-- The default is not evidence. The next closed statement rules it out
for every actual source text, including absent fields and parse errors. -/
def archive (i : Fin 14) : CellRecord := (parsedCell i).toOption.getD default

/-- Inspect only the Except constructor. Deciding this Bool does not
require decidable equality of CellRecord or the retained raw SourceJson
trees. It still executes the full pure parser and decoder at reduction. -/
def parsedCellSuccess (i : Fin 14) : Bool :=
  match parsedCell i with
  | .ok _ => true
  | .error _ => false

/-- Diagnostic only: the unchanged parser and decoder on original cell 00. -/
theorem cell00_parse_success_diagnostic :
    parsedCellSuccess (0 : Fin 14) = true := by
  decide +kernel

end
end ImbalancedChen.P2OriginalSaving16OriginalArchive
