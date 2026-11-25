import ImbalancedChen.P2OriginalSaving19MomentFloorConsumer
import ImbalancedChen.P2OriginalSaving19SourceJson

/-!
SOURCE ONLY. UNCOMPILED. ZERO FORMAL CREDIT. All closed guards below are
UNEVALUATED. Only the user may compile this module and execute its loader.

The loader performs exactly one operation: read the named ORIGINAL file as
text and emit a String literal. It computes no determinant, moment, floor,
proof, or source digest. The pure decoders below and the closed kernel
proofs establish the connection between those literal strings and the
typed archive. No external checker result or hash equality is a premise.
Run user compilation from the goldbach-proof-continuation repository root.
-/

namespace ImbalancedChen.P2OriginalSaving19Archive

set_option maxRecDepth 1000000

open Lean Elab Term

elab "originalGeometryText% " n:num : term => do
  let c := n.getNat
  unless c < 13 do throwError "original cell must be in 0..12"
  let suffix := if c < 10 then "0" ++ toString c else toString c
  let p := "../goldbach-research/eighth-third-minorant-extension-20261009-a23-s23_low-" ++
    suffix ++ "-cell.witness.json"
  let s ← liftIO <| IO.FS.readFile p
  elabTerm (Syntax.mkStrLit s) (some (mkConst ``String))

elab "originalMomentText% " n:num : term => do
  let c := n.getNat
  unless c < 13 do throwError "original cell must be in 0..12"
  let suffix := if c < 10 then "0" ++ toString c else toString c
  let p := "../goldbach-research/eighth-third-moment-refinement-20261009-a23-low-" ++
    suffix ++ ".witness.json"
  let s ← liftIO <| IO.FS.readFile p
  elabTerm (Syntax.mkStrLit s) (some (mkConst ``String))

def geometryText : Fin 13 → String :=
  ![originalGeometryText% 0, originalGeometryText% 1, originalGeometryText% 2,
    originalGeometryText% 3, originalGeometryText% 4, originalGeometryText% 5,
    originalGeometryText% 6, originalGeometryText% 7, originalGeometryText% 8,
    originalGeometryText% 9, originalGeometryText% 10, originalGeometryText% 11,
    originalGeometryText% 12]

def momentText : Fin 13 → String :=
  ![originalMomentText% 0, originalMomentText% 1, originalMomentText% 2,
    originalMomentText% 3, originalMomentText% 4, originalMomentText% 5,
    originalMomentText% 6, originalMomentText% 7, originalMomentText% 8,
    originalMomentText% 9, originalMomentText% 10, originalMomentText% 11,
    originalMomentText% 12]

def parseInteger (s : String) : Except String Int :=
  match SourceJson.intChars s.toList with
  | some z => .ok z
  | none => .error "invalid original integer"

def parseRational (s : String) : Except String ℚ := do
  let xs := s.toList
  let ns := xs.takeWhile (fun c => c != '/')
  match xs.drop ns.length with
  | [] => return (← parseInteger (String.ofList ns) : ℤ)
  | '/' :: ds =>
    let u ← parseInteger (String.ofList ns)
    let v ← parseInteger (String.ofList ds)
    if v = 0 then throw "zero original denominator"
    return (u : ℚ) / (v : ℚ)
  | _ => throw "invalid original rational"

def jsonRational (j : SourceJson) : Except String ℚ := do
  parseRational (← j.getStr?)

def rationalField (j : SourceJson) (key : String) : Except String ℚ := do
  jsonRational (← j.getObjVal? key)

def rationalArray (j : SourceJson) : Except String (Array ℚ) := do
  (← j.getArr?).mapM jsonRational

def rationalArrayField (j : SourceJson) (key : String) : Except String (Array ℚ) := do
  rationalArray (← j.getObjVal? key)

structure VertexValues where
  gap : ℚ
  factors : Array ℚ
  deriving Inhabited, DecidableEq

def decodeVertexValues (j : SourceJson) : Except String VertexValues := do
  return ⟨← rationalField j "gap", ← rationalArrayField j "factors"⟩

structure GeometryRow where
  simplexId : Nat
  vertexIds : Array Nat
  physicalVolume : ℚ
  meanGap : ℚ
  factorMaxima : Array ℚ
  gapWeightedMeans : Array ℚ
  jensenBound : ℚ
  jensenFloorQ96 : Int
  deriving Inhabited, DecidableEq

def decodeGeometryRow (j : SourceJson) : Except String GeometryRow := do
  return {
    simplexId := ← j.getObjValAs? Nat "simplex_id"
    vertexIds := ← j.getObjValAs? (Array Nat) "vertex_ids"
    physicalVolume := ← rationalField j "physical_volume"
    meanGap := ← rationalField j "mean_gap"
    factorMaxima := ← rationalArrayField j "factor_maxima"
    gapWeightedMeans := ← rationalArrayField j "gap_weighted_means"
    jensenBound := ← rationalField j "jensen_bound"
    jensenFloorQ96 := ← parseInteger (← j.getObjValAs? String "jensen_floor_Q96") }

/-- Exact face records are retained for the separate ownership task.
No pulling/coverage/disjointness theorem is asserted in this module. -/
structure FaceRecord where
  vertices : Array Nat
  dimension : Nat
  pivot : Nat
  facetSets : Array (Array Nat)
  simplices : Nat
  deriving Inhabited, DecidableEq

def decodeFace (j : SourceJson) : Except String FaceRecord := do
  return {
    vertices := ← j.getObjValAs? (Array Nat) "vertices"
    dimension := ← j.getObjValAs? Nat "dimension"
    pivot := ← j.getObjValAs? Nat "pivot"
    facetSets := ← j.getObjValAs? (Array (Array Nat)) "facet_sets"
    simplices := ← j.getObjValAs? Nat "simplices" }

structure Geometry where
  dimension : Nat
  physicalJacobian : Nat
  vertices : Array (Array ℚ)
  vertexValues : Array VertexValues
  rows : Array GeometryRow
  facetOriginalIndices : Array Nat
  facetVertices : Array (Array Nat)
  faces : Array FaceRecord
  deriving Inhabited, DecidableEq

def decodeGeometry (j : SourceJson) : Except String Geometry := do
  return {
    dimension := ← j.getObjValAs? Nat "dimension"
    physicalJacobian := ← j.getObjValAs? Nat "physical_jacobian"
    vertices := ← (← (← j.getObjVal? "vertices").getArr?).mapM rationalArray
    vertexValues := ← (← (← j.getObjVal? "vertex_values").getArr?).mapM decodeVertexValues
    rows := ← (← (← j.getObjVal? "simplices").getArr?).mapM decodeGeometryRow
    facetOriginalIndices := ← j.getObjValAs? (Array Nat) "facet_original_indices"
    facetVertices := ← j.getObjValAs? (Array (Array Nat)) "facet_vertices"
    faces := ← (← (← j.getObjVal? "face_ledger").getArr?).mapM decodeFace }

structure MomentRecord where
  simplexId : Nat
  factorFloorsQ80 : Array Int
  oldFloorQ96 : Int
  newFloorQ96 : Int
  deriving Inhabited, DecidableEq

def decodeMomentRecord (j : SourceJson) : Except String MomentRecord := do
  let strings ← j.getObjValAs? (Array String) "log_gap_factor_floors_Q80"
  return {
    simplexId := ← j.getObjValAs? Nat "simplex_id"
    factorFloorsQ80 := ← strings.mapM parseInteger
    oldFloorQ96 := ← parseInteger (← j.getObjValAs? String "old_floor_Q96")
    newFloorQ96 := ← parseInteger (← j.getObjValAs? String "new_floor_Q96") }

structure Moments where
  cellId : Nat
  sourceWitness : String
  dimension : Nat
  verticesPerSimplex : Nat
  factorCount : Nat
  logDegree : Nat
  expDegree : Nat
  logDenominator : Int
  finalDenominator : Int
  rows : Array MomentRecord
  deriving Inhabited, DecidableEq

def decodeMoments (j : SourceJson) : Except String Moments := do
  return {
    cellId := ← j.getObjValAs? Nat "cell_id"
    sourceWitness := ← j.getObjValAs? String "source_witness"
    dimension := ← j.getObjValAs? Nat "dimension"
    verticesPerSimplex := ← j.getObjValAs? Nat "vertices_per_simplex"
    factorCount := ← j.getObjValAs? Nat "factor_count"
    logDegree := ← j.getObjValAs? Nat "log_degree"
    expDegree := ← j.getObjValAs? Nat "exp_degree"
    logDenominator := ← parseInteger (← j.getObjValAs? String "log_floor_denominator")
    finalDenominator := ← parseInteger (← j.getObjValAs? String "final_floor_denominator")
    rows := ← (← (← j.getObjVal? "records").getArr?).mapM decodeMomentRecord }

def geometryParse (c : Fin 13) : Except String Geometry :=
  SourceJson.parse (geometryText c) >>= decodeGeometry

def momentParse (c : Fin 13) : Except String Moments :=
  SourceJson.parse (momentText c) >>= decodeMoments

def geometry (c : Fin 13) : Geometry := (geometryParse c).toOption.getD default
def moments (c : Fin 13) : Moments := (momentParse c).toOption.getD default

/-!
DIAGNOSTIC CANDIDATE ONLY. The byte-identical original prefix ends above,
including both loaders, all thirteen geometry/moment strings, the pure
decoders and the typed geometry/moments definitions. The original general
parse-success, cell-shape and row-shape guards are deliberately outside
this diagnostic module. This file has not been compiled.
-/

end ImbalancedChen.P2OriginalSaving19Archive
