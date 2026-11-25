import ImbalancedChen.P2OriginalSaving19MomentFloorConsumer
import ImbalancedChen.P2OriginalSaving19SourceJson
import ImbalancedChen.P2OriginalSaving19ArchivePackedInputs
import ImbalancedChen.P2OriginalSaving19SourceJsonCharInput

/-!
SOURCE CANDIDATE, NOT COMPILED OR ACCEPTED. New input representation, requiring
fresh Core acceptance. The old v2 Core object/export acceptance is not reused.
All 26 original files are quoted separately by their data owners; Core only
assembles already quoted complete characters. SourceJson.parse and every typed
schema/decoder below retain the v2 source bodies. The new parse_ofList bridges
preserve the entire parser result; they assert no concrete parse success.
-/
namespace ImbalancedChen.P2OriginalSaving19Archive

set_option maxRecDepth 1000000

noncomputable def geometryText : Fin 13 → String :=
  fun c => String.ofList (geometryChars c)

noncomputable def momentText : Fin 13 → String :=
  fun c => String.ofList (momentChars c)

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

noncomputable def geometryParse (c : Fin 13) : Except String Geometry :=
  SourceJson.parse (geometryText c) >>= decodeGeometry

noncomputable def momentParse (c : Fin 13) : Except String Moments :=
  SourceJson.parse (momentText c) >>= decodeMoments

noncomputable def geometry (c : Fin 13) : Geometry := (geometryParse c).toOption.getD default
noncomputable def moments (c : Fin 13) : Moments := (momentParse c).toOption.getD default

/-- Exact input-representation bridge, including unchanged typed decoding.
This does not discharge a parse-success, shape, or numerical obligation. -/
theorem geometryParse_eq_parseChars (c : Fin 13) :
    geometryParse c = (SourceJson.parseChars (geometryChars c) >>= decodeGeometry) :=
  congrArg (fun result => result >>= decodeGeometry)
    (SourceJson.parse_ofList (geometryChars c))

theorem momentParse_eq_parseChars (c : Fin 13) :
    momentParse c = (SourceJson.parseChars (momentChars c) >>= decodeMoments) :=
  congrArg (fun result => result >>= decodeMoments)
    (SourceJson.parse_ofList (momentChars c))

end ImbalancedChen.P2OriginalSaving19Archive
