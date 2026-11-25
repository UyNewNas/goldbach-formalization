import Lean
import ImbalancedChen.P2OriginalSaving16JensenFloor
import ImbalancedChen.P2OriginalSaving19SourceJson
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

All fourteen ORIGINAL witness texts are read only at USER compilation.
The elaborator emits only ordinary String literals. It parses no JSON,
computes no determinant or floor, and manufactures no theorem. The shared
fuel-recursive SourceJson parser and all decoders/checks below are pure.
Lean.Json.parse (which uses partial recursion) is deliberately not used.

Every finite theorem body below is UNEVALUATED. Truth, elaboration and
kernel resource feasibility are unverified. In particular Matrix.det on
39,741 rational8x8 matrices can be expensive; no feasibility claim is made.
These are proposed closed proofterms, not accepted historical PASS flags.

Compile from the repository root after installing the registered source
modules. Original files remain at ../goldbach-research. No archive text was
exported or expanded while authoring this source.
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
  let raw ← liftIO <| IO.FS.readFile path
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

/-- Closed original-file parse-success guard, UNEVALUATED. No parse
success premise or external PASS record is introduced. -/
theorem original_parse_success_tag : ∀ i : Fin 14, parsedCellSuccess i = true := by
  decide

/-- Recover the exact decoded record by constructor elimination, without
an equality test on any record or JSON payload. -/
theorem original_parse_success : ∀ i : Fin 14, parsedCell i = .ok (archive i) := by
  intro i
  cases h : parsedCell i with
  | error message =>
      have hs := original_parse_success_tag i
      simp [parsedCellSuccess, h] at hs
  | ok record =>
      simp [archive, h]

abbrev QPoint := Fin 8 → ℚ
def point (c : CellRecord) (v : Nat) : QPoint := fun j => (c.vertices.getD v #[]).getD j.val 0
def simplexVertices (c : CellRecord) (r : SimplexRecord) : Fin 9 → QPoint :=
  fun i => point c (r.vertexIds.getD i.val 0)

def comparisonQ (t : QPoint) : ℚ := 57 / 64 - (3 / 2) * (t 1 + t 2)
def capQ (t : QPoint) : ℚ := (1 + (t 0 + t 7)) / 2 - 1 / 1000000
def gapQ (t : QPoint) : ℚ := capQ t - comparisonQ t
def factorsQ (t : QPoint) : Fin 10 → ℚ :=
  ![comparisonQ t - ∑ i, t i, capQ t - ∑ i, t i,
    t 0, t 1, t 2, t 3, t 4, t 5, t 6, t 7]
def gapTotalQ (v : Fin 9 → QPoint) : ℚ := ∑ i : Fin 9, gapQ (v i)
def meansQ (v : Fin 9 → QPoint) (j : Fin 10) : ℚ :=
  ((∑ i : Fin 9, factorsQ (v i) j) +
    (∑ i : Fin 9, gapQ (v i) * factorsQ (v i) j) / gapTotalQ v) / 10
def edgeMatrix (v : Fin 9 → QPoint) : Matrix (Fin 8) (Fin 8) ℚ :=
  fun i j => v i.succ j - v 0 j
def physicalVolumeQ (v : Fin 9 → QPoint) : ℚ := |(edgeMatrix v).det| / 8.factorial
def jensenQ (v : Fin 9 → QPoint) : ℚ :=
  4 * physicalVolumeQ v * (gapTotalQ v / 9) / ∏ j : Fin 10, meansQ v j

def simplexValid (c : CellRecord) (s : Fin c.simplices.size) : Prop :=
  let r := c.simplices[s]
  let v := simplexVertices c r
  r.simplexId = s.val ∧ r.vertexIds.size = 9 ∧
  (∀ k : Fin 9, r.vertexIds.getD k.val 0 < c.vertices.size) ∧
  0 < physicalVolumeQ v ∧ 0 < gapTotalQ v ∧
  r.physicalVolume = physicalVolumeQ v ∧ r.meanGap = gapTotalQ v / 9 ∧
  r.gapWeightedMeans.size = 10 ∧
  (∀ j : Fin 10, r.gapWeightedMeans.getD j.val 0 = meansQ v j) ∧
  r.jensenBound = jensenQ v ∧ r.jensenFloor = q96Floor (jensenQ v)

instance (c : CellRecord) (s : Fin c.simplices.size) : Decidable (simplexValid c s) :=
  inferInstanceAs (Decidable (let r := c.simplices[s]; let v := simplexVertices c r;
    r.simplexId = s.val ∧ r.vertexIds.size = 9 ∧
    (∀ k : Fin 9, r.vertexIds.getD k.val 0 < c.vertices.size) ∧
    0 < physicalVolumeQ v ∧ 0 < gapTotalQ v ∧
    r.physicalVolume = physicalVolumeQ v ∧ r.meanGap = gapTotalQ v / 9 ∧
    r.gapWeightedMeans.size = 10 ∧
    (∀ j : Fin 10, r.gapWeightedMeans.getD j.val 0 = meansQ v j) ∧
    r.jensenBound = jensenQ v ∧ r.jensenFloor = q96Floor (jensenQ v)))

theorem original_simplex_operations : ∀ (i : Fin 14) (s : Fin (archive i).simplices.size),
    simplexValid (archive i) s := by decide

open P2OriginalAscendingEighthCapDictionary
open P2OriginalSaving16FourteenPhysicalAtlas
open P2OriginalSaving16CellOwnership

def atlasCell (i : Fin 14) : Cell :=
  if h : i.val < 3 then .inl ⟨i.val, h⟩ else .inr ⟨i.val - 3, by omega⟩

theorem atlasCell_sourceId (i : Fin 14) : (sourceId (atlasCell i)).val = originalId i := by
  fin_cases i <;> decide

def evalQ (a : Fin 9 → ℚ) (x : QPoint) : ℚ := a 0 + ∑ j : Fin 8, a j.succ * x j
def castPoint (x : QPoint) : Point := fun j => (x j : ℝ)

/-- A deterministic rational interior candidate derived from the first
original nondegenerate simplex. Its strictness is checked below, not
inferred from any floating navigation margin. -/
def interiorCandidate (c : CellRecord) : QPoint := fun j =>
  (∑ k : Fin 9, simplexVertices c (c.simplices.getD 0 default) k j) / 9

theorem original_headers : ∀ i : Fin 14,
    (archive i).cellId = originalId i ∧ (archive i).dimension = 8 ∧
    (archive i).physicalJacobian = 1 ∧
    (∀ v : Fin (archive i).vertices.size, ((archive i).vertices[v]).size = 8) ∧
    0 < (archive i).simplices.size := by decide

theorem original_patterns : ∀ i : Fin 14,
    (archive i).leftMasks.toList.toFinset =
      P4AOriginalAscending14Literal42.literalLeftMasks (sourceId (atlasCell i)) ∧
    Disjoint (archive i).leftMasks.toList.toFinset (archive i).rightMasks.toList.toFinset ∧
    (archive i).leftMasks.toList.toFinset ∪ (archive i).rightMasks.toList.toFinset =
      Finset.Icc 1 63 ∧ 6 ∈ (archive i).rightMasks.toList.toFinset := by decide

theorem original_strict_centers : ∀ (i : Fin 14) (k : Fin 96),
    0 < evalQ (rows (atlasCell i) k).2 (interiorCandidate (archive i)) := by decide

theorem original_vertices_all96 : ∀ (i : Fin 14) (v : Fin (archive i).vertices.size)
    (k : Fin 96), 0 ≤ evalQ (rows (atlasCell i) k).2 (point (archive i) v.val) := by decide

theorem evalQ_cast (a : Fin 9 → ℚ) (x : QPoint) :
    evalRow a (castPoint x) = (evalQ a x : ℝ) := by
  simp [evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine, castPoint, evalQ,
    Rat.cast_sum, Rat.cast_add, Rat.cast_mul]

/-- Concrete original vertices lie in the closure of their own96-row
source cell. No candidate-facet equality or completeness premise occurs. -/
theorem original_vertex_mem_closure (i : Fin 14) (v : Fin (archive i).vertices.size) :
    castPoint (point (archive i) v.val) ∈ closure (cell (atlasCell i)) := by
  apply closedRows_mem_closure (atlasCell i) (castPoint (interiorCandidate (archive i)))
  · intro k
    rw [evalQ_cast]
    exact_mod_cast original_strict_centers i k
  · intro k
    rw [evalQ_cast]
    exact_mod_cast original_vertices_all96 i v k

theorem original_facet_indices : ∀ (i : Fin 14)
    (f : Fin (archive i).facetOriginalIndices.size),
    (archive i).facetOriginalIndices[f] < 96 := by decide

theorem original_positive_normal_balance : ∀ i : Fin 14,
    (archive i).positiveNormalBalance.size = (archive i).facetOriginalIndices.size ∧
    (∀ f : Fin (archive i).facetOriginalIndices.size,
      0 < (archive i).positiveNormalBalance.getD f.val 0) ∧
    ∀ j : Fin 8,
      (∑ f : Fin (archive i).facetOriginalIndices.size,
        (archive i).positiveNormalBalance.getD f.val 0 *
          (rows (atlasCell i)
            ⟨(archive i).facetOriginalIndices[f], original_facet_indices i f⟩).2 j.succ) = 0 := by
  decide

/-- The exact original facet IDs and vertex incidence are checked against
the actual96 physical rows. The full active-basis/face-pulling theorem is
still absent: this result must not be described as a triangulation proof. -/
theorem original_facet_incidence : ∀ (i : Fin 14),
    (archive i).facetOriginalIndices.size = (archive i).facetVertices.size ∧
    ∀ (f : Fin (archive i).facetOriginalIndices.size)
      (v : Fin (archive i).vertices.size),
        (v.val ∈ ((archive i).facetVertices.getD f.val #[]).toList ↔
          evalQ (rows (atlasCell i)
            ⟨(archive i).facetOriginalIndices[f], original_facet_indices i f⟩).2
              (point (archive i) v.val) = 0) := by
  decide

def cellFloorNumerator (i : Fin 14) : ℤ :=
  ∑ s : Fin (archive i).simplices.size,
    q96Floor (jensenQ (simplexVertices (archive i) (archive i).simplices[s]))

def aggregateNumerator : ℤ := ∑ i : Fin 14, cellFloorNumerator i
def historicalNumerator : ℤ := 1222997719565324892497827

/-- Pure, closed ORIGINAL-operation comparison. It sums39,741 separate
floors; it neither floors their sum nor reads a reported gain as proof.
This is UNEVALUATED, with truth and resources unverified. -/
theorem original_q96_aggregate : aggregateNumerator = historicalNumerator := by decide

theorem original_counts :
    (∑ i : Fin 14, (archive i).simplices.size) = 39741 ∧
    (∑ i : Fin 14, (archive i).active8.size) = 39381 := by decide

/-- Arithmetic endpoint only, not the source-region integral theorem. -/
theorem original_q96_aggregate_real :
    (∑ i : Fin 14, (cellFloorNumerator i : ℝ) / (2 : ℝ) ^ 96) =
      (1222997719565324892497827 : ℝ) / (2 : ℝ) ^ 96 := by
  rw [← Finset.sum_div]
  have h := congrArg (fun z : ℤ => (z : ℝ)) original_q96_aggregate
  simpa [aggregateNumerator, historicalNumerator] using
    congrArg (fun x : ℝ => x / (2 : ℝ) ^ 96) h

end
end ImbalancedChen.P2OriginalSaving16OriginalArchive
