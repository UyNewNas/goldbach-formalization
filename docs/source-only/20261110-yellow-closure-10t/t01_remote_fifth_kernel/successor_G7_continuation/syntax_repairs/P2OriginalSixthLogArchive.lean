import Lean
import ImbalancedChen.P2OriginalSixthPhysicalRow
import ImbalancedChen.P2OriginalSaving16OriginalArchive

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Original G7 bytes are read only as ordinary String literals at USER
compilation. The existing pure fuel-recursive SourceJson parser decodes
them; the elaborator proves nothing and runs no numerical producer.
All closed guards below are UNEVALUATED. They reconstruct determinants,
actual7-node moments, eight separateQ80 floors and the whole simplexQ96
floor. A quoted historical PASS or summary is never a proof input.
-/
namespace ImbalancedChen.P2OriginalSixthLogArchive
open Lean Elab Term
open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive (parseInteger rationalField rationalArray)
open P2OriginalSixthSimplexBinding (QPoint edgeMatrix physicalVolumeQ)
open P2OriginalSixthPhysicalRow (PhysicalRow decodeQ gapQ factorsQ)
open P2OriginalLogMomentQ96CheckerSourceOnly
open scoped BigOperators
def originalNames : List String :=
  ["sixth-license-family-20261009-exact.witness.json",
   "sixth-license-family-20261009-mask50-residual.witness.json",
   "sixth-pair17-winner-20261009-exact.witness.json",
   "sixth-pair12-ascending-cell-20261009.witness.json",
   "sixth-tent33-ascending-20261009.witness.json",
   "sixth-log-moment-jensen-20261009.witness.json",
   "sixth-pair12-ascending-cell-20261009.navigation.json"]

elab "originalG7Text% " n:num : term => do
  let i := n.getNat
  let names := #["sixth-license-family-20261009-exact.witness.json",
    "sixth-license-family-20261009-mask50-residual.witness.json",
    "sixth-pair17-winner-20261009-exact.witness.json",
    "sixth-pair12-ascending-cell-20261009.witness.json",
    "sixth-tent33-ascending-20261009.witness.json",
    "sixth-log-moment-jensen-20261009.witness.json",
    "sixth-pair12-ascending-cell-20261009.navigation.json"]
  unless i < names.size do throwError "original G7 selects exactly seven original texts"
  let path := "../tmp/publication-20261010/verification-renewal-v2/_runs/full-final/" ++ names[i]!
  let raw ← liftIO <| IO.FS.readFile path
  elabTerm (Syntax.mkStrLit raw) (some (mkConst ``String))

def originalText : Fin 7 → String :=
  ![originalG7Text% 0,originalG7Text% 1,originalG7Text% 2,
    originalG7Text% 3,originalG7Text% 4,originalG7Text% 5,originalG7Text% 6]

structure Simplex where
  simplexId : Nat
  vertexIds : Array Nat
  physicalVolume : ℚ
  deriving Inhabited
structure Face where
  vertices : Array Nat
  pivot : Nat
  facetSets : Array (Array Nat)
  deriving Inhabited
structure CellData where
  cellId : String
  vertices : Array (Array ℚ)
  facets : Array (Array Nat)
  facetOriginalIndices : Array Nat
  rawGates : Array (Array ℚ)
  faces : Array Face
  simplices : Array Simplex
  deriving Inhabited
structure LogRow where
  group : String
  cellId : String
  simplexId : Nat
  factorFloors : Array Int
  oldFloor : Int
  newFloor : Int
  deriving Inhabited

def decodeSimplex (j : SourceJson) : Except String Simplex := do
  return { simplexId := ← j.getObjValAs? Nat "simplex_id"
           vertexIds := ← j.getObjValAs? (Array Nat) "vertex_ids"
           physicalVolume := ← rationalField j "physical_volume" }
def decodeFace (j : SourceJson) : Except String Face := do
  return { vertices := ← j.getObjValAs? (Array Nat) "vertices"
           pivot := ← j.getObjValAs? Nat "pivot"
           facetSets := ← j.getObjValAs? (Array (Array Nat)) "facet_sets" }
def decodeCell (pair12 : Bool) (gateDocument j : SourceJson) : Except String CellData := do
  let cid ← if pair12 then pure "pair12-fixed" else j.getObjValAs? String "cell_id"
  let ledger ← j.getObjVal? (if pair12 then "face_ledger" else "positive_dimensional_face_ledger")
  return { cellId := cid
           vertices := ← (← (← j.getObjVal? "vertices").getArr?).mapM rationalArray
           facets := ← j.getObjValAs? (Array (Array Nat)) "facet_vertices"
           facetOriginalIndices := ← j.getObjValAs? (Array Nat) "facet_original_indices"
           rawGates := ← (← (← gateDocument.getObjVal? "affine_constraints").getArr?).mapM
             (fun g => do rationalArray (← g.getObjVal? "affine"))
           faces := ← (← ledger.getArr?).mapM decodeFace
           simplices := ← (← (← j.getObjVal? "simplices").getArr?).mapM decodeSimplex }
def decodeLogRow (j : SourceJson) : Except String LogRow := do
  return { group := ← j.getObjValAs? String "group"
           cellId := ← j.getObjValAs? String "cell_id"
           simplexId := ← j.getObjValAs? Nat "simplex_id"
           factorFloors := ← (← (← j.getObjVal? "log_gap_factor_floors_Q80").getArr?).mapM
             (fun q => do parseInteger (← q.getStr?))
           oldFloor := ← parseInteger (← j.getObjValAs? String "old_floor_Q96")
           newFloor := ← parseInteger (← j.getObjValAs? String "new_floor_Q96") }

def parsedCells (i : Fin 5) : Except String (Array CellData) := do
  let j ← SourceJson.parse (originalText ⟨i.val,by omega⟩)
  if i.val = 3 then
    let gates ← SourceJson.parse (originalText 6)
    return #[← decodeCell true gates j]
  else (← (← j.getObjVal? "cells").getArr?).mapM (fun cell => decodeCell false cell cell)
def parsedLog : Except String (Array LogRow) := do
  let j ← SourceJson.parse (originalText 5)
  let degree ← j.getObjValAs? Nat "log_moment_degree"
  let expDegree ← j.getObjValAs? Nat "exp_degree"
  let q80 ← parseInteger (← j.getObjValAs? String "log_floor_denominator")
  let q96 ← parseInteger (← j.getObjValAs? String "final_floor_denominator")
  unless degree = 6 ∧ expDegree = 3 ∧ q80 = (2:Int)^80 ∧ q96 = (2:Int)^96 do
    throw "original G7 degree or floor scales differ"
  (← (← j.getObjVal? "records").getArr?).mapM decodeLogRow

def sourceCells (i : Fin 5) : Array CellData := (parsedCells i).toOption.getD #[]
def logRows : Array LogRow := parsedLog.toOption.getD #[]
def sourceFile : Fin 11 → Fin 5 := ![0,0,0,0,1,1,2,2,3,4,4]
def sourceOffset : Fin 11 → Nat := ![0,1,2,3,0,1,0,1,0,0,1]
def sourceCell : Fin 11 → ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics.Cell :=
  ![.singleton33_1355,.singleton33_1371,.singleton33_1867,.singleton34_1371,
    .singleton50_1353,.singleton50_1355,.pair17_1355,.pair17_1867,.pair12_fixed,
    .tent33_1371,.tent33_1867]
def sourceGroup (i : Fin 11) : String :=
  match (sourceCell i).family with
  | .singleton => "singleton" | .pair17 => "pair17" | .pair12 => "pair12" | .tent33 => "tent33"
def archive (i : Fin 11) : CellData := (sourceCells (sourceFile i)).getD (sourceOffset i) default
def rawVertex (i : Fin 11) (v : Nat) : QPoint :=
  fun j => ((archive i).vertices.getD v #[]).getD j.val 0
def vertex (i : Fin 11) (v : Nat) : QPoint := decodeQ (sourceCell i) (rawVertex i v)
def rowVertices (i : Fin 11) (s : Fin (archive i).simplices.size) : Fin 7 → QPoint :=
  fun k => vertex i ((archive i).simplices[s].vertexIds.getD k.val 0)
def logAt (i : Fin 11) (s : Fin (archive i).simplices.size) : LogRow :=
  (logRows.toList.find? fun r => r.group == sourceGroup i && r.cellId == (sourceCell i).sourceID &&
    r.simplexId == s.val).getD default
def parseSuccess : Bool :=
  (List.ofFn fun i : Fin 5 => match parsedCells i with | .ok _ => true | .error _ => false).all id &&
  (match parsedLog with | .ok _ => true | .error _ => false)

theorem original_parse_success : parseSuccess = true := by decide
theorem original_headers : ∀ i : Fin 11,
    (archive i).cellId = (sourceCell i).sourceID ∧
    (∀ v : Fin (archive i).vertices.size, (archive i).vertices[v].size = 6) ∧
    0 < (archive i).simplices.size := by decide

def PrimitiveRowChecks (i : Fin 11) (s : Fin (archive i).simplices.size) : Prop :=
  let v := rowVertices i s
  (archive i).simplices[s].simplexId = s.val ∧
  (archive i).simplices[s].vertexIds.size = 7 ∧
  (∀ k : Fin 7, (archive i).simplices[s].vertexIds.getD k.val 0 < (archive i).vertices.size) ∧
  (edgeMatrix v).det ≠ 0 ∧
  (archive i).simplices[s].physicalVolume = physicalVolumeQ v ∧
  (∀ k, 0 ≤ gapQ (sourceCell i) (v k)) ∧
  0 < ∑ k, gapQ (sourceCell i) (v k) ∧
  ∀ k j, P2OriginalSixthMomentRow.cutoffQ ≤ factorsQ (sourceCell i) (v k) j
instance (i : Fin 11) (s : Fin (archive i).simplices.size) : Decidable (PrimitiveRowChecks i s) :=
  by unfold PrimitiveRowChecks; infer_instance

/-- UNEVALUATED original geometry-to-row primitive guards. -/
theorem original_primitive_rows : ∀ i s, PrimitiveRowChecks i s := by decide

def physicalRow (i : Fin 11) (s : Fin (archive i).simplices.size) : PhysicalRow (sourceCell i) where
  verticesQ := rowVertices i s
  determinant_ne_zero := (original_primitive_rows i s).2.2.2.1
  gap_nonneg := (original_primitive_rows i s).2.2.2.2.2.1
  gapTotal_pos := (original_primitive_rows i s).2.2.2.2.2.2.1
  factor_floor := (original_primitive_rows i s).2.2.2.2.2.2.2

def MomentChecks (i : Fin 11) (s : Fin (archive i).simplices.size) : Prop :=
  let r := (physicalRow i s).toRow
  let w := logAt i s
  w.group = sourceGroup i ∧ w.cellId = (sourceCell i).sourceID ∧ w.simplexId = s.val ∧
  w.factorFloors.size = 8 ∧
  (∀ j : Fin 8, w.factorFloors.getD j.val 0 = factorFloorQ80 (P2OriginalSixthMomentRow.rowMomentsQ r j)) ∧
  w.oldFloor = oldFloorQ96 (P2OriginalSixthMomentRow.rowMassQ r) (P2OriginalSixthMomentRow.rowMeansQ r) ∧
  w.newFloor = newFloorQ96 (P2OriginalSixthMomentRow.rowMassQ r) (P2OriginalSixthMomentRow.rowMeansQ r)
    (P2OriginalSixthMomentRow.rowMomentsQ r)
instance (i : Fin 11) (s : Fin (archive i).simplices.size) : Decidable (MomentChecks i s) :=
  by unfold MomentChecks; infer_instance

/-- UNEVALUATED arithmetic, independently reconstructed from original
physical vertices rather than accepting any previous PASS record. -/
theorem original_moment_rows : ∀ i s, MomentChecks i s := by decide

def cellFloorNumerator (i : Fin 11) : Int := ∑ s : Fin (archive i).simplices.size, (logAt i s).newFloor
def aggregateNumerator : Int := ∑ i : Fin 11, cellFloorNumerator i
def originalNumerator : Int := 1208544915921356327515701
theorem original_counts :
    (∑ i : Fin 11, (archive i).simplices.size) = 2631 ∧ logRows.size = 2631 := by decide
theorem original_q96_aggregate : aggregateNumerator = originalNumerator := by decide

end ImbalancedChen.P2OriginalSixthLogArchive
