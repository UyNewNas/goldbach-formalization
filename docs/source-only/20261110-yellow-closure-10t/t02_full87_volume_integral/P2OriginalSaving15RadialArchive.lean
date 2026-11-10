import Lean
import ImbalancedChen.P2OriginalPhysicalSimplexJensenRow
import ImbalancedChen.P2OriginalRadialBasePulling
import ImbalancedChen.P4AOriginalFull87ArchiveSourceIndex

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The one original seed7 radial witness, four projected chambers and ONLY
its four-panel records. Original1/2-panel alternatives are not summed.
This module constructs the eight actual staircase simplices per panel;
it does not assert any volume/integral/nonoverlap statement as data.
-/
namespace ImbalancedChen.P2OriginalSaving15RadialArchive
open Lean Elab Term
elab "originalRadial15Text%" : term => do
  let raw ← liftIO <| IO.FS.readFile
    "../goldbach-research/eighth-radial-reduction-20261009.witness.json"
  elabTerm (Syntax.mkStrLit raw) (some (mkConst ``String))

noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open scoped Classical BigOperators
open P2OriginalSaving19Archive
  (SourceJson rationalField rationalArrayField rationalArray parseInteger FaceRecord decodeFace)
open P2OriginalSaving16OriginalArchive (QPoint evalQ edgeMatrix physicalVolumeQ)
open P2OriginalRadialBasePulling (QPoint7 Affine7 eval7)

structure Panel where
  panel : ℕ
  mass : ℚ
  means : Array ℚ
  bound : ℚ
  floor : ℤ
  deriving Inhabited, DecidableEq
def decodePanel (j : SourceJson) : Except String Panel := do
  return {panel := ← j.getObjValAs? Nat "panel"
    mass := ← rationalField j "mass_gap"
    means := ← rationalArrayField j "factor_gap_weighted_means"
    bound := ← rationalField j "bound"
    floor := ← parseInteger (← j.getObjValAs? String "floor_Q96")}
structure OuterRow where
  simplexId : ℕ
  vertexIds : Array ℕ
  outerVolume : ℚ
  panels : Array Panel
  deriving Inhabited, DecidableEq
def decodeOuterRow (j : SourceJson) : Except String OuterRow := do
  let ps ← (← j.getObjVal? "panel_records").getObjVal? "4"
  return {simplexId := ← j.getObjValAs? Nat "simplex_id"
    vertexIds := ← j.getObjValAs? (Array Nat) "vertex_ids"
    outerVolume := ← rationalField j "outer_volume"
    panels := ← (← ps.getArr?).mapM decodePanel}
structure Chamber where
  lowerId : ℕ
  upperId : ℕ
  gates : Array (Array ℚ)
  vertices : Array (Array ℚ)
  facets : Array (Array ℕ)
  faces : Array FaceRecord
  rows : Array OuterRow
  deriving Inhabited, DecidableEq
def decodeChamber (j : SourceJson) : Except String Chamber := do
  return {lowerId := ← j.getObjValAs? Nat "lower_id"
    upperId := ← j.getObjValAs? Nat "upper_id"
    gates := ← (← (← j.getObjVal? "inequalities").getArr?).mapM rationalArray
    vertices := ← (← (← j.getObjVal? "vertices").getArr?).mapM rationalArray
    facets := ← j.getObjValAs? (Array (Array Nat)) "facet_vertices"
    faces := ← (← (← j.getObjVal? "face_ledger").getArr?).mapM decodeFace
    rows := ← (← (← j.getObjVal? "simplices").getArr?).mapM decodeOuterRow}
structure Archive where
  dimension : ℕ
  lower : Array (Array ℚ)
  upper : Array (Array ℚ)
  chambers : Array Chamber
  deriving Inhabited, DecidableEq
def decodeArchive (j : SourceJson) : Except String Archive := do
  return {dimension := ← j.getObjValAs? Nat "dimension"
    lower := ← (← (← j.getObjVal? "lower_affine").getArr?).mapM rationalArray
    upper := ← (← (← j.getObjVal? "upper_affine").getArr?).mapM rationalArray
    chambers := ← (← (← j.getObjVal? "cells").getArr?).mapM decodeChamber}
def originalText : String := originalRadial15Text%
def parsedArchive : Except String Archive := SourceJson.parse originalText >>= decodeArchive
def archive : Archive := parsedArchive.toOption.getD default
def parseSuccess : Bool := match parsedArchive with | .ok _ => true | .error _ => false
theorem original_parse_tag : parseSuccess = true := by decide
theorem original_parse : parsedArchive = .ok archive := by
  cases h : parsedArchive with
  | error msg => have hs := original_parse_tag; simp [parseSuccess,h] at hs
  | ok d => simp [archive,h]

def chamber (c : Fin 4) : Chamber := archive.chambers.getD c.val default
def data (c : Fin 4) : P2OriginalRadialBasePulling.Data where
  vertices := (chamber c).vertices
  facets := (chamber c).facets
  faces := (chamber c).faces
  rows := (chamber c).rows.map (fun r => r.vertexIds)
  gates := (chamber c).gates
abbrev BaseRow (c : Fin 4) := Fin (data c).rows.size
def baseVertex (c : Fin 4) (s : BaseRow c) (i : Fin 8) : QPoint7 :=
  P2OriginalRadialBasePulling.rowVertices (data c) s i
def lowerId (c : Fin 4) : Fin 2 := ⟨c.val / 2,by omega⟩
def upperId (c : Fin 4) : Fin 2 := ⟨c.val % 2,by omega⟩
def lowerAffine : Fin 2 → Affine7 :=
  ![![25/32+2/1000000,-1,-3,-3,0,0,0,0],
    ![1/7-2/(7*1000000),-1/7,-2/7,-2/7,-2/7,-2/7,-2/7,-2/7]]
def upperAffine : Fin 2 → Affine7 :=
  ![![0,0,0,0,0,0,0,1],![25/128,-1,0,0,0,0,0,0]]
def lowerAt (c : Fin 4) (x : QPoint7) : ℚ := eval7 (lowerAffine (lowerId c)) x
def upperAt (c : Fin 4) (x : QPoint7) : ℚ := eval7 (upperAffine (upperId c)) x
def liftPoint (x : QPoint7) (r : ℚ) : QPoint :=
  ![x 0,x 1,x 2,x 3,x 4,x 5,x 6,r]
def height (c : Fin 4) (x : QPoint7) (n : ℕ) : ℚ :=
  lowerAt c x + (n : ℚ) / 4 * (upperAt c x - lowerAt c x)
-- The staircase index is Fin8, independent of the four panel index.
def pieceVertices (c : Fin 4) (s : BaseRow c) (p : Fin 4) (k : Fin 8) : Fin 9 → QPoint :=
  fun i => if h : i.val ≤ k.val then
    let j : Fin 8 := ⟨i.val,by omega⟩
    liftPoint (baseVertex c s j) (height c (baseVertex c s j) p.val)
  else
    let j : Fin 8 := ⟨i.val-1,by omega⟩
    liftPoint (baseVertex c s j) (height c (baseVertex c s j) (p.val+1))
def extendedVertices (c : Fin 4) (s : BaseRow c) : Fin 9 → QPoint :=
  fun i => if h : i.val < 8 then liftPoint (baseVertex c s ⟨i.val,h⟩) 0
    else liftPoint (baseVertex c s 0) 1
def panelRecord (c : Fin 4) (s : BaseRow c) (p : Fin 4) : Panel :=
  (((chamber c).rows.getD s.val default).panels.getD p.val default)

theorem original_headers :
    archive.dimension = 7 ∧ archive.chambers.size = 4 ∧
    (∀ i : Fin 2, archive.lower.getD i.val #[] = Array.ofFn (lowerAffine i) ∧
      archive.upper.getD i.val #[] = Array.ofFn (upperAffine i)) ∧
    ∀ c : Fin 4, (chamber c).lowerId = (lowerId c).val ∧ (chamber c).upperId = (upperId c).val ∧
      ∀ s : BaseRow c, ((chamber c).rows.getD s.val default).simplexId = s.val ∧
        ((chamber c).rows.getD s.val default).panels.size = 4 ∧
        ∀ p : Fin 4, (panelRecord c s p).panel = p.val := by decide
theorem original_base_checks : ∀ c : Fin 4, P2OriginalRadialBasePulling.Checks (data c) := by decide
theorem original_extended_determinants : ∀ (c : Fin 4) (s : BaseRow c),
    (edgeMatrix (extendedVertices c s)).det ≠ 0 := by decide
theorem original_widths_and_selectors : ∀ (c : Fin 4) (v : Fin (data c).vertices.size),
    let x := P2OriginalRadialBasePulling.vertex (data c) v.val
    lowerAt c x ≤ upperAt c x ∧
    (∀ i : Fin 2, eval7 (lowerAffine i) x ≤ lowerAt c x) ∧
    (∀ i : Fin 2, upperAt c x ≤ eval7 (upperAffine i) x) := by decide

def seedRows (g : Fin 96) : Fin 9 → ℚ := P4AOriginalRemainingEighthSources.row .seed g
theorem original_endpoint_source_rows : ∀ (c : Fin 4) (v : Fin (data c).vertices.size) (g : Fin 96),
    let x := P2OriginalRadialBasePulling.vertex (data c) v.val
    0 ≤ evalQ (seedRows g) (liftPoint x (lowerAt c x)) ∧
    0 ≤ evalQ (seedRows g) (liftPoint x (upperAt c x)) := by decide

def savedNumerator : ℤ := ∑ c : Fin 4, ∑ s : BaseRow c, ∑ p : Fin 4, (panelRecord c s p).floor
theorem original_selected_numerator : savedNumerator = 74558208451675327462975 := by decide
theorem original_outer_count : (∑ c : Fin 4, (data c).rows.size) = 2847 := by decide
theorem original_selected_seed_record :
    (P4AOriginalFull87ArchiveSourceIndex.archivedRecordForOriginalCell (.remaining .seed)).2 =
      (savedNumerator : ℚ)/(2 : ℚ)^96 := by decide

end
end ImbalancedChen.P2OriginalSaving15RadialArchive
