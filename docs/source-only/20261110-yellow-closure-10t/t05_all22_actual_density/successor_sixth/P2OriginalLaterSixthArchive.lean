import Lean
import ImbalancedChen.P2OriginalLaterSixthKernel
import ImbalancedChen.P2OriginalSaving16OriginalArchive
import ImbalancedChen.CurrentUpperEighteenBudget

/-! Author witness and navigation documents of the seven later sixth
entries. The elaborator embeds the original strings. Rational arithmetic,
row selection, incidence, physical determinants and per-simplex Q96
floors are separate closed definitions for kernel verification. -/
namespace ImbalancedChen.P2OriginalLaterSixthArchive
open Lean Elab Term
open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive (parseInteger rationalField rationalArray)
open P2OriginalSixthSimplexBinding (QPoint edgeMatrix physicalVolumeQ)
open P2OriginalLaterSixthKernel
open P2OriginalLogMomentQ96CheckerSourceOnly (oldFloorQ96)
open P2OriginalSixthMomentRow (rowMassQ rowMeansQ)
open scoped BigOperators

def names : Array String :=
  #["sixth-tent33-descending-20261009.witness.json",
    "sixth-tent34-ascending-upgrade-20261009.witness.json",
    "sixth-tent34-descending-upgrade-20261009.witness.json",
    "sixth-lower-clip-window-exact-20261009.witness.json",
    "sixth-lower-desc34-window-20261009.witness.json",
    "sixth-lower-mask33-cells-20261009.witness.json",
    "sixth-lower-mask50-cells-20261009.witness.json",
    "sixth-lower-mask33-upgrade-20261009.witness.json",
    "sixth-nonsingleton-freecap-20261009.witness.json",
    "sixth-actual-cap-refinement-20261009.witness.json",
    "sixth-lower-clip-window-navigation-20261009.json",
    "sixth-lower-desc34-window-20261009-navigation.json",
    "sixth-lower-mask33-cells-20261009-navigation.json",
    "sixth-lower-mask50-cells-20261009-navigation.json",
    "sixth-lower-mask33-upgrade-20261009-navigation.json"]

elab "originalLaterSixthText% " n:num : term => do
  let idx := n.getNat
  let some name := names[idx]? | throwError "unknown original later-sixth document"
  let path := "../tmp/publication-20261010/verification-renewal-v2/_runs/full-final/" ++ name
  let raw ← liftIO <| IO.FS.readFile path
  elabTerm (Syntax.mkStrLit raw) (some (mkConst ``String))

def text : Fin 15 → String :=
  ![originalLaterSixthText% 0,originalLaterSixthText% 1,originalLaterSixthText% 2,
    originalLaterSixthText% 3,originalLaterSixthText% 4,originalLaterSixthText% 5,
    originalLaterSixthText% 6,originalLaterSixthText% 7,originalLaterSixthText% 8,
    originalLaterSixthText% 9,originalLaterSixthText% 10,originalLaterSixthText% 11,
    originalLaterSixthText% 12,originalLaterSixthText% 13,originalLaterSixthText% 14]

structure Face where
  vertices : Array Nat
  pivot : Nat
  facetSets : Array (Array Nat)
  deriving Inhabited
structure Simplex where
  idx : Nat
  ids : Array Nat
  volume : ℚ
  q96 : Int
  deriving Inhabited
structure Bank where
  vertices : Array (Array ℚ)
  gates : Array (Array ℚ)
  facets : Array (Array Nat)
  faces : Array Face
  simplices : Array Simplex
  deriving Inhabited

def file : Piece → Fin 15 := ![0,0,1,1,2,2,3,4,5,5,6,6,6,6,7,8,8,8,8,9,9]
def offset : Piece → Nat := ![0,1,0,1,0,1,0,0,0,3,0,1,2,3,0,0,1,2,3,0,1]
def nav : Piece → Option (Fin 15 × Nat) :=
  ![none,none,none,none,none,none,some (10,8),some (11,8),some (12,11),some (12,28),
    some (13,6),some (13,7),some (13,23),some (13,24),some (14,1),none,none,none,none,none,none]
def pattern : Piece → Nat :=
  ![1371,1867,1371,1371,1371,1371,1371,1371,1867,1867,1353,1355,1353,1355,1371,1355,1355,1867,1867,1371,1371]
def pieceCount : Piece → Nat :=
  ![420,225,231,390,180,378,626,274,599,101,6,1,6,6,120,60,153,322,1,390,300]

def pick (j : SourceJson) (k : String) (idx : Nat) : Except String SourceJson := do
  let a ← (← j.getObjVal? k).getArr?
  match a[idx]? with
  | some r => pure r
  | none => throw "original array index outside witness"
def decodeFace (j : SourceJson) : Except String Face := do
  return ⟨← j.getObjValAs? (Array Nat) "vertices",← j.getObjValAs? Nat "pivot",
    ← j.getObjValAs? (Array (Array Nat)) "facet_sets"⟩
def decodeSimplex (key : String) (j : SourceJson) : Except String Simplex := do
  return ⟨← j.getObjValAs? Nat "simplex_id",← j.getObjValAs? (Array Nat) "vertex_ids",
    ← rationalField j "physical_volume",← parseInteger (← j.getObjValAs? String key)⟩
def document (k : Fin 15) := SourceJson.parse (text k)
def parseBank (i : Piece) : Except String Bank := do
  let doc ← document (file i)
  let single := (file i).val=3 ∨ (file i).val=4
  let geom ← if single then pure doc else pick doc "cells" (offset i)
  let gates ← match nav i with
    | none => pure geom
    | some (k,j) => do pick (← document k) "records" j
  let p ← gates.getObjValAs? Nat "pattern"
  unless p=pattern i do throw "original branch label mismatch"
  if ¬single then
    let pg ← geom.getObjValAs? Nat "pattern"
    unless pg=pattern i do throw "original witness branch label mismatch"
  let ledger := if (file i).val=0 ∨ (file i).val=1 ∨ (file i).val=9 then
      "positive_dimensional_face_ledger" else "face_ledger"
  let floorKey := if 3≤(file i).val ∧ (file i).val≤7 then "jensen_floor_Q96" else "floor_Q96"
  return {
    vertices := ← (← (← geom.getObjVal? "vertices").getArr?).mapM rationalArray
    gates := ← (← (← gates.getObjVal? "affine_constraints").getArr?).mapM
      (fun a => do rationalArray (← a.getObjVal? "affine"))
    facets := ← geom.getObjValAs? (Array (Array Nat)) "facet_vertices"
    faces := ← (← (← geom.getObjVal? ledger).getArr?).mapM decodeFace
    simplices := ← (← (← geom.getObjVal? "simplices").getArr?).mapM (decodeSimplex floorKey) }

def bank (i : Piece) : Bank := (parseBank i).toOption.getD default
abbrev Individual (i : Piece) := Fin (bank i).simplices.size
def sx (i : Piece) (s : Individual i) := (bank i).simplices[s]
def physicalQ (q : QPoint) : QPoint :=
  ![q 0,q 1,q 2,(1-q 0)/2-q 1-q 2-3*q 3/2+q 4/2,(q 3-q 4)/2,q 5]
def vertex (i : Piece) (v : Nat) : QPoint :=
  let raw : QPoint := fun j => ((bank i).vertices.getD v #[]).getD j.val 0
  if charted i then physicalQ raw else raw
def rowVertices (i : Piece) (s : Individual i) : Fin 7 → QPoint :=
  fun k => vertex i ((sx i s).ids.getD k.val 0)

structure Primitive (i : Piece) (s : Individual i) : Prop where
  simplexId : (sx i s).idx=s.val
  idCount : (sx i s).ids.size=7
  idsWithin : ∀ k : Fin 7,(sx i s).ids.getD k.val 0<(bank i).vertices.size
  det : (edgeMatrix (rowVertices i s)).det≠0
  volumeMatch : (sx i s).volume=physicalVolumeQ (rowVertices i s)
  gapNonneg : ∀ k,0≤evalQ (gapPlane i) (rowVertices i s k)
  gapSum : 0<∑ k,evalQ (gapPlane i) (rowVertices i s k)
  factorsLower : ∀ k j,P2OriginalSixthMomentRow.cutoffQ≤evalQ (factorPlane i j) (rowVertices i s k)

instance primitiveDecidable (i : Piece) (s : Individual i) : Decidable (Primitive i s) :=
  decidable_of_iff
    ((sx i s).idx=s.val ∧ (sx i s).ids.size=7 ∧
      (∀ k : Fin 7,(sx i s).ids.getD k.val 0<(bank i).vertices.size) ∧
      (edgeMatrix (rowVertices i s)).det≠0 ∧
      (sx i s).volume=physicalVolumeQ (rowVertices i s) ∧
      (∀ k,0≤evalQ (gapPlane i) (rowVertices i s k)) ∧
      (0<∑ k,evalQ (gapPlane i) (rowVertices i s k)) ∧
      (∀ k j,P2OriginalSixthMomentRow.cutoffQ≤evalQ (factorPlane i j) (rowVertices i s k)))
    ⟨fun ⟨a,b,c,d,e,f,g,h⟩ => ⟨a,b,c,d,e,f,g,h⟩,
      fun p => ⟨p.simplexId,p.idCount,p.idsWithin,p.det,p.volumeMatch,p.gapNonneg,p.gapSum,p.factorsLower⟩⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem original_piece_sizes (i : Piece) : (bank i).simplices.size=pieceCount i := by
  fin_cases i <;> decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem original_primitive (i : Piece) : ∀ s : Individual i,Primitive i s := by
  fin_cases i <;> decide

def physicalRow (i : Piece) (s : Individual i) : PhysicalRow i :=
  ⟨rowVertices i s,(original_primitive i s).det,(original_primitive i s).gapNonneg,
    (original_primitive i s).gapSum,(original_primitive i s).factorsLower⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem original_ordinary_Jensen (i : Piece) :
    ∀ s : Individual i,(sx i s).q96=oldFloorQ96 (rowMassQ (physicalRow i s).toRow) (rowMeansQ (physicalRow i s).toRow) := by
  fin_cases i <;> decide

def totalQ96 (s : Fin 7) : Int :=
  ∑ i ∈ Finset.univ.filter (fun i => slot i=s), ∑ j : Individual i,(sx i j).q96

/-- Each selected original rational is the Q96 numerator of exactly its
archived simplices. In G13 the two correction pieces are included once. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem original_slot_totals (s : Fin 7) : totalQ96 s =
    ![148834609033428677786865,306737545112876482463163,187277743940187526723019,
      670429887277013841791829,2*198410119216276585672773,8*5023185001132087792027,
      16*581521529176619227721] s := by
  fin_cases s <;> decide

theorem numerical_slot (s : Fin 7) :
    currentUpperEighteenGains ⟨7+s.val,by omega⟩=(totalQ96 s:ℝ)/(2:ℝ)^96 := by
  rw [original_slot_totals]
  fin_cases s <;> norm_num [currentUpperEighteenGains]

end ImbalancedChen.P2OriginalLaterSixthArchive
