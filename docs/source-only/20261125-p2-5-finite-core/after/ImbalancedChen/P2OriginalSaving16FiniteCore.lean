import Lean
import ImbalancedChen.P2OriginalSaving16OriginalInput
import ImbalancedChen.P2OriginalSaving16Decoder
import ImbalancedChen.P2OriginalSaving16Q96FloorCore
import ImbalancedChen.P2OriginalSaving19SourceJson
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / NOT COMPILED / ZERO FINITE OR Q96 CREDIT.

Mechanical extraction of twenty-one existing finite source commands from
P2OriginalSaving16FiniteArchive at SHA256
9db41aa0553a3c5020acceffa3f1bc91529f1382f7dc6c6d57ba96c073e6d627.
The nineteen definitions, QPoint abbreviation and anonymous Decidable
instance retain their original namespace, complete text and context.

This module exposes the same archive and original simplex computations.
The four closed guards and their parse-success elimination theorem stay
in P2OriginalSaving16FiniteArchive. No file reader, parser, decoder,
algorithm, numerical result or theorem is added here. OriginalInput and
its fourteen-input binding remain required when this module is compiled.
-/
namespace ImbalancedChen.P2OriginalSaving16OriginalArchive

open Lean Elab Term
open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16JensenFloor (q96Floor)
open scoped BigOperators


noncomputable section


def originalId : Fin 14 → Nat := ![0,1,2,3,4,5,6,8,9,10,11,12,13,14]

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

def physicalVolumeQ (v : Fin 9 → QPoint) : ℚ := |(edgeMatrix v).det| / ((8 : ℕ).factorial : ℚ)

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

def cellFloorNumerator (i : Fin 14) : ℤ :=
  ∑ s : Fin (archive i).simplices.size,
    q96Floor (jensenQ (simplexVertices (archive i) (archive i).simplices[s]))

def aggregateNumerator : ℤ := ∑ i : Fin 14, cellFloorNumerator i

def historicalNumerator : ℤ := 1222997719565324892497827

end
end ImbalancedChen.P2OriginalSaving16OriginalArchive
