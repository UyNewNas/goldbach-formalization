import Lean
import ImbalancedChen.P2OriginalSaving17DescendingGeometry

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The actual fifteen descending witness texts, with the existing pure
SourceJson and unchanged schema decoder reused from saving16. The loader
emits String literals only. All following finite proof bodies are closed
and UNEVALUATED. T03 owns byte provenance/staging, not these mathematical
source-row, determinant, factor-mean, floor and pulling-incidence checks.
-/
namespace ImbalancedChen.P2OriginalSaving17DescendingArchive
open Lean Elab Term
open scoped Classical BigOperators
open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive
  (CellRecord SimplexRecord decodeCell QPoint point simplexVertices evalQ castPoint
   edgeMatrix physicalVolumeQ)
open P2OriginalSaving16JensenFloor (q96Floor)

elab "originalSaving17Text% " n:num : term => do
  let c := n.getNat
  unless c < 15 do throwError "saving17 selects descending source IDs0..14"
  let suffix := if c < 10 then "0" ++ toString c else toString c
  let path := "../goldbach-research/eighth-prefix-family-20261009-descending-cell-" ++
    suffix ++ ".witness.json"
  let raw ← liftIO <| IO.FS.readFile path
  elabTerm (Syntax.mkStrLit raw) (some (mkConst ``String))

noncomputable section
open Set
open P2OriginalSaving17DescendingGeometry

def originalText : Fin 15 → String :=
  ![originalSaving17Text% 0, originalSaving17Text% 1, originalSaving17Text% 2,
    originalSaving17Text% 3, originalSaving17Text% 4, originalSaving17Text% 5,
    originalSaving17Text% 6, originalSaving17Text% 7, originalSaving17Text% 8,
    originalSaving17Text% 9, originalSaving17Text% 10, originalSaving17Text% 11,
    originalSaving17Text% 12, originalSaving17Text% 13, originalSaving17Text% 14]

def parsedCell (i : Fin 15) : Except String CellRecord := do
  decodeCell (← SourceJson.parse (originalText i))
def archive (i : Fin 15) : CellRecord := (parsedCell i).toOption.getD default
def parsedCellSuccess (i : Fin 15) : Bool :=
  match parsedCell i with | .ok _ => true | .error _ => false

theorem original_parse_success_tag : ∀ i : Fin 15, parsedCellSuccess i = true := by decide
theorem original_parse_success (i : Fin 15) : parsedCell i = .ok (archive i) := by
  cases h : parsedCell i with
  | error message =>
      have hs := original_parse_success_tag i
      simp [parsedCellSuccess, h] at hs
  | ok record => simp [archive, h]

def comparisonQ (t : QPoint) : ℚ := 57 / 64 - (3 / 2) * (t 1 + t 2)
def capQ (t : QPoint) : ℚ := 57 / 64 - (3 / 2) * (t 0 + t 7) - 1 / 1000000
def gapQ (t : QPoint) : ℚ := capQ t - comparisonQ t
def factorsQ (t : QPoint) : Fin 10 → ℚ :=
  ![comparisonQ t - ∑ i, t i, capQ t - ∑ i, t i,
    t 0, t 1, t 2, t 3, t 4, t 5, t 6, t 7]
def gapTotalQ (v : Fin 9 → QPoint) : ℚ := ∑ i : Fin 9, gapQ (v i)
def meansQ (v : Fin 9 → QPoint) (j : Fin 10) : ℚ :=
  ((∑ i : Fin 9, factorsQ (v i) j) +
    (∑ i : Fin 9, gapQ (v i) * factorsQ (v i) j) / gapTotalQ v) / 10
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

theorem original_simplex_operations : ∀ (i : Fin 15) (s : Fin (archive i).simplices.size),
    simplexValid (archive i) s := by decide

theorem original_headers : ∀ i : Fin 15,
    (archive i).cellId = i.val ∧ (archive i).dimension = 8 ∧
    (archive i).physicalJacobian = 1 ∧
    (∀ v : Fin (archive i).vertices.size, ((archive i).vertices[v]).size = 8) ∧
    0 < (archive i).simplices.size := by decide

theorem original_vertices_all96 : ∀ (i : Fin 15) (v : Fin (archive i).vertices.size)
    (k : Fin 96), 0 ≤ evalQ (rows i k).2 (point (archive i) v.val) := by decide

theorem evalQ_cast (a : Fin 9 → ℚ) (x : QPoint) :
    evalRow a (castPoint x) = (evalQ a x : ℝ) :=
  P2OriginalSaving16OriginalArchive.evalQ_cast a x

theorem original_vertex_mem_closure (i : Fin 15) (v : Fin (archive i).vertices.size) :
    castPoint (point (archive i) v.val) ∈ closure (cell i) := by
  apply closedRows_mem_closure i
    (P4AOriginalFull87DescAscPairInteriors.originalDescPoint i)
    (P4AOriginalFull87DescAscPairInteriors.all15_centre_mem_original_source i)
  intro k
  rw [evalQ_cast]
  exact_mod_cast original_vertices_all96 i v k

theorem original_facet_indices : ∀ (i : Fin 15)
    (f : Fin (archive i).facetOriginalIndices.size),
    (archive i).facetOriginalIndices[f] < 96 := by decide

theorem original_facet_incidence : ∀ (i : Fin 15),
    (archive i).facetOriginalIndices.size = (archive i).facetVertices.size ∧
    ∀ (f : Fin (archive i).facetOriginalIndices.size) (v : Fin (archive i).vertices.size),
      (v.val ∈ ((archive i).facetVertices.getD f.val #[]).toList ↔
        evalQ (rows i ⟨(archive i).facetOriginalIndices[f], original_facet_indices i f⟩).2
          (point (archive i) v.val) = 0) := by decide

def cellFloorNumerator (i : Fin 15) : ℤ :=
  ∑ s : Fin (archive i).simplices.size,
    q96Floor (jensenQ (simplexVertices (archive i) (archive i).simplices[s]))
def aggregateNumerator : ℤ := ∑ i : Fin 15, cellFloorNumerator i
def historicalNumerator : ℤ := 467454156274267811817033

/-- Each original row is floored before summation, exactly as published.
No author PASS, reported bound or integral inequality is used as proof. -/
theorem original_q96_aggregate : aggregateNumerator = historicalNumerator := by decide
theorem original_counts :
    (∑ i : Fin 15, (archive i).simplices.size) = 63612 ∧
    (∑ i : Fin 15, (archive i).active8.size) = 48324 := by decide

theorem original_q96_aggregate_real :
    (∑ i : Fin 15, (cellFloorNumerator i : ℝ) / (2 : ℝ) ^ 96) =
      (467454156274267811817033 : ℝ) / (2 : ℝ) ^ 96 := by
  rw [← Finset.sum_div]
  have h := congrArg (fun z : ℤ => (z : ℝ)) original_q96_aggregate
  simpa [aggregateNumerator, historicalNumerator] using
    congrArg (fun x : ℝ => x / (2 : ℝ) ^ 96) h

end
end ImbalancedChen.P2OriginalSaving17DescendingArchive
