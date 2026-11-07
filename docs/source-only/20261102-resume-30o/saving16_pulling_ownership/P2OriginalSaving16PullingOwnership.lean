import ImbalancedChen.P2OriginalSaving16PullingFaceInduction
import ImbalancedChen.P2OriginalSaving16SimplexBinding
import ImbalancedChen.P2OriginalSaving19OwnedSource

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
All closed finite bodies are UNEVALUATED; their truth, elaboration, and
resource feasibility are unverified. The original M archive is frozen.

Decode only its retained face-ledger fields. Primitive checks authenticate
the original max pivots, supporting facet intersections, child antichains,
and ordered row identity. The separating-wall induction, rather than a
disjointness guard or a lifting-plane table, proves the geometric result.
-/
namespace ImbalancedChen.P2OriginalSaving16PullingOwnership

open Set MeasureTheory
open scoped BigOperators
open P2OriginalAscendingEighthCapDictionary
open P2OriginalSaving16FourteenPhysicalAtlas
open P2OriginalSaving16JensenFloor
open P2OriginalSaving16OriginalArchive
open P2OriginalSaving16SimplexBinding
open P2OriginalSaving16PullingFaceInduction
open P2OriginalSaving19Archive (SourceJson)

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

def parsedFaces (c : Fin 14) : Except String (Array FaceRecord) :=
  (archive c).faceLedger.mapM decodeFace

def faces (c : Fin 14) : Array FaceRecord := (parsedFaces c).toOption.getD #[]

def facesParseSuccess (c : Fin 14) : Bool :=
  match parsedFaces c with
  | .ok _ => true
  | .error _ => false

/-- No new file loader or parser. The original raw SourceJson ledger is
decoded at user compilation only. No default is accepted as parse success. -/
theorem original_faces_parse_tag : ∀ c : Fin 14, facesParseSuccess c = true := by
  decide

theorem original_faces_parse : ∀ c : Fin 14, parsedFaces c = .ok (faces c) := by
  intro c
  cases h : parsedFaces c with
  | error message =>
      have hs := original_faces_parse_tag c
      simp [facesParseSuccess, h] at hs
  | ok record => simp [faces, h]

def faceRecord (c : Fin 14) (face : List Nat) : FaceRecord :=
  ((faces c).toList.find? (fun f => f.vertices.toList == face)).getD default

def pivot (c : Fin 14) (face : List Nat) : Nat := (faceRecord c face).pivot

def children (c : Fin 14) (face : List Nat) : List (List Nat) :=
  (((faceRecord c face).facetSets.toList.map Array.toList).filter
    (fun child => !(child.contains (pivot c face))))

def whole (c : Fin 14) : List Nat := List.range (archive c).vertices.size

abbrev FacetIndex (c : Fin 14) := Fin (archive c).facetOriginalIndices.size

def facet (c : Fin 14) (f : FacetIndex c) : List Nat :=
  ((archive c).facetVertices.getD f.val #[]).toList

def gate (c : Fin 14) (f : FacetIndex c) : AffineRow :=
  (rows (atlasCell c)
    ⟨(archive c).facetOriginalIndices[f], original_facet_indices c f⟩).2

def originalPull (c : Fin 14) : List (List Nat) :=
  pull (pivot c) (children c) 9 (whole c)

def savedRows (c : Fin 14) : List (List Nat) :=
  (archive c).simplices.toList.map (fun r => r.vertexIds.toList)

def rowIds (c : Fin 14) (s : Fin (archive c).simplices.size) : List Nat :=
  ((archive c).simplices[s]).vertexIds.toList

/-- Only finite vertex-ID incidence. Child equality is checked on the
parent face against an ORIGINAL facet list, and incomparable children
cannot share their entire vertex set. All nested pivots are the maxima.
This is not a coverage, disjointness, volume, integral, or endpoint test. -/
theorem original_face_incidence_shape : ∀ c : Fin 14,
    Shape (facet c) (pivot c) (children c) 9 (whole c) := by
  decide

/-- Exact ordered recursion, as written by the original family producer.
Nodup is a vertex-ID-list property, not a geometric overlap assertion. -/
theorem original_pulling_bindings : ∀ c : Fin 14,
    originalPull c = savedRows c ∧ (savedRows c).Nodup := by
  decide

theorem row_mem_originalPull (c : Fin 14) (s : Fin (archive c).simplices.size) :
    rowIds c s ∈ originalPull c := by
  rw [(original_pulling_bindings c).1]
  apply List.mem_map.mpr
  exact ⟨(archive c).simplices[s], Array.getElem_mem_toList s.isLt, rfl⟩

theorem rowIds_ne (c : Fin 14) (s t : Fin (archive c).simplices.size) (hst : s ≠ t) :
    rowIds c s ≠ rowIds c t := by
  intro he
  have hs : s.val < (savedRows c).length := by simpa [savedRows] using s.isLt
  have ht : t.val < (savedRows c).length := by simpa [savedRows] using t.isLt
  have hget : (savedRows c)[s.val] = (savedRows c)[t.val] := by
    simpa [savedRows, rowIds] using he
  apply hst
  exact Fin.ext ((List.getElem_inj (h₀ := hs) (h₁ := ht)
    (original_pulling_bindings c).2).mp hget)

/-- The original96-row legality theorem supplies support, not a newly
computed gate table. No boundedness or vertex-exhaustion claim is needed. -/
theorem original_gate_nonneg (c : Fin 14) (f : FacetIndex c) (v : Nat)
    (hv : v ∈ whole c) : 0 ≤ evalQ (gate c f) (point (archive c) v) := by
  have hv' : v < (archive c).vertices.size := by simpa [whole] using hv
  exact original_vertices_all96 c ⟨v, hv'⟩
    ⟨(archive c).facetOriginalIndices[f], original_facet_indices c f⟩

/-- This is the precise correspondence to M's ORIGINAL facet incidence,
not to saving19's unrelated archive. -/
theorem original_facet_zero (c : Fin 14) (f : FacetIndex c) (v : Nat)
    (hv : v ∈ whole c) :
    (v ∈ facet c f ↔ evalQ (gate c f) (point (archive c) v) = 0) := by
  have hv' : v < (archive c).vertices.size := by simpa [whole] using hv
  exact (original_facet_incidence c).2 f ⟨v, hv'⟩

theorem vertexId_mem_rowIds (c : Fin 14) (s : Fin (archive c).simplices.size)
    (k : Fin 9) : ((archive c).simplices[s]).vertexIds.getD k.val 0 ∈ rowIds c s := by
  have hsize := (original_simplex_operations c s).2.1
  have hk : k.val < ((archive c).simplices[s]).vertexIds.size := by
    rw [hsize]
    exact k.isLt
  change _ ∈ ((archive c).simplices[s]).vertexIds.toList
  rw [← Array.getElem_eq_getD (h := hk) 0]
  exact Array.getElem_mem_toList hk

/-- The geometric induction is now instantiated on the same original
vertices and row ordinals used by M's physical simplex map. -/
theorem original_row_separator (c : Fin 14)
    (s t : Fin (archive c).simplices.size) (hst : s ≠ t) :
    ∃ a : AffineRow,
      (∀ k : Fin 9, evalQ a (rowVertices c s k) ≤ 0) ∧
      (∀ k : Fin 9, 0 ≤ evalQ a (rowVertices c t k)) ∧
      ∃ v ∈ whole c, evalQ a (point (archive c) v) ≠ 0 := by
  obtain ⟨a, hs, ht, v, hv, ha⟩ := pull_pair_separated
    (point (archive c)) (gate c) (facet c) (whole c) (pivot c) (children c)
    (original_gate_nonneg c) (original_facet_zero c)
    (fun _ h => h) (original_face_incidence_shape c)
    (row_mem_originalPull c s) (row_mem_originalPull c t) (rowIds_ne c s t hst)
  exact ⟨a, fun k => hs _ (vertexId_mem_rowIds c s k),
    fun k => ht _ (vertexId_mem_rowIds c t k), v, hv, ha⟩

noncomputable section

/-- Both neutral APIs evaluate the identical affine coefficient vector
on Fin8 → real. This identity is established before using M19 geometry. -/
theorem evalRow_eq_generic (a : AffineRow) (x : Point) :
    evalRow a x = P2OriginalSaving19OwnedSource.eval a x := rfl

theorem evalRow_interpolate (a : AffineRow) (v : Fin 9 → Point) (x : Point) :
    evalRow a (Bary.pointInterpolate v x) =
      Bary.interpolate (fun k => evalRow a (v k)) x := by
  simpa only [evalRow_eq_generic] using
    P2OriginalSaving19OwnedSource.eval_interpolate a v x

theorem rowSupport_eval_nonpos (c : Fin 14) (s : Fin (archive c).simplices.size)
    (a : AffineRow) (ha : ∀ k : Fin 9, evalQ a (rowVertices c s k) ≤ 0)
    {x : Point} (hx : x ∈ rowSupport c s) : evalRow a x ≤ 0 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [← Bary.vertices_interpolate, evalRow_interpolate]
  apply Finset.sum_nonpos
  intro k _
  apply mul_nonpos_of_nonneg_of_nonpos (Bary.bary_nonneg hy k)
  rw [rowMap, edge_vertices, evalQ_cast]
  exact_mod_cast ha k

theorem rowSupport_eval_nonneg (c : Fin 14) (s : Fin (archive c).simplices.size)
    (a : AffineRow) (ha : ∀ k : Fin 9, 0 ≤ evalQ a (rowVertices c s k))
    {x : Point} (hx : x ∈ rowSupport c s) : 0 ≤ evalRow a x := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [← Bary.vertices_interpolate, evalRow_interpolate]
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg (Bary.bary_nonneg hy k)
  rw [rowMap, edge_vertices, evalQ_cast]
  exact_mod_cast ha k

/-- The complete actual39741 within-cell ownership consequence. M19
supplies only affine-zero-set nullity after the proved evaluator identity;
none of its rows, polynomial lifts, endpoints, or disjointness is used. -/
theorem original_within_cell_null_overlap (c : Fin 14)
    (s t : Fin (archive c).simplices.size) (hst : s ≠ t) :
    (volume : Measure Point) (rowSupport c s ∩ rowSupport c t) = 0 := by
  obtain ⟨a, hs, ht, v, hv, ha⟩ := original_row_separator c s t hst
  apply measure_mono_null (t := {x : Point | evalRow a x = 0})
  · rintro x ⟨hxs, hxt⟩
    exact le_antisymm (rowSupport_eval_nonpos c s a hs hxs)
      (rowSupport_eval_nonneg c t a ht hxt)
  · simp_rw [evalRow_eq_generic]
    apply P2OriginalSaving19OwnedSource.affine_zero_volume
    refine ⟨castPoint (point (archive c) v), ?_⟩
    rw [← evalRow_eq_generic, evalQ_cast]
    exact_mod_cast ha

theorem original_within_cell_ae_pairwise (c : Fin 14) :
    Pairwise (fun s t : Fin (archive c).simplices.size =>
      AEDisjoint volume (rowSupport c s) (rowSupport c t)) :=
  original_within_cell_null_overlap c

theorem rowSupport_measurable (c : Fin 14) (s : Fin (archive c).simplices.size) :
    MeasurableSet (rowSupport c s) := Bary.support_measurable _ _

end
end ImbalancedChen.P2OriginalSaving16PullingOwnership
