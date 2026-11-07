import ImbalancedChen.P2OriginalSaving19OwnedSource
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
SOURCE ONLY / UNCOMPILED / CREDIT 0. Closed finite guards UNEVALUATED.
Reconstruct the ORIGINAL max-pulling recursion from its face ledger and
bind its ordered output to the actual thirteen-cell rows. The matching
negative monomial lift gives exact rational supporting-face certificates.
Neither coverage nor null overlap is an input. No new literal geometry,
separator, height, facet, moment or floor table is created.
-/
namespace ImbalancedChen.P2OriginalSaving19PullingOwnership

open Set MeasureTheory Filter
open scoped BigOperators Matrix Polynomial
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P2OriginalSaving19SimplexMoments
open P2OriginalSaving19MomentFloorConsumer
open P2OriginalSaving19Archive
open P2OriginalSaving19Original28918
open P2OriginalSaving19OwnedSource

/-- Fuel is dimension+1, not an execution budget. Singleton faces are the
producer's base case; non-singletons use its original ordered facet list. -/
def pullingRows (c : Fin 13) : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | n + 1, face =>
    if face.length = 1 then [face]
    else match (geometry c).faces.toList.find? (fun f => f.vertices.toList == face) with
      | none => []
      | some f =>
        (f.facetSets.toList.filter (fun s => !s.contains f.pivot)).flatMap
          (fun s => (pullingRows c n s.toList).map (fun t => f.pivot :: t))

def properIntersections (c : Fin 13) (face : Finset Nat) : Finset (Finset Nat) :=
  (((geometry c).facetVertices.toList.map (fun f => face ∩ f.toList.toFinset)).toFinset.erase
    ∅).erase face

def maximalIntersections (c : Fin 13) (face : Finset Nat) : Finset (Finset Nat) :=
  (properIntersections c face).filter
    (fun s => ∀ t ∈ properIntersections c face, s ⊆ t → s = t)

def FaceChecks (c : Fin 13) (f : FaceRecord) : Prop :=
  f.vertices.toList.Nodup ∧ 1 < f.vertices.size ∧
  f.pivot ∈ f.vertices.toList ∧ (∀ v ∈ f.vertices.toList, v ≤ f.pivot) ∧
  (f.facetSets.toList.map (fun s => s.toList.toFinset)).toFinset =
    maximalIntersections c f.vertices.toList.toFinset ∧
  (pullingRows c (f.dimension + 1) f.vertices.toList).length = f.simplices

instance (c : Fin 13) (f : FaceRecord) : Decidable (FaceChecks c f) := by
  unfold FaceChecks
  infer_instance

/-- The ordered row IDs are reproduced from the actual original ledger.
The additional face/facet checks authenticate maximal intersections and
the max pivot; the rational supporting planes below prove the measure
consequence independently of any coverage claim. None of these bodies ran. -/
theorem original_pulling_checks :
    (∀ c, pullingRows c 9 (List.range (geometry c).vertices.size) =
      ((geometry c).rows.toList.map (fun r => r.vertexIds.toList))) ∧
    (∀ c (f : Fin (geometry c).faces.size), FaceChecks c (geometry c).faces[f.val]!) ∧
    (∀ c (f : Fin (geometry c).facetVertices.size), ∃ g : Fin 97,
      ∀ v : VertexIndex c,
        (v.val ∈ (geometry c).facetVertices[f.val]!.toList ↔
          evalQ (gate c g) (originalPoint c v) = 0)) := by
  decide

def homogeneousVertices (r : OriginalRowIndex) : Matrix (Fin 9) (Fin 9) ℚ :=
  fun k j => Fin.cases 1 (rawVertex r k) j

def heightPolynomial (v : Nat) : ℚ[X] := -Polynomial.X^v

def liftCoefficientPolynomial (r : OriginalRowIndex) (j : Fin 9) : ℚ[X] :=
  Polynomial.C (((homogeneousVertices r).det)⁻¹) *
    ∑ k : Fin 9, Polynomial.C ((homogeneousVertices r).adjugate j k) *
      heightPolynomial (vertexId r k)

def planePolynomial (r : OriginalRowIndex) (x : QPoint) : ℚ[X] :=
  liftCoefficientPolynomial r 0 +
    ∑ j : Fin 8, Polynomial.C (x j) * liftCoefficientPolynomial r j.succ

def liftPlaneAt (r : OriginalRowIndex) (b : ℚ) : AffineRow :=
  fun j => (liftCoefficientPolynomial r j).eval b

/-- Matching max-pulling ownership certificate on the ORIGINAL vertices.
The negative highest monomial makes the max pivot the first pulled vertex.
Own-vertex identities and positive leading coefficients are finite rational
equalities/inequalities, not a disjointness or integral-valued proposition.
All rows, including repeated cell-local ordinals, retain their cell ID. -/
theorem original_polynomial_faces : ∀ r : OriginalRowIndex,
    (∀ k : Fin 9, planePolynomial r (rawVertex r k) =
      heightPolynomial (vertexId r k)) ∧
    (∀ v : VertexIndex r.1, (∀ k : Fin 9, vertexId r k ≠ v.val) →
      0 < (heightPolynomial v.val - planePolynomial r (originalPoint r.1 v)).leadingCoeff) := by
  decide

/-- Row ordinals alone would not establish this. This closed test rejects
equal unordered vertex sets within each original cell. -/
theorem original_vertex_sets_distinct : ∀ c (i j : CellRow c), i ≠ j →
    ∃ k : Fin 9, ∀ l : Fin 9, vertexId ⟨c, i⟩ l ≠ vertexId ⟨c, j⟩ k := by
  decide

theorem planePolynomial_eval (r : OriginalRowIndex) (x : QPoint) (b : ℚ) :
    (planePolynomial r x).eval b = evalQ (liftPlaneAt r b) x := by
  simp [planePolynomial, liftPlaneAt, evalQ, mul_comm]

/-- Positive leading coefficient also handles constant residuals. -/
theorem polynomial_eventually_positive (p : ℚ[X]) (hp : 0 < p.leadingCoeff) :
    ∀ᶠ b : ℚ in atTop, 0 < p.eval b := by
  by_cases hd : 0 < p.degree
  · exact (p.tendsto_atTop_of_leadingCoeff_nonneg hd hp.le).eventually
      (eventually_gt_atTop 0)
  · have he : p = Polynomial.C (p.coeff 0) :=
      Polynomial.eq_C_of_degree_le_zero (le_of_not_gt hd)
    rw [he] at hp ⊢
    simpa using Filter.Eventually.of_forall (fun _ : ℚ => hp)

theorem exists_common_lifting_parameter : ∃ b : ℚ, ∀ r : OriginalRowIndex,
    ∀ v : VertexIndex r.1, (∀ k : Fin 9, vertexId r k ≠ v.val) →
      evalQ (liftPlaneAt r b) (originalPoint r.1 v) < -(b^v.val) := by
  classical
  have he : ∀ᶠ b : ℚ in atTop, ∀ r : OriginalRowIndex,
      ∀ v : VertexIndex r.1, (∀ k : Fin 9, vertexId r k ≠ v.val) →
        evalQ (liftPlaneAt r b) (originalPoint r.1 v) < -(b^v.val) := by
    apply eventually_all.mpr
    intro r
    apply eventually_all.mpr
    intro v
    by_cases hv : ∀ k : Fin 9, vertexId r k ≠ v.val
    · have hp := polynomial_eventually_positive
        (heightPolynomial v.val - planePolynomial r (originalPoint r.1 v))
        ((original_polynomial_faces r).2 v hv)
      filter_upwards [hp] with b hb _
      simpa [Polynomial.eval_sub, heightPolynomial, planePolynomial_eval, sub_pos] using hb
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hv h))
  exact he.exists

noncomputable section

def heightBase : ℚ := Classical.choose exists_common_lifting_parameter
def height (v : Nat) : ℚ := -(heightBase^v)
def liftPlane (r : OriginalRowIndex) : AffineRow := liftPlaneAt r heightBase

theorem own_vertex_lift (r : OriginalRowIndex) (k : Fin 9) :
    evalQ (liftPlane r) (rawVertex r k) = height (vertexId r k) := by
  have h := congrArg (Polynomial.eval heightBase) ((original_polynomial_faces r).1 k)
  simpa [planePolynomial_eval, heightPolynomial, liftPlane, height] using h

theorem off_vertex_lift (r : OriginalRowIndex) (v : VertexIndex r.1)
    (hv : ∀ k : Fin 9, vertexId r k ≠ v.val) :
    evalQ (liftPlane r) (originalPoint r.1 v) < height v.val :=
  Classical.choose_spec exists_common_lifting_parameter r v hv

theorem all_vertex_lift (r : OriginalRowIndex) (v : VertexIndex r.1) :
    evalQ (liftPlane r) (originalPoint r.1 v) ≤ height v.val := by
  by_cases hv : ∃ k : Fin 9, vertexId r k = v.val
  · obtain ⟨k, hk⟩ := hv
    have hp : rawVertex r k = originalPoint r.1 v := by
      ext j
      simp only [P2OriginalSaving19Original28918.rawVertex,
        P2OriginalSaving19Archive.rawVertex, originalPoint, vertexId] at hk ⊢
      rw [hk]
    have h := own_vertex_lift r k
    rw [hp, hk] at h
    exact h.le
  · exact (off_vertex_lift r v (by simpa only [not_exists] using hv)).le

theorem lift_value_on_vertex (r : OriginalRowIndex) (k : Fin 9) :
    eval (liftPlane r) (vertices (rowLinear r) (rowBase r) k) =
      (height (vertexId r k) : ℝ) := by
  rw [row_vertices, eval_cast, own_vertex_lift]

theorem lift_below_vertex (c : Fin 13) (i j : CellRow c) (k : Fin 9) :
    eval (liftPlane ⟨c, i⟩) (vertices (rowLinear ⟨c, j⟩) (rowBase ⟨c, j⟩) k) ≤
      eval (liftPlane ⟨c, j⟩) (vertices (rowLinear ⟨c, j⟩) (rowBase ⟨c, j⟩) k) := by
  rw [lift_value_on_vertex, row_vertices, eval_cast, rawVertex_lookup]
  exact_mod_cast all_vertex_lift ⟨c, i⟩
    ⟨vertexId ⟨c, j⟩ k, vertexId_bound ⟨c, j⟩ k⟩

/-- Barycentric interpolation transfers supporting-plane inequalities to
every point of the original physical simplex. -/
theorem lift_below_on_support (c : Fin 13) (i j : CellRow c) {x : Point}
    (hx : x ∈ actualSupport ⟨c, j⟩) :
    eval (liftPlane ⟨c, i⟩) x ≤ eval (liftPlane ⟨c, j⟩) x := by
  obtain ⟨y, hy, rfl⟩ := hx
  simp_rw [← vertices_interpolate (rowLinear ⟨c, j⟩) (rowBase ⟨c, j⟩), eval_interpolate]
  unfold interpolate
  exact Finset.sum_le_sum (fun k _ =>
    mul_le_mul_of_nonneg_left (lift_below_vertex c i j k) (bary_nonneg hy k))

def separatingRow (c : Fin 13) (i j : CellRow c) : AffineRow :=
  liftPlane ⟨c, i⟩ - liftPlane ⟨c, j⟩

theorem separatingRow_nonzero (c : Fin 13) (i j : CellRow c) (hij : i ≠ j) :
    ∃ x : Point, eval (separatingRow c i j) x ≠ 0 := by
  obtain ⟨k, hk⟩ := original_vertex_sets_distinct c i j hij
  have hs : eval (liftPlane ⟨c, i⟩)
      (vertices (rowLinear ⟨c, j⟩) (rowBase ⟨c, j⟩) k) <
      eval (liftPlane ⟨c, j⟩)
      (vertices (rowLinear ⟨c, j⟩) (rowBase ⟨c, j⟩) k) := by
    rw [lift_value_on_vertex, row_vertices, eval_cast, rawVertex_lookup]
    exact_mod_cast off_vertex_lift ⟨c, i⟩
      ⟨vertexId ⟨c, j⟩ k, vertexId_bound ⟨c, j⟩ k⟩ hk
  refine ⟨vertices (rowLinear ⟨c, j⟩) (rowBase ⟨c, j⟩) k, ?_⟩
  simpa only [separatingRow, eval_sub, sub_ne_zero] using ne_of_lt hs

theorem intersection_on_separating_wall (c : Fin 13) (i j : CellRow c) :
    actualSupport ⟨c, i⟩ ∩ actualSupport ⟨c, j⟩ ⊆
      {x | eval (separatingRow c i j) x = 0} := by
  rintro x ⟨hi, hj⟩
  change eval (separatingRow c i j) x = 0
  rw [separatingRow, eval_sub]
  exact sub_eq_zero.mpr (le_antisymm
    (lift_below_on_support c i j hj) (lift_below_on_support c j i hi))

theorem original_within_cell_null_overlap (c : Fin 13) (i j : CellRow c) (hij : i ≠ j) :
    volume (actualSupport ⟨c, i⟩ ∩ actualSupport ⟨c, j⟩) = 0 :=
  measure_mono_null (intersection_on_separating_wall c i j)
    (affine_zero_volume (separatingRow c i j) (separatingRow_nonzero c i j hij))

end
end ImbalancedChen.P2OriginalSaving19PullingOwnership
