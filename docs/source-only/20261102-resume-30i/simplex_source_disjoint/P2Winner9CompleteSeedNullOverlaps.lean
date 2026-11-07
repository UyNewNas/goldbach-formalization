import ImbalancedChen.P2Winner9CompleteSeedSourceGates
import Mathlib.Analysis.Polynomial.Basic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
An independent regular-lifting certificate for the ACTUAL 11026 stored
simplex supports. No triangulation theorem, coverage premise, source-ID
injectivity surrogate or imported JSON checker result is used. Exact
polynomial lifting rows are decoded from the existing 201 rational vertices;
there is no new literal face/height/normal archive. All closed finite proof
bodies remain UNEXECUTED and their evaluation feasibility is not claimed.
-/
namespace ImbalancedChen.P2Winner9CompleteSeedNullOverlaps

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Matrix Polynomial
open P2Winner9CompleteSeedData P2Winner9CompleteSeedPositiveDomains
open P2Winner9CompleteSeedSourceGates
open P2Winner9SelectedRowRealJacobian P2Winner9SelectedRowAnalyticCaps
open P2Winner9PhysicalAffineTransfer P2Winner9PhysicalVertexInterpolation
open P2Winner9BarycentricMixedDegreeOne

def homogeneousVertices (i : RowIndex) : Matrix (Fin 9) (Fin 9) ℚ :=
  fun k j => Fin.cases 1 (physicalVertices i k) j
def heightPolynomial (v : ℕ) : ℚ[X] := -Polynomial.X^v
def liftCoefficientPolynomial (i : RowIndex) (j : Fin 9) : ℚ[X] :=
  Polynomial.C (((homogeneousVertices i).det)⁻¹) *
    ∑ k : Fin 9, Polynomial.C ((homogeneousVertices i).adjugate j k) *
      heightPolynomial ((entry i).vertexIds k)
def planePolynomial (i : RowIndex) (x : Fin 8 → ℚ) : ℚ[X] :=
  liftCoefficientPolynomial i 0 +
    ∑ j : Fin 8, Polynomial.C (x j) * liftCoefficientPolynomial i j.succ
def liftPlaneAt (i : RowIndex) (b : ℚ) : Row :=
  ⟨(liftCoefficientPolynomial i 0).eval b,
    fun j => (liftCoefficientPolynomial i j.succ).eval b⟩

/-- Source-only exact regular-face certificate. It checks polynomials of
degree at most 200, never evaluates a tower-sized integer height. Own-vertex
identities and positive leading coefficients at every nonincident original
vertex replace an assumed pulling triangulation. UNEXECUTED finite body. -/
theorem all_original_polynomial_faces : ∀ i : RowIndex,
    (∀ k : Fin 9, planePolynomial i (physicalVertices i k) =
      heightPolynomial ((entry i).vertexIds k)) ∧
    (∀ v : VertexIndex, (∀ k : Fin 9, (entry i).vertexIds k ≠ v.val) →
      0 < (heightPolynomial v.val - planePolynomial i (originalPoint v)).leadingCoeff) := by
  decide +kernel

theorem planePolynomial_eval (i : RowIndex) (x : Fin 8 → ℚ) (b : ℚ) :
    (planePolynomial i x).eval b = (liftPlaneAt i b).evalQ x := by
  simp [planePolynomial, liftPlaneAt, Row.evalQ, mul_comm]

/-- Pure analysis: positive leading coefficient gives eventual positivity,
including degree zero. No positivity-at-a-chosen-base premise is used. -/
theorem polynomial_eventually_positive (p : ℚ[X]) (hp : 0 < p.leadingCoeff) :
    ∀ᶠ b : ℚ in atTop, 0 < p.eval b := by
  by_cases hd : 0 < p.degree
  · exact (p.tendsto_atTop_of_leadingCoeff_nonneg hd hp.le).eventually
      (eventually_gt_atTop 0)
  · have he : p = Polynomial.C (p.coeff 0) :=
      Polynomial.eq_C_of_degree_le_zero (le_of_not_gt hd)
    rw [he] at hp ⊢
    simpa using Filter.Eventually.of_forall (fun _ : ℚ => hp)

/-- One rational parameter works for all actual rows and all 201 original
vertices. Finiteness is used analytically; no search for this parameter runs. -/
theorem exists_common_lifting_parameter : ∃ b : ℚ, ∀ i : RowIndex, ∀ v : VertexIndex,
    (∀ k : Fin 9, (entry i).vertexIds k ≠ v.val) →
      (liftPlaneAt i b).evalQ (originalPoint v) < -(b^v.val) := by
  classical
  have he : ∀ᶠ b : ℚ in atTop, ∀ i : RowIndex, ∀ v : VertexIndex,
      (∀ k : Fin 9, (entry i).vertexIds k ≠ v.val) →
        (liftPlaneAt i b).evalQ (originalPoint v) < -(b^v.val) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro v
    by_cases hv : ∀ k : Fin 9, (entry i).vertexIds k ≠ v.val
    · have hp := polynomial_eventually_positive
        (heightPolynomial v.val - planePolynomial i (originalPoint v))
        ((all_original_polynomial_faces i).2 v hv)
      filter_upwards [hp] with b hb _
      simpa [Polynomial.eval_sub, heightPolynomial, planePolynomial_eval, sub_pos] using hb
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hv h))
  exact he.exists

def heightBase : ℚ := Classical.choose exists_common_lifting_parameter
def height (v : ℕ) : ℚ := -(heightBase^v)
def liftPlane (i : RowIndex) : Row := liftPlaneAt i heightBase

/-- The supporting inequalities are now DERIVED from exact polynomial
faces and one common analytic parameter; they are not a certificate input. -/
theorem all_original_lifting_faces (i : RowIndex) :
    (∀ k : Fin 9, (liftPlane i).evalQ (physicalVertices i k) =
      height ((entry i).vertexIds k)) ∧
    (∀ v : VertexIndex, (liftPlane i).evalQ (originalPoint v) ≤ height v.val) ∧
    (∀ v : VertexIndex, (∀ k : Fin 9, (entry i).vertexIds k ≠ v.val) →
      (liftPlane i).evalQ (originalPoint v) < height v.val) := by
  have hown (k : Fin 9) : (liftPlane i).evalQ (physicalVertices i k) =
      height ((entry i).vertexIds k) := by
    have h := congrArg (Polynomial.eval heightBase) ((all_original_polynomial_faces i).1 k)
    simpa [planePolynomial_eval, heightPolynomial, liftPlane, height] using h
  have hoff (v : VertexIndex) (hv : ∀ k : Fin 9, (entry i).vertexIds k ≠ v.val) :
      (liftPlane i).evalQ (originalPoint v) < height v.val :=
    Classical.choose_spec exists_common_lifting_parameter i v hv
  refine ⟨hown, ?_, hoff⟩
  intro v
  by_cases hv : ∃ k : Fin 9, (entry i).vertexIds k = v.val
  · obtain ⟨k, hk⟩ := hv
    have hpoint : physicalVertices i k = originalPoint v := by
      simp only [physicalVertices, originalPoint, hk]
    have h := hown k
    rw [hpoint, hk] at h
    exact h.le
  · exact (hoff v (by simpa only [not_exists] using hv)).le

/-- Different original simplices have different geometric vertex sets.
This finite source body is also unexecuted. Ordinal uniqueness alone would
not establish it. Equal unordered rows would fail this proposition. -/
theorem actual_vertex_set_distinct : ∀ i j : RowIndex, i ≠ j →
    ∃ k : Fin 9, ∀ l : Fin 9, (entry i).vertexIds l ≠ (entry j).vertexIds k := by
  decide +kernel

theorem lift_value_on_vertex (i : RowIndex) (k : Fin 9) :
    (liftPlane i).eval (realVertices (physicalVertices i) k) =
      (height ((entry i).vertexIds k) : ℝ) := by
  rw [realVertices, Row.eval_cast]
  exact_mod_cast (all_original_lifting_faces i).1 k

theorem lift_below_vertex (i j : RowIndex) (k : Fin 9) :
    (liftPlane i).eval (realVertices (physicalVertices j) k) ≤
      (liftPlane j).eval (realVertices (physicalVertices j) k) := by
  rw [lift_value_on_vertex]
  let v : VertexIndex := ⟨(entry j).vertexIds k, vertex_id_bound j k⟩
  change (liftPlane i).eval (fun a => (physicalVertices j k a : ℝ)) ≤ _
  rw [actual_vertex_lookup, Row.eval_cast]
  exact_mod_cast (all_original_lifting_faces i).2.1 v

/-- On each actual simplex its own lifted plane dominates every other
plane. This transports rational supporting-face inequalities through the
actual physical barycentric map. -/
theorem lift_below_on_support (i j : RowIndex) {x : Ambient}
    (hx : x ∈ actualSupport j) : (liftPlane i).eval x ≤ (liftPlane j).eval x := by
  rcases hx with ⟨y, hy, rfl⟩
  rw [Row.eval_vertexMap, Row.eval_vertexMap]
  unfold affine
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_right (lift_below_vertex i j k) (barycentric_nonneg hy k)

def separatingRow (i j : RowIndex) : Row := (liftPlane i).sub (liftPlane j)

theorem separatingRow_nonzero (i j : RowIndex) (hij : i ≠ j) :
    ∃ x : Ambient, (separatingRow i j).eval x ≠ 0 := by
  obtain ⟨k, hk⟩ := actual_vertex_set_distinct i j hij
  let v : VertexIndex := ⟨(entry j).vertexIds k, vertex_id_bound j k⟩
  have hr : (liftPlane i).evalQ (originalPoint v) < height v.val :=
    (all_original_lifting_faces i).2.2 v hk
  have hs : (liftPlane i).eval (realVertices (physicalVertices j) k) <
      (liftPlane j).eval (realVertices (physicalVertices j) k) := by
    rw [lift_value_on_vertex]
    change (liftPlane i).eval (fun a => (physicalVertices j k a : ℝ)) < _
    rw [actual_vertex_lookup, Row.eval_cast]
    exact_mod_cast hr
  refine ⟨realVertices (physicalVertices j) k, ?_⟩
  simpa only [separatingRow, Row.eval_sub, sub_ne_zero] using ne_of_lt hs

theorem intersection_on_separating_wall (i j : RowIndex) :
    actualSupport i ∩ actualSupport j ⊆ {x | (separatingRow i j).eval x = 0} := by
  rintro x ⟨hi, hj⟩
  have h₁ := lift_below_on_support i j hj
  have h₂ := lift_below_on_support j i hi
  change (separatingRow i j).eval x = 0
  rw [separatingRow, Row.eval_sub]
  exact sub_eq_zero.mpr (le_antisymm h₁ h₂)

/-- Genuine pairwise null intersection of the original physical supports,
including intersections along arbitrary lower-dimensional faces. -/
theorem all_actual_supports_null_overlap (i j : RowIndex) (hij : i ≠ j) :
    volume (actualSupport i ∩ actualSupport j) = 0 :=
  measure_mono_null (intersection_on_separating_wall i j)
    (Row.zero_volume (separatingRow i j) (separatingRow_nonzero i j hij))

/-- A single finite exceptional set handles all original source walls and
all simplex overlaps. Its removal changes none of the 11026 integrals. -/
def overlapSet : Set Ambient :=
  ⋃ i : RowIndex, ⋃ j : RowIndex, if i = j then ∅ else actualSupport i ∩ actualSupport j
def exceptionalSet : Set Ambient := sourceWalls ∪ overlapSet
def legalOwnedSupport (i : RowIndex) : Set Ambient := actualSupport i \ exceptionalSet

theorem overlapSet_null : volume overlapSet = 0 := by
  apply measure_iUnion_null
  intro i
  apply measure_iUnion_null
  intro j
  by_cases h : i = j
  · simp [h]
  · simp only [if_neg h]
    exact all_actual_supports_null_overlap i j h

theorem exceptionalSet_null : volume exceptionalSet = 0 :=
  measure_union_null sourceWalls_null overlapSet_null

theorem exceptionalSet_measurable : MeasurableSet exceptionalSet := by
  apply sourceWalls_measurable.union
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  by_cases h : i = j
  · simp [h]
  · simp only [if_neg h]
    exact (all_actual_support_measurable i).inter (all_actual_support_measurable j)

theorem legalOwnedSupport_measurable (i : RowIndex) : MeasurableSet (legalOwnedSupport i) :=
  (all_actual_support_measurable i).diff exceptionalSet_measurable

theorem legalOwnedSupport_subset_source (i : RowIndex) :
    legalOwnedSupport i ⊆ originalPhysicalSource := by
  rintro x ⟨hx, he⟩
  exact support_off_walls_in_original_source i ⟨hx, fun hw => he (Or.inl hw)⟩

theorem legalOwnedSupport_pairwise_disjoint :
    Pairwise (fun i j : RowIndex => Disjoint (legalOwnedSupport i) (legalOwnedSupport j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro x ⟨hi, he⟩ ⟨hj, _⟩
  apply he
  right
  apply mem_iUnion.mpr
  refine ⟨i, mem_iUnion.mpr ⟨j, ?_⟩⟩
  simpa only [if_neg hij] using And.intro hi hj

theorem legalOwnedSupport_ae_eq (i : RowIndex) :
    legalOwnedSupport i =ᵐ[volume] actualSupport i := by
  have he : ∀ᵐ x : Ambient ∂volume, x ∉ exceptionalSet := by
    rw [ae_iff]
    simpa only [not_not] using exceptionalSet_null
  filter_upwards [he] with x hx
  simp [legalOwnedSupport, hx]

end
end ImbalancedChen.P2Winner9CompleteSeedNullOverlaps
