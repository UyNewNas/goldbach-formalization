import ImbalancedChen.P2OriginalSaving19Original28918
import ImbalancedChen.AffinePrimeGates

/-!
SOURCE ONLY / UNCOMPILED / ZERO CREDIT. Closed rational proof terms below
are UNEVALUATED. These are the ORIGINAL13/28918 rows, not the unequal seed.
The 97 source gates are the existing literal ascending rows whose semantics
are proved by J. All original constraints, not just candidate facets, are
checked at the original vertices. No source inclusion is a premise.
-/
namespace ImbalancedChen.P2OriginalSaving19OwnedSource

open Set MeasureTheory
open scoped BigOperators
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P2OriginalSaving19SimplexMoments
open P2OriginalSaving19MomentFloorConsumer
open P2OriginalSaving19Archive
open P2OriginalSaving19Original28918
open OriginalAscendingThirteenCellOwnership
open OriginalAscendingThirteenLiteralAffineRows
open OriginalAscendingThirteenExportOwnershipJoin
open OriginalDescendingFifteenLiteralAffineRows (evaluateCoefficients)

abbrev CellRow (c : Fin 13) := Fin (originalRowCount c)
abbrev VertexIndex (c : Fin 13) := Fin (geometry c).vertices.size

def originalPoint (c : Fin 13) (v : VertexIndex c) : QPoint :=
  fun j => ((geometry c).vertices[v.val]!)[j.val]!

def vertexId (r : OriginalRowIndex) (k : Fin 9) : Nat :=
  (rawGeometryRow r).vertexIds[k.val]!

theorem vertexId_bound (r : OriginalRowIndex) (k : Fin 9) :
    vertexId r k < (geometry r.1).vertices.size :=
  (original_row_shapes r).2.2.2.2.1 k

theorem rawVertex_lookup (r : OriginalRowIndex) (k : Fin 9) :
    rawVertex r k = originalPoint r.1 ⟨vertexId r k, vertexId_bound r k⟩ := rfl

abbrev AffineRow := Fin 9 → ℚ

def evalQ (a : AffineRow) (x : QPoint) : ℚ := a 0 + ∑ j, a j.succ * x j

def gate (c : Fin 13) (g : Fin 97) : AffineRow := exportedCoefficients c g

/-- Original source-data obligations, never accepted as inputs. The two
identically zero producer rows were excluded by J, so all 97 are proper. -/
theorem original_gate_checks :
    (∀ c g, ∃ j : Fin 8, gate c g j.succ ≠ 0) ∧
    (∀ c (v : VertexIndex c) g, 0 ≤ evalQ (gate c g) (originalPoint c v)) := by
  decide

noncomputable section

def actualSupport (r : OriginalRowIndex) : Set Point := support (rowLinear r) (rowBase r)

def eval (a : AffineRow) (x : Point) : ℝ := evaluateCoefficients a x

@[simp] theorem eval_cast (a : AffineRow) (x : QPoint) :
    eval a (realPoint x) = (evalQ a x : ℝ) := by
  simp [eval, evalQ, evaluateCoefficients, realPoint]

@[simp] theorem eval_sub (a b : AffineRow) (x : Point) :
    eval (a - b) x = eval a x - eval b x := by
  simp [eval, evaluateCoefficients, sub_mul, Finset.sum_sub_distrib]
  ring

theorem eval_interpolate (a : AffineRow) (v : Fin 9 → Point) (x : Point) :
    eval a (pointInterpolate v x) = interpolate (fun k => eval a (v k)) x := by
  simp only [eval, evaluateCoefficients, pointInterpolate_apply]
  rw [interpolate_add, interpolate_const, interpolate_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp [interpolate, Finset.mul_sum, mul_assoc, mul_left_comm]

theorem eval_nonneg_on_support (a : AffineRow) (r : OriginalRowIndex)
    (hv : ∀ k, 0 ≤ evalQ a (rawVertex r k)) {x : Point}
    (hx : x ∈ actualSupport r) : 0 ≤ eval a x := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [← vertices_interpolate, eval_interpolate]
  unfold interpolate
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg (bary_nonneg hy k)
  rw [row_vertices, eval_cast]
  exact_mod_cast hv k

def linearPart (a : AffineRow) : Point →L[ℝ] ℝ :=
  ∑ j : Fin 8, (a j.succ : ℝ) • ContinuousLinearMap.proj j

theorem eval_eq_affine (a : AffineRow) (x : Point) :
    eval a x = (a 0 : ℝ) + linearPart a x := by
  simp [eval, evaluateCoefficients, linearPart]

theorem eval_continuous (a : AffineRow) : Continuous (eval a) := by
  simp only [eval_eq_affine]
  fun_prop

/-- Proper affine walls are null, including nonzero constant walls. -/
theorem affine_zero_volume (a : AffineRow) (h : ∃ x : Point, eval a x ≠ 0) :
    volume {x | eval a x = 0} = 0 := by
  by_cases hL : linearPart a = 0
  · obtain ⟨x, hx⟩ := h
    have hc : (a 0 : ℝ) ≠ 0 := by simpa [eval_eq_affine, hL] using hx
    have he : {x : Point | eval a x = 0} = ∅ := by
      ext y
      simp [eval_eq_affine, hL, hc]
    rw [he, measure_empty]
  · have he : {x : Point | eval a x = 0} = {x | linearPart a x = -(a 0 : ℝ)} := by
      ext x
      simp only [mem_setOf_eq, eval_eq_affine]
      constructor <;> intro hx <;> linarith
    rw [he]
    exact affinePrimeWall_volume_zero (linearPart a) hL _

def sourceWalls (c : Fin 13) : Set Point := ⋃ g : Fin 97, {x | eval (gate c g) x = 0}

theorem gate_zero_volume (c : Fin 13) (g : Fin 97) :
    volume {x | eval (gate c g) x = 0} = 0 := by
  apply affine_zero_volume
  obtain ⟨j, hj⟩ := original_gate_checks.1 c g
  by_cases hc : gate c g 0 = 0
  · refine ⟨Pi.single j 1, ?_⟩
    simpa [eval, evaluateCoefficients, hc, Pi.single_apply] using
      (show (gate c g j.succ : ℝ) ≠ 0 by exact_mod_cast hj)
  · refine ⟨0, ?_⟩
    simpa [eval, evaluateCoefficients] using
      (show (gate c g 0 : ℝ) ≠ 0 by exact_mod_cast hc)

theorem sourceWalls_null (c : Fin 13) : volume (sourceWalls c) = 0 :=
  measure_iUnion_null (gate_zero_volume c)

theorem sourceWalls_measurable (c : Fin 13) : MeasurableSet (sourceWalls c) :=
  MeasurableSet.iUnion (fun g =>
    (isClosed_eq (eval_continuous (gate c g)) continuous_const).measurableSet)

theorem all_supports_closed_gates (r : OriginalRowIndex) {x : Point}
    (hx : x ∈ actualSupport r) (g : Fin 97) : 0 ≤ eval (gate r.1 g) x := by
  apply eval_nonneg_on_support _ r _ hx
  intro k
  rw [rawVertex_lookup]
  exact original_gate_checks.2 _ _ _

/-- Closed simplices reach strict original cells only off the actual
proper source walls. No boundary vertex is declared strict. -/
theorem support_off_walls_in_cell (r : OriginalRowIndex) :
    actualSupport r \ sourceWalls r.1 ⊆ cell r.1 := by
  rintro x ⟨hx, hw⟩
  apply (strictExportedRows_iff_StrictRows r.1 x).mp
  intro g
  have hge := all_supports_closed_gates r hx g
  have hne : eval (gate r.1 g) x ≠ 0 := fun he => hw (mem_iUnion.mpr ⟨g, he⟩)
  exact lt_of_le_of_ne hge (Ne.symm hne)

theorem actualSupport_measurable (r : OriginalRowIndex) : MeasurableSet (actualSupport r) :=
  support_measurable _ _

end
end ImbalancedChen.P2OriginalSaving19OwnedSource
