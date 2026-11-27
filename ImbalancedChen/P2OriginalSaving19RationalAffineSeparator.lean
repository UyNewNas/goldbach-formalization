import ImbalancedChen.P2OriginalSaving19RationalSimplexBridge
import ImbalancedChen.AffinePrimeGates

/-! Proper rational affine forms separate actual simplex interiors.
All hypotheses below concern coefficients and vertex signs. -/
namespace ImbalancedChen.P2OriginalSaving19RationalAffineSeparator
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P2OriginalSaving19SimplexMoments
open P2OriginalSaving19RowNumericsPure
open P2OriginalSaving19RationalSimplexBridge

abbrev Form := Fin 9 → ℚ
def evalQ (a : Form) (x : QPoint) : ℚ := a 0 + ∑ j : Fin 8, a j.succ * x j
def eval (a : Form) (x : Point) : ℝ := (a 0 : ℝ) + ∑ j : Fin 8, (a j.succ : ℝ) * x j
def linearPart (a : Form) : Point →L[ℝ] ℝ :=
  ∑ j : Fin 8, (a j.succ : ℝ) • ContinuousLinearMap.proj j

theorem eval_cast (a : Form) (x : QPoint) : eval a (realPoint x) = (evalQ a x : ℝ) := by
  simp [eval, evalQ, realPoint]

theorem eval_continuous (a : Form) : Continuous (eval a) := by
  unfold eval
  fun_prop

theorem eval_interpolate (a : Form) (v : Fin 9 → Point) (x : Point) :
    eval a (pointInterpolate v x) = interpolate (fun i => eval a (v i)) x := by
  simp only [eval, pointInterpolate_apply]
  rw [interpolate_add, interpolate_const, interpolate_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp [interpolate, Finset.mul_sum, mul_left_comm]

theorem eval_nonneg_support (a : Form) (L : Point ≃L[ℝ] Point) (b : Point)
    (hv : ∀ i, 0 ≤ eval a (vertices L b i)) {x : Point} (hx : x ∈ support L b) :
    0 ≤ eval a x := by
  obtain ⟨y, hy, rfl⟩ := hx
  change 0 ≤ eval a (b + L y)
  rw [← vertices_interpolate, eval_interpolate]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (bary_nonneg hy i) (hv i))

theorem eval_nonpos_support (a : Form) (L : Point ≃L[ℝ] Point) (b : Point)
    (hv : ∀ i, eval a (vertices L b i) ≤ 0) {x : Point} (hx : x ∈ support L b) :
    eval a x ≤ 0 := by
  obtain ⟨y, hy, rfl⟩ := hx
  change eval a (b + L y) ≤ 0
  rw [← vertices_interpolate, eval_interpolate]
  exact Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (bary_nonneg hy i) (hv i))

theorem proper_wall_null (a : Form) (h : ∃ j : Fin 8, a j.succ ≠ 0) :
    volume {x : Point | eval a x = 0} = 0 := by
  have hL : linearPart a ≠ 0 := by
    obtain ⟨j, hj⟩ := h
    intro hz
    have he := congrArg (fun f : Point →L[ℝ] ℝ => f (Pi.single j 1)) hz
    have hn : (a j.succ : ℝ) ≠ 0 := by exact_mod_cast hj
    apply hn
    simpa [linearPart, Pi.single_apply] using he
  have he : {x : Point | eval a x = 0} = {x | linearPart a x = -(a 0 : ℝ)} := by
    ext x
    simp only [mem_ofPred_eq, eval]
    have hl : linearPart a x = ∑ j : Fin 8, (a j.succ : ℝ) * x j := by
      simp [linearPart]
    rw [hl]
    constructor <;> intro hx <;> linarith
  rw [he]
  exact affinePrimeWall_volume_zero (linearPart a) hL _

theorem separated_intersection_null (a : Form)
    (L K : Point ≃L[ℝ] Point) (b c : Point)
    (proper : ∃ j : Fin 8, a j.succ ≠ 0)
    (left : ∀ i, 0 ≤ eval a (vertices L b i))
    (right : ∀ i, eval a (vertices K c i) ≤ 0) :
    volume (support L b ∩ support K c) = 0 := by
  apply measure_mono_null (t := {x : Point | eval a x = 0})
  · rintro x ⟨hx, hy⟩
    exact le_antisymm (eval_nonpos_support a K c right hy)
      (eval_nonneg_support a L b left hx)
  · exact proper_wall_null a proper

#print axioms separated_intersection_null
end
end ImbalancedChen.P2OriginalSaving19RationalAffineSeparator
