import ImbalancedChen.P2OriginalSaving19SimplexMoments
import ImbalancedChen.AffinePrimeGates

/-!
SOURCE ONLY / NOT COMPILED.

Mechanical extraction of the six existing affine interpolation and null-wall
helpers from P2OriginalSaving19OwnedSource. Their original namespace,
declaration text and proof bodies are retained. This module imports no
original28918 archive or its source data. The original owner imports this
module and keeps its remaining source-specific declarations unchanged.
-/
namespace ImbalancedChen.P2OriginalSaving19OwnedSource

open Set MeasureTheory
open scoped BigOperators
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P2OriginalSaving19SimplexMoments
open OriginalDescendingFifteenLiteralAffineRows (evaluateCoefficients)

abbrev AffineRow := Fin 9 → ℚ

noncomputable section

def eval (a : AffineRow) (x : Point) : ℝ := evaluateCoefficients a x

theorem eval_interpolate (a : AffineRow) (v : Fin 9 → Point) (x : Point) :
    eval a (pointInterpolate v x) = interpolate (fun k => eval a (v k)) x := by
  simp only [eval, evaluateCoefficients, pointInterpolate_apply]
  rw [interpolate_add, interpolate_const, interpolate_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp [interpolate, Finset.mul_sum, mul_assoc, mul_left_comm]

def linearPart (a : AffineRow) : Point →L[ℝ] ℝ :=
  ∑ j : Fin 8, (a j.succ : ℝ) • ContinuousLinearMap.proj j

theorem eval_eq_affine (a : AffineRow) (x : Point) :
    eval a x = (a 0 : ℝ) + linearPart a x := by
  simp [eval, evaluateCoefficients, linearPart]

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

end
end ImbalancedChen.P2OriginalSaving19OwnedSource
