import ImbalancedChen.P2OriginalSixthSimplexMoments
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The genuine6D edge matrix. The original row-edge determinant is
transposed solely for the column convention of the affine map.
Physical volume is abs(det6)/6!, with no additional chart multiplier.
-/
namespace ImbalancedChen.P2OriginalSixthSimplexBinding
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2OriginalSixthSimplexMoments (Point)
abbrev QPoint := Fin 6 → ℚ
def castPoint (x : QPoint) : Point := fun j => (x j : ℝ)
def edgeMatrix (v : Fin 7 → QPoint) : Matrix (Fin 6) (Fin 6) ℚ :=
  fun i j => v i.succ j - v 0 j
def physicalVolumeQ (v : Fin 7 → QPoint) : ℚ := |(edgeMatrix v).det| / (6.factorial : ℚ)

def edgeLinear (v : Fin 7 → QPoint) : Point →L[ℝ] Point :=
  (Matrix.toLin' ((edgeMatrix v).transpose.map (fun q => (q : ℝ)))).toContinuousLinearMap

theorem edgeLinear_det (v : Fin 7 → QPoint) :
    (edgeLinear v).det = ((edgeMatrix v).det : ℝ) := by
  rw [edgeLinear, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin',
    ← Rat.cast_det, Matrix.det_transpose]

def edgeEquiv (v : Fin 7 → QPoint) (h : (edgeMatrix v).det ≠ 0) : Point ≃L[ℝ] Point :=
  (edgeLinear v).toContinuousLinearEquivOfDetNeZero (by
    rw [edgeLinear_det]
    exact_mod_cast h)

/-- The transposition matches the producer's row-edge determinant with
the column convention of the physical affine map. -/
theorem edge_vertices (v : Fin 7 → QPoint) (h : (edgeMatrix v).det ≠ 0) :
    P2OriginalSixthSimplexMoments.vertices (edgeEquiv v h) (castPoint (v 0)) = fun i => castPoint (v i) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [P2OriginalSixthSimplexMoments.vertices]
  · intro k
    ext j
    simp [P2OriginalSixthSimplexMoments.vertices, edgeEquiv, edgeLinear, Matrix.toLin'_apply,
      Matrix.mulVec_single, Matrix.transpose_apply, Matrix.map_apply,
      edgeMatrix, castPoint]

theorem physicalVolumeQ_cast (v : Fin 7 → QPoint) (h : (edgeMatrix v).det ≠ 0) :
    (physicalVolumeQ v : ℝ) = P2OriginalSixthSimplexMoments.physicalVolume (edgeEquiv v h) := by
  simp only [physicalVolumeQ, P2OriginalSixthSimplexMoments.physicalVolume, P2OriginalSixthSimplexMoments.jacobian, edgeEquiv,
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero, edgeLinear_det,
    Rat.cast_div, Rat.cast_abs, Rat.cast_natCast]

end
end ImbalancedChen.P2OriginalSixthSimplexBinding
