import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-! Existing actual cusp matrices, separated from the packet assembly. -/

noncomputable section
namespace P3ActualCuspScalingSourceOnly
open scoped MatrixGroups UpperHalfPlane

def oldScaling (z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.sqrt z, 0; Real.sqrt z, 1 / Real.sqrt z]

def newScaling (z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.sqrt z, -(1 / Real.sqrt z); Real.sqrt z, 0]

def translation (z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 1 / z; 0, 1]

theorem oldScaling_det (z : ℝ) (hz : 0 < z) :
    Matrix.det (oldScaling z) = 1 := by
  have hs : Real.sqrt z ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hz)
  simp [oldScaling, Matrix.det_fin_two_of, hs]

theorem newScaling_det (z : ℝ) (hz : 0 < z) :
    Matrix.det (newScaling z) = 1 := by
  have hs : Real.sqrt z ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hz)
  simp [newScaling, Matrix.det_fin_two_of, hs]

theorem translation_det (z : ℝ) : Matrix.det (translation z) = 1 := by
  simp [translation, Matrix.det_fin_two_of]

theorem oldScaling_eq_newScaling_mul_translation (z : ℝ) (hz : 0 < z) :
    oldScaling z = newScaling z * translation z := by
  have hs : Real.sqrt z ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hz)
  have hdiv : Real.sqrt z / z = 1 / Real.sqrt z := by
    apply (div_eq_div_iff (ne_of_gt hz) hs).2
    simpa [pow_two] using (Real.sq_sqrt (le_of_lt hz))
  have hmul : Real.sqrt z * (1 / z) = 1 / Real.sqrt z := by
    calc
      Real.sqrt z * (1 / z) = Real.sqrt z / z := by ring
      _ = 1 / Real.sqrt z := hdiv
  change
    !![Real.sqrt z, 0; Real.sqrt z, 1 / Real.sqrt z] =
      !![Real.sqrt z, -(1 / Real.sqrt z); Real.sqrt z, 0] *
        !![1, 1 / z; 0, 1]
  rw [Matrix.mul_fin_two]
  simp only [one_div] at hmul
  simp [hmul]

def oldSL (z : ℝ) (hz : 0 < z) : SL(2, ℝ) :=
  ⟨oldScaling z, oldScaling_det z hz⟩

def newSL (z : ℝ) (hz : 0 < z) : SL(2, ℝ) :=
  ⟨newScaling z, newScaling_det z hz⟩

def translationSL (z : ℝ) : SL(2, ℝ) :=
  ⟨translation z, translation_det z⟩

theorem oldSL_eq_newSL_mul_translationSL (z : ℝ) (hz : 0 < z) :
    oldSL z hz = newSL z hz * translationSL z := by
  apply Subtype.ext
  change oldScaling z = newScaling z * translation z
  exact oldScaling_eq_newScaling_mul_translation z hz

/-- The existing upper-half-plane action respects the scaling-matrix
identity, including the right-hand translation. -/
theorem oldSL_smul_eq (z : ℝ) (hz : 0 < z) (w : ℍ) :
    oldSL z hz • w = newSL z hz • (translationSL z • w) := by
  rw [oldSL_eq_newSL_mul_translationSL z hz, mul_smul]

end P3ActualCuspScalingSourceOnly
end
