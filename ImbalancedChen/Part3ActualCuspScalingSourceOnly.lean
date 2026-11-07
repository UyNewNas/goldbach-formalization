import ImbalancedChen.Part3ActualLiteralPacketIntegral
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-24. This file has not been compiled.

The three matrices are actual real 2 by 2 matrices. Their identities express
the ABL/DI to Pascadi scaling-matrix change at a positive level `z`.
The phase lemmas concern the existing literal packet definitions. They do not
assert a Fourier-coefficient transformation law or a spectral estimate.
-/

noncomputable section

namespace P3ActualCuspScalingSourceOnly

open P3ActualLiteralPacketIntegralSourceOnly
open P3Period64NativeReconstructionSourceOnly (e e_add)
open ImbalancedChen.Part3 (CoprimePacket)
open P3NativePeriod64SamplingSourceOnly (D4)
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

/-- Exact cancellation of the two literal charts' cusp phases. -/
theorem cuspPhase_true_mul_false (z n : ℕ) :
    cuspPhase true z n * cuspPhase false z n = 1 := by
  simp only [cuspPhase, if_true, if_false, one_mul, neg_one_mul, neg_div]
  rw [← e_add]
  simp [e]

theorem cuspPhase_false_mul_true (z n : ℕ) :
    cuspPhase false z n * cuspPhase true z n = 1 := by
  rw [mul_comm]
  exact cuspPhase_true_mul_false z n

private theorem signedCoefficient_true_cancel_core (d : CoprimePacket) (n : ℕ) :
    signedCoefficient true d n * cuspPhase false d.level n =
      if Nat.Coprime n d.residue then d.beta (d.multiplier * n) d.level else 0 := by
  by_cases hc : Nat.Coprime n d.residue
  · simp only [signedCoefficient, if_pos hc]
    rw [mul_assoc, cuspPhase_true_mul_false, mul_one]
  · simp only [signedCoefficient, if_neg hc, zero_mul]

private theorem signedCoefficient_false_cancel_core (d : CoprimePacket) (n : ℕ) :
    signedCoefficient false d n * cuspPhase true d.level n =
      if Nat.Coprime n d.residue then d.beta (d.multiplier * n) d.level else 0 := by
  by_cases hc : Nat.Coprime n d.residue
  · simp only [signedCoefficient, if_pos hc]
    rw [mul_assoc, cuspPhase_false_mul_true, mul_one]
  · simp only [signedCoefficient, if_neg hc, zero_mul]

/-- The positive chart, multiplied by its opposite phase, recovers the
actual beta entry of the existing mode packet on the coprime fibre. -/
theorem signedCoefficient_true_cancel
    (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ) (n : ℕ) :
    signedCoefficient true (modePacket d k U Z) n * cuspPhase false d.level n =
      if Nat.Coprime n d.residue then
        (modePacket d k U Z).beta (d.multiplier * n) d.level
      else 0 := by
  exact signedCoefficient_true_cancel_core (modePacket d k U Z) n

/-- The negative chart is the already defined transformed coefficient.
Multiplication by e(+n/z) exactly removes its e(-n/z) factor. -/
theorem transformedCoefficient_cancel
    (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ) (n : ℕ) :
    (modePacket d k U Z).transformedCoefficient n * cuspPhase true d.level n =
      if Nat.Coprime n d.residue then
        (modePacket d k U Z).beta (d.multiplier * n) d.level
      else 0 := by
  rw [← signedCoefficient_false_eq_actual]
  exact signedCoefficient_false_cancel_core (modePacket d k U Z) n

/-- The surviving beta entry is exactly the pre-existing `modePacket` phase
times the unmodified packet coefficient. -/
theorem signedCoefficient_true_cancel_expanded
    (d : CoprimePacket) (k : D4 → ℤ) (U Z : ℝ) (n : ℕ) :
    signedCoefficient true (modePacket d k U Z) n * cuspPhase false d.level n =
      if Nat.Coprime n d.residue then
        d.beta (d.multiplier * n) d.level *
          e ((k 2 : ℝ) / 64 * (((d.multiplier * n : ℕ) : ℝ) / U) +
            (k 3 : ℝ) / 64 * ((d.level : ℝ) / Z))
      else 0 := by
  rw [signedCoefficient_true_cancel]
  rfl

end P3ActualCuspScalingSourceOnly
