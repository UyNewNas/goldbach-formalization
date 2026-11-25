import ImbalancedChen.Part3CuspScalingMatrices
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
