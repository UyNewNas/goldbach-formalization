import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Existing phase definitions relocated without changing their qualified names.
The moves of `e`, `e_add` and `cuspPhase` are recorded in
`docs/part3-distribution/p34-20261125/DECLARATION_MOVES.json`. The move of `norm_e` and the
shared unfolding equation are recorded in `docs/part3-distribution/p34-20261126/DECLARATION_MOVES.json`. -/

noncomputable section
namespace P3Period64NativeReconstructionSourceOnly

def e (s : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))

lemma e_add (s t : ℝ) : e (s+t) = e s * e t := by
  dsimp [e]
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]

lemma norm_e (s : ℝ) : ‖e s‖ = 1 := by
  simp [e, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

end P3Period64NativeReconstructionSourceOnly

namespace P3ActualLiteralPacketIntegralSourceOnly

def cuspPhase (negative : Bool) (z n : ℕ) : ℂ :=
  P3Period64NativeReconstructionSourceOnly.e ((if negative then (1 : ℝ) else -1)*(n : ℝ)/(z : ℝ))

-- Materialize the unfolding equation here so independent consumers share its owner.
attribute [local simp] cuspPhase

end P3ActualLiteralPacketIntegralSourceOnly
end
