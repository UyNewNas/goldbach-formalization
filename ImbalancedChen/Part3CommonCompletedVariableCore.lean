import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Interval.Finset.Nat

/-! The common completed-variable interval and phase used at every level. -/

namespace ImbalancedChen.Part3

noncomputable section

open Classical

/-- The returned variable has ONE interval and ONE phase, shared by all
levels. There is deliberately no level-indexed interval or phase field. -/
structure CommonCompletedVariable where
  intervalLo : ℕ
  intervalHi : ℕ
  additivePhase : ℝ

def CommonCompletedVariable.weight (d : CommonCompletedVariable) (m : ℕ) : ℂ :=
  if m ∈ Finset.Ico d.intervalLo d.intervalHi then
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (d.additivePhase : ℂ) * (m : ℂ))
  else 0

end

end ImbalancedChen.Part3
