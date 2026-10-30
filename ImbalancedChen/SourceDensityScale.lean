import ImbalancedChen.SingularSeries
import Mathlib.Tactic.Ring

/-! Exact source/density scale identity, extracted without changing its declaration. -/
namespace ImbalancedChen
noncomputable section

/-- Exact source/density scale conversion, including Lean's total division
conventions at the two small exceptional natural arguments. -/
theorem sourceMassScale_mul_densityScale (N : ℕ) :
    ((N : ℝ) / Real.log (N : ℝ)) *
        (singularSeries N / Real.log (N : ℝ)) = singularNormalization N := by
  simp only [singularNormalization, div_eq_mul_inv]
  ring

end
end ImbalancedChen
