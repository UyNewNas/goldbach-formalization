import ImbalancedChen.RoughPrimeUniverse
import Mathlib.NumberTheory.Divisors

/-! Exact finite-carrier definitions, shared with the original rounding module. -/
namespace ImbalancedChen.P2LowerFiniteCellRounding

noncomputable section
open scoped Classical BigOperators

def roughProduct (N cap : ℕ) (w z : ℝ) : ℕ :=
  (roughPrimeUniverse N cap w z).prod

def «universe» (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  (roughProduct N cap w z).divisors

end
end ImbalancedChen.P2LowerFiniteCellRounding
