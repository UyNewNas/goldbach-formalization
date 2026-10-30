import ImbalancedChen.ActualSmallRosser
import ImbalancedChen.SmallRoughMainTerm

/-! Finite density definitions, extracted verbatim with original names. -/
namespace ImbalancedChen
noncomputable section
open scoped BigOperators

/-- The reciprocal-totient density of the same literal lower coefficient
whose pointwise polynomial is used in the physical majorant. -/
def actualSmallRosserMinusDensity (N cap : ℕ) (w L : ℝ) : ℝ :=
  reciprocalTotientDensity (actualSmallRosserSupport N cap w)
    (actualSmallRosserMinus N cap w L)

/-- The reciprocal-totient density of the same literal upper coefficient. -/
def actualSmallRosserPlusDensity (N cap : ℕ) (w L : ℝ) : ℝ :=
  reciprocalTotientDensity (actualSmallRosserSupport N cap w)
    (actualSmallRosserPlus N cap w L)

/-- The actual target-prime-deleted Goldbach Euler product. For even
targets the carrier automatically excludes the prime two. -/
def actualSmallEulerProduct (N cap : ℕ) (w : ℝ) : ℝ :=
  ∏ p ∈ actualSmallPrimeFinset N cap w, (1 - 1 / ((p : ℝ) - 1))

end
end ImbalancedChen
