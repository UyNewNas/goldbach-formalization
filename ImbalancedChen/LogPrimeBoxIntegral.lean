import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Lebesgue integrals on logarithmic prime boxes

The box is the actual product of the half-open intervals `[a i, b i)`
in the finite-dimensional real space. Its reciprocal-coordinate density
is integrated against Lebesgue volume restricted to that set. Restriction
of the product measure and finite-dimensional Fubini reduce this genuine
integral to the one-dimensional logarithm integrals.

Positive lower endpoints suffice for integrability, and weak endpoint
inequalities are allowed in the formula. Thus degenerate coordinate
intervals are included. The zero-dimensional box has volume and mass one.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open MeasureTheory Set

/-- A product of half-open intervals, with the strict upper condition in
every coordinate. This is a product set, not an order interval in a product
partial order. -/
def logPrimeBox {k : ℕ} (a b : Fin k → ℝ) : Set (Fin k → ℝ) :=
  Set.univ.pi (fun i => Set.Ico (a i) (b i))

@[simp] theorem mem_logPrimeBox {k : ℕ} {a b x : Fin k → ℝ} :
    x ∈ logPrimeBox a b ↔ ∀ i, a i ≤ x i ∧ x i < b i := by
  simp [logPrimeBox]

theorem measurableSet_logPrimeBox {k : ℕ} (a b : Fin k → ℝ) :
    MeasurableSet (logPrimeBox a b) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

/-- The one-dimensional density is integrable on every interval with a
positive lower endpoint, also when that interval is empty. -/
theorem integrableOn_one_div_Ico {a : ℝ} (b : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => 1 / x) (Set.Ico a b) := by
  have hcont : ContinuousOn (fun x : ℝ => 1 / x) (Set.Icc a b) :=
    continuousOn_const.div continuousOn_id (fun x hx => (ha.trans_le hx.1).ne')
  exact hcont.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self

/-- The exact logarithm integral uses the Lebesgue set integral on the
half-open interval, including the case of equal endpoints. -/
theorem integral_one_div_Ico {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x : ℝ in Set.Ico a b, 1 / x) = Real.log (b / a) := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact integral_one_div_of_pos ha (ha.trans_le hab)

/-- The product reciprocal-coordinate density is genuinely integrable
on the actual product box, without imposing strict separation of endpoints. -/
theorem integrableOn_logPrimeBox_one_div {k : ℕ} (a b : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) :
    IntegrableOn (fun x : Fin k → ℝ => ∏ i, 1 / x i) (logPrimeBox a b) := by
  unfold IntegrableOn logPrimeBox
  rw [volume_pi, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod (fun i => integrableOn_one_div_Ico (b i) (ha i))

/-- Fubini on the true restricted Lebesgue product measure evaluates the
box integral as the product of the coordinate logarithms. -/
theorem integral_logPrimeBox_one_div {k : ℕ} (a b : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i ≤ b i) :
    (∫ x : Fin k → ℝ in logPrimeBox a b, ∏ i, 1 / x i) =
      ∏ i, Real.log (b i / a i) := by
  unfold logPrimeBox
  rw [volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact integral_one_div_Ico (ha i) (hab i)

/-- An arbitrary constant multiplier preserves integrability. -/
theorem integrableOn_logPrimeBox_const_mul_one_div {k : ℕ} (c : ℝ)
    (a b : Fin k → ℝ) (ha : ∀ i, 0 < a i) :
    IntegrableOn (fun x : Fin k → ℝ => c * ∏ i, 1 / x i) (logPrimeBox a b) :=
  (integrableOn_logPrimeBox_one_div a b ha).const_mul c

/-- Constant-weighted box mass, for finite lower sums and Euler-ratio
endpoint weights. No sign condition on the constant is necessary. -/
theorem integral_logPrimeBox_const_mul_one_div {k : ℕ} (c : ℝ)
    (a b : Fin k → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i ≤ b i) :
    (∫ x : Fin k → ℝ in logPrimeBox a b, c * ∏ i, 1 / x i) =
      c * ∏ i, Real.log (b i / a i) := by
  rw [integral_const_mul, integral_logPrimeBox_one_div a b ha hab]

/-- The terminal upper-endpoint weight used in the logarithmic three-prime
boundary lower sums is a specialization of the actual box integral. -/
theorem integral_logPrimeBox_terminal_upper_weight {k : ℕ}
    (a b : Fin k → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i ≤ b i)
    (j : Fin k) :
    (∫ x : Fin k → ℝ in logPrimeBox a b, (1 / b j) * ∏ i, 1 / x i) =
      (1 / b j) * ∏ i, Real.log (b i / a i) :=
  integral_logPrimeBox_const_mul_one_div (1 / b j) a b ha hab

end

end ImbalancedChen
