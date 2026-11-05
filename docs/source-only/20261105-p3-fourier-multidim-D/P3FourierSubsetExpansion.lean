import ImbalancedChen.P3FourierOneDimDecay
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
P3.6 / MANUSCRIPT INTERNAL / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Finite-dimensional, completely explicit subset expansion for the Fourier D
ledger of equation (F). This is NOT a higher-dimensional integration-by-parts
claim. The unsigned subset monomials and their (2*pi)-scaled versions agree
with the true ordered doubled-coordinate derivatives only after the missing
coordinatewise Fourier differentiation identity has been established.
-/

namespace ImbalancedChen.P3FourierSubsetExpansion
noncomputable section
open scoped BigOperators

/-- The product on the RHS of manuscript (F), in PHYSICAL xi frequency. -/
def physicalDenom {d : ℕ} (xi : Fin d → ℝ) : ℝ :=
  ∏ i : Fin d, (1 + xi i ^ 2)

/-- Each finite subset S contributes exactly one monomial, corresponding
 to applying two derivatives in every coordinate of S. -/
def physicalMonomial {d : ℕ} (S : Finset (Fin d)) (xi : Fin d → ℝ) : ℝ :=
  ∏ i ∈ S, xi i ^ 2

theorem physicalDenom_eq_subset_sum {d : ℕ} (xi : Fin d → ℝ) :
    physicalDenom xi = ∑ S : Finset (Fin d), physicalMonomial S xi := by
  classical
  simpa [physicalDenom, physicalMonomial] using
    (Finset.prod_one_add (s := (Finset.univ : Finset (Fin d)))
      (f := fun i : Fin d => xi i ^ 2))

theorem physicalDenom_pos {d : ℕ} (xi : Fin d → ℝ) :
    0 < physicalDenom xi := by
  classical
  unfold physicalDenom
  exact Finset.prod_pos (fun i hi => by positivity)

/-- The same product in C, used when Fourier differentiation produces
 (-xi_i^2) multipliers. -/
def complexDenom {d : ℕ} (xi : Fin d → ℝ) : ℂ :=
  ∏ i : Fin d, (1 + ((xi i ^ 2 : ℝ) : ℂ))

def complexMonomial {d : ℕ} (S : Finset (Fin d)) (xi : Fin d → ℝ) : ℂ :=
  ∏ i ∈ S, ((xi i ^ 2 : ℝ) : ℂ)

theorem complexDenom_eq_subset_sum {d : ℕ} (xi : Fin d → ℝ) :
    complexDenom xi = ∑ S : Finset (Fin d), complexMonomial S xi := by
  classical
  simpa [complexDenom, complexMonomial] using
    (Finset.prod_one_add (s := (Finset.univ : Finset (Fin d)))
      (f := fun i : Fin d => ((xi i ^ 2 : ℝ) : ℂ)))

/-- No mysterious dimension factor: the complex product has norm equal
 to the positive real physical denominator itself. -/
theorem norm_complexDenom {d : ℕ} (xi : Fin d → ℝ) :
    ‖complexDenom xi‖ = physicalDenom xi := by
  classical
  unfold complexDenom physicalDenom
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro i hi
  have hnonneg : 0 ≤ (1 + xi i ^ 2 : ℝ) := by positivity
  have hc : (1 : ℂ) + ((xi i ^ 2 : ℝ) : ℂ) =
      ((1 + xi i ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]

/-- The real scaling does not replace a Fourier change-of-variables
 theorem: it is just the precise physical xi=2*pi*eta convention. -/
def physicalFrequency {d : ℕ} (eta : Fin d → ℝ) : Fin d → ℝ :=
  fun i => 2 * Real.pi * eta i

theorem physicalFrequency_inv {d : ℕ} (xi : Fin d → ℝ) :
    physicalFrequency (fun i => xi i / (2 * Real.pi)) = xi := by
  funext i
  exact P3FourierOneDimDecay.physical_frequency_eq (xi i)

end
end ImbalancedChen.P3FourierSubsetExpansion
