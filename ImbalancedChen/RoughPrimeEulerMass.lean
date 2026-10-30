import ImbalancedChen.RoughPrimeUniverse
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Real.Basic

/-! Finite Euler mass via Mathlib multiplicativity. Original theorem signature, including N/hcop,
is preserved. The proof uses the pointwise reciprocal totient as an arithmetic
function, not the Dirichlet inverse, and no progression-density supplier. -/
namespace ImbalancedChen
noncomputable section
open scoped BigOperators
open ArithmeticFunction

theorem reciprocalTotient_sum_divisors_primeProduct
    (N : ℕ) (P : Finset ℕ) (hprime : ∀ p ∈ P, Nat.Prime p)
    (hcop : ∀ p ∈ P, Nat.Coprime p N) :
    (∑ d ∈ (P.prod id).divisors, 1 / (Nat.totient d : ℝ)) =
      ∏ p ∈ P, (1 + 1 / ((p : ℝ) - 1)) := by
  classical
  have hsf : Squarefree (P.prod id) := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime
      (fun p hp q hq hpq => ?_) (fun p hp => (hprime p hp).squarefree)
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq)
  let f : ArithmeticFunction ℝ :=
    ⟨fun d => (Nat.totient d : ℝ)⁻¹, by simp⟩
  have hf : f.IsMultiplicative := by
    refine ⟨?_, ?_⟩
    · simp [f]
    · intro m n hmn
      change (Nat.totient (m * n) : ℝ)⁻¹ =
        (Nat.totient m : ℝ)⁻¹ * (Nat.totient n : ℝ)⁻¹
      rw [Nat.totient_mul hmn, Nat.cast_mul, mul_inv_rev]
      exact mul_comm _ _
  have heuler := hf.prodPrimeFactors_one_add_of_squarefree hsf
  have hfac : (P.prod id).primeFactors = P := by
    simpa only [id_eq] using Nat.primeFactors_prod hprime
  calc
    (∑ d ∈ (P.prod id).divisors, 1 / (Nat.totient d : ℝ)) =
        ∑ d ∈ (P.prod id).divisors, f d := by
      simp only [f, ArithmeticFunction.coe_mk, one_div]
    _ = ∏ p ∈ (P.prod id).primeFactors, (1 + f p) := heuler.symm
    _ = ∏ p ∈ P, (1 + 1 / ((p : ℝ) - 1)) := by
      rw [hfac]
      apply Finset.prod_congr rfl
      intro p hp
      change 1 + (Nat.totient p : ℝ)⁻¹ = 1 + 1 / ((p : ℝ) - 1)
      rw [Nat.totient_prime (hprime p hp), Nat.cast_sub (hprime p hp).one_le]
      simp only [Nat.cast_one, one_div]

theorem roughPrimeFinset_odd_of_even {N cap : ℕ} {w z : ℝ}
    (hN : Even N) {p : ℕ} (hp : p ∈ roughPrimeFinset N cap w z) :
    Nat.Prime p ∧ 2 < p := by
  obtain ⟨_, hprime, hnot, _, _⟩ := mem_roughPrimeFinset.mp hp
  have h2N : 2 ∣ N := by
    obtain ⟨k, hk⟩ := hN
    exact ⟨k, by omega⟩
  have hne : p ≠ 2 := by
    intro heq
    subst p
    exact hnot h2N
  exact ⟨hprime, by have := hprime.two_le; omega⟩

/-- The plus Euler factors are bounded by inverse Goldbach factors. -/
theorem roughPrime_eulerProduct_le_inverseProduct
    (N cap : ℕ) (w z : ℝ) (hN : Even N) :
    (∏ p ∈ roughPrimeFinset N cap w z, (1 + 1 / ((p : ℝ) - 1))) ≤
      ∏ p ∈ roughPrimeFinset N cap w z, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
  classical
  apply Finset.prod_le_prod
  · intro p hp
    have hp2 : (2 : ℝ) < p := by
      exact_mod_cast (roughPrimeFinset_odd_of_even hN hp).2
    exact add_nonneg zero_le_one (div_nonneg zero_le_one (by linarith))
  · intro p hp
    have hp2 : (2 : ℝ) < p := by
      exact_mod_cast (roughPrimeFinset_odd_of_even hN hp).2
    have hx : (1 : ℝ) / ((p : ℝ) - 1) < 1 :=
      (div_lt_one (by linarith)).mpr (by linarith)
    rw [← one_div]
    apply (le_div_iff₀ (sub_pos.mpr hx)).mpr
    nlinarith [sq_nonneg (1 / ((p : ℝ) - 1))]

end
end ImbalancedChen
