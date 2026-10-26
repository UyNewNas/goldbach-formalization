import ImbalancedChen.Part3EisensteinAmplitudeMultiplicativity
import ImbalancedChen.Part3EisensteinPrimePowerEulerPolynomial
import Mathlib.Data.Nat.Factorization.Induction

/-! Actual finite composite Euler factorization, including arbitrary prime
exponents, of the entire normalized divisor amplitudes. Native Nat
factorization induction supplies the finite coprime product; actual local
prime-power polynomials supply every factor. No infinite Euler product or
spectral identification is assumed. SOURCE ONLY / UNCOMPILED / ZERO CREDIT. -/

noncomputable section
open Complex Finset
open scoped BigOperators
open ImbalancedChen.Part3ActualRamanujanDirichletSeries
open ImbalancedChen.Part3.NormalizedEisensteinPrimeAmplitude20261026b
open ImbalancedChen.Part3.EisensteinAmplitudeMultiplicativity20261026b
open ImbalancedChen.Part3.EisensteinPrimePowerEulerPolynomial20261026b

namespace ImbalancedChen.Part3.EisensteinCompositeEulerPolynomial20261026b

/-- Native prime-factorization induction applies to the actual amplitude,
using proved coprime multiplicativity and its literal value at one. -/
theorem normalizedAmplitude_factorization (n : ℕ) (hn : n ≠ 0) (s : ℂ) :
    normalizedDivisorAmplitude n s =
      n.factorization.prod (fun p k => normalizedDivisorAmplitude (p ^ k) s) := by
  exact Nat.multiplicative_factorization (fun m => normalizedDivisorAmplitude m s)
    (fun a b hab => normalizedAmplitude_mul_of_coprime hab s)
    (by simp [normalizedDivisorAmplitude, divisorFactor]) hn

/-- Canonical full finite Euler factorization with every actual prime
exponent retained. Each local scalar is the genuine symmetric p-power. -/
theorem normalizedAmplitude_composite_euler (n : ℕ) (hn : n ≠ 0) (s : ℂ) :
    normalizedDivisorAmplitude n s = n.factorization.prod (fun p k =>
      primeHeckePolynomial k ((p : ℂ) ^ (s - 1 / 2) + (p : ℂ) ^ (1 / 2 - s))) := by
  rw [normalizedAmplitude_factorization n hn s]
  apply Finsupp.prod_congr
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors (by
    simpa only [Nat.support_factorization] using hp)
  exact normalizedAmplitude_prime_power hpPrime _ s

/-- The exact original finite prime-divisor set, with native valuations
as exponents. In particular no squarefree reduction has been made. -/
theorem normalizedAmplitude_composite_euler_valuation (n : ℕ) (hn : n ≠ 0) (s : ℂ) :
    normalizedDivisorAmplitude n s = ∏ p ∈ n.primeFactors,
      primeHeckePolynomial (padicValNat p n)
        ((p : ℂ) ^ (s - 1 / 2) + (p : ℂ) ^ (1 / 2 - s)) := by
  rw [normalizedAmplitude_composite_euler n hn s]
  change (∏ p ∈ n.factorization.support, primeHeckePolynomial (n.factorization p)
    ((p : ℂ) ^ (s - 1 / 2) + (p : ℂ) ^ (1 / 2 - s))) = _
  rw [Nat.support_factorization]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp)]

end ImbalancedChen.Part3.EisensteinCompositeEulerPolynomial20261026b
