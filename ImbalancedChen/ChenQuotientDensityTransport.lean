import ImbalancedChen.ChenQuotientSieveRemainders
import ImbalancedChen.SieveDimensionComparison

/-!
# Exact local-density transport for genuine selected quotient sources

Only the prime product and the local density agree with the initial sieve.
The support, total mass, and remainders are not identified. The constructor's
rough-multiplier gate is kept in every statement, even where definitional
reduction does not use its proof. No foreign dimension predicate or new
analytic hypothesis is imported. Held, uncompiled source candidate.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Classical

/-- The actual sieving prime product is independent of the multiplier. -/
theorem chenQuotientBoundingSieve_prodPrimes_eq_initial
    (N b : ℕ) (z : ℝ) (hN : Even N)
    (hb : Nat.Coprime b (sieveProduct N (Nat.ceil z))) :
    (chenQuotientBoundingSieve N b z hN hb).prodPrimes =
      (chenInitialBoundingSieve N z hN).prodPrimes := rfl

/-- Equality is at every natural modulus, including one. It does not
assert the separate totient-ratio formula without its positive-b gate. -/
theorem chenQuotientBoundingSieve_nu_eq_initial
    (N b : ℕ) (z : ℝ) (hN : Even N)
    (hb : Nat.Coprime b (sieveProduct N (Nat.ceil z))) (d : ℕ) :
    (chenQuotientBoundingSieve N b z hN hb).nu d =
      (chenInitialBoundingSieve N z hN).nu d := rfl

@[simp] theorem chenQuotientBoundingSieve_nu_one
    (N b : ℕ) (z : ℝ) (hN : Even N)
    (hb : Nat.Coprime b (sieveProduct N (Nat.ceil z))) :
    (chenQuotientBoundingSieve N b z hN hb).nu 1 = 1 := by
  change 1 / (Nat.totient 1 : ℝ) = 1
  norm_num

/-- Prime-factor support is exactly the real strict-cutoff sieve carrier. -/
theorem chenQuotientBoundingSieve_primeFactors
    (N b : ℕ) (z : ℝ) (hN : Even N)
    (hb : Nat.Coprime b (sieveProduct N (Nat.ceil z))) :
    (chenQuotientBoundingSieve N b z hN hb).prodPrimes.primeFactors =
      sievePrimes N (Nat.ceil z) := by
  change (∏ p ∈ sievePrimes N (Nat.ceil z), p).primeFactors = _
  exact Nat.primeFactors_prod fun p hp => (mem_sievePrimes.mp hp).2.1

/-- No prime equal to the real cutoff is introduced by ceiling. -/
theorem chenQuotientBoundingSieve_supported_primes_lt
    (N b : ℕ) (z : ℝ) (hN : Even N)
    (hb : Nat.Coprime b (sieveProduct N (Nat.ceil z))) :
    ∀ p ∈ (chenQuotientBoundingSieve N b z hN hb).prodPrimes.primeFactors,
      (p : ℝ) < z := by
  intro p hp
  rw [chenQuotientBoundingSieve_primeFactors] at hp
  exact (mem_sievePrimes_chen_real_cap.mp hp).1

/-- The full Euler product is the already owned finite density. -/
theorem chenQuotientBoundingSieve_EulerProduct
    (N b : ℕ) (z : ℝ) (hN : Even N)
    (hb : Nat.Coprime b (sieveProduct N (Nat.ceil z))) :
    (∏ p ∈ (chenQuotientBoundingSieve N b z hN hb).prodPrimes.primeFactors,
      (1 - (chenQuotientBoundingSieve N b z hN hb).nu p)) =
        finiteSieveDensity N (Nat.ceil z) := by
  rw [chenQuotientBoundingSieve_primeFactors]
  unfold finiteSieveDensity
  apply Finset.prod_congr rfl
  intro p hp
  change 1 - (chenInitialBoundingSieve N z hN).nu p = _
  rw [chenInitialBoundingSieve_prime_density N z hN (mem_sievePrimes.mp hp).2.1]

/-- Every local dimension product is identical to the initial one.
Hence any initial local-product inequality transports by this equality;
this theorem itself asserts no Mertens or dimension constant. -/
theorem chenQuotientBoundingSieve_localProduct_eq_initial
    (N b : ℕ) (z w v : ℝ) (hN : Even N)
    (hb : Nat.Coprime b (sieveProduct N (Nat.ceil z))) :
    (∏ p ∈ (chenQuotientBoundingSieve N b z hN hb).prodPrimes.primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < v),
      (1 - (chenQuotientBoundingSieve N b z hN hb).nu p)⁻¹) =
    (∏ p ∈ (chenInitialBoundingSieve N z hN).prodPrimes.primeFactors.filter
        (fun p : ℕ => w ≤ (p : ℝ) ∧ (p : ℝ) < v),
      (1 - (chenInitialBoundingSieve N z hN).nu p)⁻¹) := rfl

/-- A smaller real row cutoff retains the gate for a centre-coprime
multiplier already allowed at A. Actual selected multipliers satisfy both
gates by their existing sieve_data theorem. -/
theorem chenQuotient_multiplier_gate_of_cutoff_le {N b : ℕ} {A z : ℝ}
    (hbN : Nat.Coprime b N)
    (hb : Nat.Coprime b (sieveProduct N (Nat.ceil A))) (hzA : z ≤ A) :
    Nat.Coprime b (sieveProduct N (Nat.ceil z)) := by
  have hrough := (chenPrimeRough_iff_coprime_sieveProduct A hbN).mpr hb
  apply chen_rough_multiplier_coprime_sieveProduct
  intro p hp hpb
  exact hzA.trans (hrough p hp hpb)

end

end ImbalancedChen
