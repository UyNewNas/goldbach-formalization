import ImbalancedChen.FiniteSieveModel
import ImbalancedChen.SingularSeries
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact finite Euler factors of the actual sieve

The density product is literally over `sievePrimes N z`, with its strict
natural cap and its exclusion of prime divisors of `N`. For even `N` and
`2 < z`, its factorization has an explicit leading `2`, compensating for
the prime-two factor in the product over all primes below the cap.

The other two products are the finite versions of the factors used in
`singularSeries`. All subtraction inside their factors is real subtraction.
The finite identity also holds at `N = 0`; its correction is indexed by
divisibility below the cap, rather than by the empty `0.primeFactors`.
Only the separate comparison with `oddPrimeDivisors` requires `N ≠ 0`.

The last theorem specializes mathlib's actual `BoundingSieve.selbergTerms`
on allowed divisors. Their squarefreeness is proved from the sieve product
before multiplicativity is used. No Mertens estimate, infinite-product
approximation, optimized sieve bound, or distribution estimate is claimed.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- All primes strictly below the natural cap. -/
def primesBelowCap (z : ℕ) : Finset ℕ :=
  (Finset.range z).filter (fun p : ℕ => Nat.Prime p)

/-- Odd primes strictly below the natural cap. -/
def oddPrimesBelowCap (z : ℕ) : Finset ℕ :=
  (Finset.range z).filter (fun p : ℕ => Nat.Prime p ∧ 2 < p)

/-- The finite correction includes every odd prime divisor below the cap,
also when `N = 0`. -/
def oddPrimeDivisorsBelowCap (N z : ℕ) : Finset ℕ :=
  (oddPrimesBelowCap z).filter (fun p : ℕ => p ∣ N)

@[simp] theorem mem_primesBelowCap {z p : ℕ} :
    p ∈ primesBelowCap z ↔ p < z ∧ Nat.Prime p := by
  simp only [primesBelowCap, Finset.mem_filter, Finset.mem_range]

@[simp] theorem mem_oddPrimesBelowCap {z p : ℕ} :
    p ∈ oddPrimesBelowCap z ↔ p < z ∧ Nat.Prime p ∧ 2 < p := by
  simp only [oddPrimesBelowCap, Finset.mem_filter, Finset.mem_range]

@[simp] theorem mem_oddPrimeDivisorsBelowCap {N z p : ℕ} :
    p ∈ oddPrimeDivisorsBelowCap N z ↔
      p < z ∧ Nat.Prime p ∧ 2 < p ∧ p ∣ N := by
  simp only [oddPrimeDivisorsBelowCap, Finset.mem_filter,
    mem_oddPrimesBelowCap, and_assoc]

/-- The literal `V_N(z)` of the actual sieve, with real subtraction. -/
def finiteSieveDensity (N z : ℕ) : ℝ :=
  ∏ p ∈ sievePrimes N z, (1 - 1 / ((p : ℝ) - 1))

/-- At zero every prime is excluded from the actual sieve. -/
@[simp] theorem finiteSieveDensity_zero (z : ℕ) :
    finiteSieveDensity 0 z = 1 := by
  simp [finiteSieveDensity, sievePrimes]

/-- At a prime, the actual reciprocal-totient density has this real form. -/
theorem halfProductDensity_prime {p : ℕ} (hp : Nat.Prime p) :
    halfProductDensity p = 1 / ((p : ℝ) - 1) := by
  have hp1 : 1 ≤ p := le_trans (by decide : 1 ≤ 2) hp.two_le
  rw [halfProductDensity_apply, Nat.totient_prime hp,
    Nat.cast_sub hp1, Nat.cast_one]

/-- The literal Euler product is the one from the already constructed
mathlib sieve, not a separately postulated density. -/
theorem finiteSieveDensity_eq_boundingSieve_product
    (num den N : ℕ) (T : ℝ) (z : ℕ) (hN : Even N) :
    finiteSieveDensity N z =
      ∏ p ∈ sievePrimes N z,
        (1 - (halfProductBoundingSieve num den N T z hN).nu p) := by
  apply Finset.prod_congr rfl
  intro p hp
  change 1 - 1 / ((p : ℝ) - 1) = 1 - halfProductDensity p
  rw [halfProductDensity_prime (mem_sievePrimes.mp hp).2.1]

/-- Evenness excludes two from the literal allowed-prime set. -/
theorem sievePrimes_eq_oddPrimesBelowCap_filter
    {N z : ℕ} (hN : Even N) :
    sievePrimes N z = (oddPrimesBelowCap z).filter (fun p : ℕ => ¬p ∣ N) := by
  ext p
  simp only [mem_sievePrimes, Finset.mem_filter, mem_oddPrimesBelowCap]
  constructor
  · rintro ⟨hpz, hp, hpN⟩
    have hpne : p ≠ 2 := by
      intro heq
      apply hpN
      simpa only [heq] using hN.two_dvd
    have hp2 : 2 < p := by have := hp.two_le; omega
    exact ⟨⟨hpz, hp, hp2⟩, hpN⟩
  · rintro ⟨⟨hpz, hp, _⟩, hpN⟩
    exact ⟨hpz, hp, hpN⟩

/-- The prime-two factor is separated explicitly; the cap is strict. -/
theorem primesBelowCap_eq_insert_two {z : ℕ} (hz : 2 < z) :
    primesBelowCap z = insert 2 (oddPrimesBelowCap z) := by
  ext p
  simp only [mem_primesBelowCap, Finset.mem_insert, mem_oddPrimesBelowCap]
  constructor
  · rintro ⟨hpz, hp⟩
    by_cases hp2 : p = 2
    · exact Or.inl hp2
    · exact Or.inr ⟨hpz, hp, by have := hp.two_le; omega⟩
  · rintro (rfl | ⟨hpz, hp, _⟩)
    · exact ⟨hz, Nat.prime_two⟩
    · exact ⟨hpz, hp⟩

/-- The leading two exactly cancels `1 - 1/2`. -/
theorem twice_prime_euler_product {z : ℕ} (hz : 2 < z) :
    2 * (∏ p ∈ primesBelowCap z, (1 - 1 / (p : ℝ))) =
      ∏ p ∈ oddPrimesBelowCap z, (1 - 1 / (p : ℝ)) := by
  rw [primesBelowCap_eq_insert_two hz,
    Finset.prod_insert (by simp : 2 ∉ oddPrimesBelowCap z)]
  norm_num <;> ring

/-- The elementary local identity behind the odd-prime Euler factors. -/
theorem odd_prime_euler_factor {p : ℕ} (hp : 2 < p) :
    (1 - 1 / (p : ℝ)) * (1 - 1 / ((p : ℝ) - 1) ^ 2) =
      1 - 1 / ((p : ℝ) - 1) := by
  have hpr : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hp0, hp1] <;> ring

/-- For an excluded odd prime, the manuscript's correction cancels the
local sieve factor exactly. -/
theorem odd_prime_euler_factor_correction {p : ℕ} (hp : 2 < p) :
    (1 - 1 / (p : ℝ)) * (1 - 1 / ((p : ℝ) - 1) ^ 2) *
      (((p : ℝ) - 1) / ((p : ℝ) - 2)) = 1 := by
  rw [odd_prime_euler_factor hp]
  have hpr : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
  field_simp [hp1, hp2] <;> ring

/-- The exact finite identity with every range and the factor two explicit.
It holds for all even `N`, including zero. There is no asymptotic premise. -/
theorem finiteSieveDensity_euler_identity
    {N z : ℕ} (hN : Even N) (hz : 2 < z) :
    finiteSieveDensity N z =
      2 * (∏ p ∈ primesBelowCap z, (1 - 1 / (p : ℝ))) *
        (∏ p ∈ oddPrimesBelowCap z, (1 - 1 / ((p : ℝ) - 1) ^ 2)) *
        (∏ p ∈ oddPrimeDivisorsBelowCap N z,
          ((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
  classical
  have hodd : finiteSieveDensity N z =
      (∏ p ∈ oddPrimesBelowCap z, (1 - 1 / (p : ℝ))) *
        (∏ p ∈ oddPrimesBelowCap z, (1 - 1 / ((p : ℝ) - 1) ^ 2)) *
        (∏ p ∈ oddPrimeDivisorsBelowCap N z,
          ((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
    calc
      finiteSieveDensity N z = ∏ p ∈ oddPrimesBelowCap z,
          (1 - 1 / (p : ℝ)) * (1 - 1 / ((p : ℝ) - 1) ^ 2) *
            (if p ∣ N then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1) := by
        rw [finiteSieveDensity, sievePrimes_eq_oddPrimesBelowCap_filter hN,
          Finset.prod_filter]
        apply Finset.prod_congr rfl
        intro p hp
        have hp2 : 2 < p := (mem_oddPrimesBelowCap.mp hp).2.2
        by_cases hpN : p ∣ N
        · simp only [hpN, not_true_eq_false, if_false, if_true]
          exact (odd_prime_euler_factor_correction hp2).symm
        · simp only [hpN, not_false_eq_true, if_true, if_false, mul_one]
          exact (odd_prime_euler_factor hp2).symm
      _ = (∏ p ∈ oddPrimesBelowCap z, (1 - 1 / (p : ℝ))) *
          (∏ p ∈ oddPrimesBelowCap z, (1 - 1 / ((p : ℝ) - 1) ^ 2)) *
          (∏ p ∈ oddPrimeDivisorsBelowCap N z,
            ((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        congr 1
        exact (Finset.prod_filter (s := oddPrimesBelowCap z)
          (fun p : ℕ => p ∣ N) (fun p : ℕ =>
            ((p : ℝ) - 1) / ((p : ℝ) - 2))).symm
  rw [← twice_prime_euler_product hz] at hodd
  exact hodd

/-- The finite correction is precisely the strict-cap part of the existing
manuscript correction, when the natural prime-divisor set represents `N`. -/
theorem oddPrimeDivisorsBelowCap_eq_filter
    {N z : ℕ} (hN : N ≠ 0) :
    oddPrimeDivisorsBelowCap N z =
      (oddPrimeDivisors N).filter (fun p : ℕ => p < z) := by
  ext p
  simp only [mem_oddPrimeDivisorsBelowCap, Finset.mem_filter,
    mem_oddPrimeDivisors hN]
  constructor
  · rintro ⟨hpz, hp, hp2, hpN⟩
    exact ⟨⟨hp, hp2, hpN⟩, hpz⟩
  · rintro ⟨⟨hp, hp2, hpN⟩, hpz⟩
    exact ⟨hpz, hp, hp2, hpN⟩

/-- The truncated constant uses exactly the factor in the manuscript's
genuine infinite product. This is only a local factor identity. -/
theorem finite_odd_factor_eq_oddPrimeFactor
    {p : ℕ} (hp : Nat.Prime p) (hp2 : 2 < p) :
    (1 - 1 / ((p : ℝ) - 1) ^ 2) = oddPrimeFactor ⟨p, hp, hp2⟩ := rfl

/-- Specialization of mathlib's genuine Selberg terms on allowed divisors.
Squarefreeness is derived explicitly from `d ∣ sieveProduct N z`, and is
used in the prime-factor expansion of the reciprocal-totient density. -/
theorem halfProductBoundingSieve_selbergTerms
    (num den N : ℕ) (T : ℝ) (z d : ℕ) (hN : Even N)
    (hd : d ∣ sieveProduct N z) :
    (halfProductBoundingSieve num den N T z hN).selbergTerms d =
      ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 2) := by
  have hdsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd (sieveProduct_squarefree N z)
  rw [BoundingSieve.selbergTerms_apply]
  change halfProductDensity d *
    (∏ p ∈ d.primeFactors, (1 - halfProductDensity p)⁻¹) = _
  rw [← halfProductDensity_isMultiplicative.prod_primeFactors hdsq,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ sieveProduct N z := (Nat.dvd_of_mem_primeFactors hp).trans hd
  have hp2 : 2 < p := two_lt_prime_of_dvd_sieveProduct hN hpprime hpd
  have hpr : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp2
  have hp1r : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp2r : (p : ℝ) - 2 ≠ 0 := by linarith
  simp only [halfProductDensity_prime hpprime]
  have hfactor : 1 - 1 / ((p : ℝ) - 1) =
      ((p : ℝ) - 2) / ((p : ℝ) - 1) := by
    field_simp [hp1r] <;> ring
  rw [hfactor]
  field_simp [hp1r, hp2r] <;> ring

end

end ImbalancedChen
