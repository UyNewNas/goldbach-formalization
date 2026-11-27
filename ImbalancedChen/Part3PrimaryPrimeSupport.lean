import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Associated

/-! # Prime support and its coprime complement -/

namespace ImbalancedChen.Part3.CanonicalReciprocalData

noncomputable section
open scoped BigOperators

/-- The factor of `n` containing the full powers of primes dividing `d`. -/
def supportedPart (n d : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p ∣ d), p ^ n.factorization p

/-- The complementary factor of `n`, containing primes not dividing `d`. -/
def coprimePart (n d : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => ¬p ∣ d), p ^ n.factorization p

theorem supportedPart_pos (n d : ℕ) : 0 < supportedPart n d := by
  apply Nat.pos_of_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero

theorem supportedPart_mul_coprimePart {n : ℕ} (hn : 0 < n) (d : ℕ) :
    supportedPart n d * coprimePart n d = n := by
  rw [supportedPart, coprimePart, Finset.prod_filter_mul_prod_filter_not]
  exact (Nat.prod_primeFactors_pow_factorization (Nat.ne_of_gt hn)).symm

theorem supportedPart_dvd {n : ℕ} (hn : 0 < n) (d : ℕ) :
    supportedPart n d ∣ n :=
  ⟨coprimePart n d, (supportedPart_mul_coprimePart hn d).symm⟩

/-- Every prime divisor of the supported part divides the reference integer. -/
theorem prime_dvd_supportedPart {n d p : ℕ} (hp : p.Prime)
    (hps : p ∣ supportedPart n d) : p ∣ d := by
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hps
  obtain ⟨hqn, hqd⟩ := Finset.mem_filter.mp hq
  have heq : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hqn)).mp
      (hp.dvd_of_dvd_pow hpq)
  exact heq ▸ hqd

/-- Every prime divisor of the complementary part avoids the reference integer. -/
theorem prime_dvd_coprimePart_not_dvd {n d p : ℕ} (hp : p.Prime)
    (hpt : p ∣ coprimePart n d) : ¬p ∣ d := by
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hpt
  obtain ⟨hqn, hqd⟩ := Finset.mem_filter.mp hq
  have heq : p = q :=
    (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hqn)).mp
      (hp.dvd_of_dvd_pow hpq)
  exact heq ▸ hqd

theorem coprimePart_coprime (n d : ℕ) : (coprimePart n d).Coprime d := by
  by_contra h
  obtain ⟨p, hp, hpt, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact prime_dvd_coprimePart_not_dvd hp hpt hpd

/-- Coprimality transfers from `d` to every integer supported on primes dividing `d`. -/
theorem coprime_of_prime_support {u d s : ℕ} (hu : u.Coprime d)
    (hs : ∀ p : ℕ, p.Prime → p ∣ s → p ∣ d) : u.Coprime s := by
  by_contra h
  obtain ⟨p, hp, hpu, hps⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpu, hs p hp hps⟩) hu

end
end ImbalancedChen.Part3.CanonicalReciprocalData
