import ImbalancedChen.FiniteSieveEuler
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact finite comparison for the sieve dimension condition

For even `N`, the literal sieve density is strictly positive. Its quotient
between natural caps `w ≤ v` is exactly the product of `(p - 1)/(p - 2)`
over allowed primes in the half-open interval `w ≤ p < v`. Removing primes
which divide the center can only decrease this quotient. In particular,
the quotient is bounded by the corresponding product over all odd primes.

The comparison is uniform in the even center, including `N = 0`, and in
fact needs no lower bound on `w`. Thus it includes `2 ≤ w ≤ v`. All prime
cutoffs and subtraction conventions are the literal ones in
`FiniteSieveEuler`: the upper endpoint is strict and subtraction in Euler
factors is real subtraction.

This file proves only exact finite identities and inequalities. It does
not assert a Mertens estimate, a logarithmic dimension bound, or any
analytic sieve/distribution estimate.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- All odd primes in the half-open natural interval `[w, v)`. -/
def oddPrimesInInterval (w v : ℕ) : Finset ℕ :=
  (oddPrimesBelowCap v).filter (fun p : ℕ => w ≤ p)

/-- The actual allowed sieve primes in the same half-open interval. -/
def sievePrimesInInterval (N w v : ℕ) : Finset ℕ :=
  (sievePrimes N v).filter (fun p : ℕ => w ≤ p)

/-- The baseline density uses every odd prime below the strict cap. -/
def oddPrimeSieveDensity (z : ℕ) : ℝ :=
  ∏ p ∈ oddPrimesBelowCap z, (1 - 1 / ((p : ℝ) - 1))

@[simp] theorem mem_oddPrimesInInterval {w v p : ℕ} :
    p ∈ oddPrimesInInterval w v ↔
      w ≤ p ∧ p < v ∧ Nat.Prime p ∧ 2 < p := by
  simp only [oddPrimesInInterval, Finset.mem_filter, mem_oddPrimesBelowCap]
  constructor
  · rintro ⟨⟨hpv, hp, hp2⟩, hwp⟩
    exact ⟨hwp, hpv, hp, hp2⟩
  · rintro ⟨hwp, hpv, hp, hp2⟩
    exact ⟨⟨hpv, hp, hp2⟩, hwp⟩

@[simp] theorem mem_sievePrimesInInterval {N w v p : ℕ} :
    p ∈ sievePrimesInInterval N w v ↔
      w ≤ p ∧ p < v ∧ Nat.Prime p ∧ ¬p ∣ N := by
  simp only [sievePrimesInInterval, Finset.mem_filter, mem_sievePrimes]
  constructor
  · rintro ⟨⟨hpv, hp, hpN⟩, hwp⟩
    exact ⟨hwp, hpv, hp, hpN⟩
  · rintro ⟨hwp, hpv, hp, hpN⟩
    exact ⟨⟨hpv, hp, hpN⟩, hwp⟩

/-- Evenness removes the prime two from every actual sieve cap. -/
theorem two_lt_of_mem_sievePrimes {N z p : ℕ}
    (hN : Even N) (hp : p ∈ sievePrimes N z) : 2 < p := by
  rw [sievePrimes_eq_oddPrimesBelowCap_filter hN] at hp
  exact (mem_oddPrimesBelowCap.mp (Finset.mem_filter.mp hp).1).2.2

/-- Every odd-prime density factor is strictly positive. -/
theorem odd_sieve_factor_pos {p : ℕ} (hp : 2 < p) :
    (0 : ℝ) < 1 - 1 / ((p : ℝ) - 1) := by
  have hpr : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hden : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hlt : 1 / ((p : ℝ) - 1) < (1 : ℝ) :=
    (div_lt_one hden).mpr (by linarith)
  linarith

/-- The reciprocal factor is at least one. -/
theorem one_le_odd_sieve_ratio_factor {p : ℕ} (hp : 2 < p) :
    (1 : ℝ) ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  have hpr : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  apply (le_div_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 2)).mpr
  linarith

/-- Density and quotient factors cancel exactly at every odd prime. -/
theorem odd_sieve_factor_mul_ratio {p : ℕ} (hp : 2 < p) :
    (1 - 1 / ((p : ℝ) - 1)) *
      (((p : ℝ) - 1) / ((p : ℝ) - 2)) = 1 := by
  have hpr : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
  field_simp [hp1, hp2] <;> ring

/-- Adding factors which are at least one can only increase a product.
This finite comparison is independent of primality or any asymptotic. -/
theorem finite_prod_le_prod_of_subset_of_one_le
    {α : Type*} {s t : Finset α} {f : α → ℝ}
    (hst : s ⊆ t) (hf : ∀ a ∈ t, 1 ≤ f a) :
    (∏ a ∈ s, f a) ≤ ∏ a ∈ t, f a := by
  classical
  have hfilter : t.filter (fun a => a ∈ s) = s := by
    ext a
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨hst h, h⟩
  rw [← hfilter, Finset.prod_filter]
  apply Finset.prod_le_prod
  · intro a ha
    by_cases hs : a ∈ s
    · simpa only [hs, if_true] using (zero_le_one.trans (hf a ha))
    · simpa only [hs, if_false] using (zero_le_one : (0 : ℝ) ≤ 1)
  · intro a ha
    by_cases hs : a ∈ s
    · simpa only [hs, if_true] using (le_rfl : f a ≤ f a)
    · simpa only [hs, if_false] using (hf a ha)

/-- A finite multiplicative split gives an exact quotient whenever the
complementary factors have specified reciprocals. -/
theorem finite_prod_ratio_of_split
    {α : Type*} (s t u : Finset α) (f g : α → ℝ)
    (ht : 0 < ∏ a ∈ t, f a)
    (hsplit : (∏ a ∈ t, f a) = (∏ a ∈ s, f a) * ∏ a ∈ u, f a)
    (hfg : ∀ a ∈ u, f a * g a = 1) :
    (∏ a ∈ s, f a) / (∏ a ∈ t, f a) = ∏ a ∈ u, g a := by
  have hcancel : (∏ a ∈ u, f a) * (∏ a ∈ u, g a) = 1 := by
    rw [← Finset.prod_mul_distrib]
    calc
      (∏ a ∈ u, f a * g a) = ∏ _a ∈ u, (1 : ℝ) := by
        apply Finset.prod_congr rfl
        exact hfg
      _ = 1 := by simp
  apply (div_eq_iff ht.ne').mpr
  rw [hsplit]
  calc
    (∏ a ∈ s, f a) = (∏ a ∈ s, f a) * 1 := by ring
    _ = (∏ a ∈ s, f a) * ((∏ a ∈ u, f a) * (∏ a ∈ u, g a)) := by
      rw [hcancel]
    _ = (∏ a ∈ u, g a) * ((∏ a ∈ s, f a) * (∏ a ∈ u, f a)) := by ring

/-- In particular, the literal density is never zero for an even center. -/
theorem finiteSieveDensity_pos {N : ℕ} (hN : Even N) (z : ℕ) :
    0 < finiteSieveDensity N z := by
  apply Finset.prod_pos
  intro p hp
  exact odd_sieve_factor_pos (two_lt_of_mem_sievePrimes hN hp)

/-- The all-odd-prime baseline density is strictly positive at every cap. -/
theorem oddPrimeSieveDensity_pos (z : ℕ) : 0 < oddPrimeSieveDensity z := by
  apply Finset.prod_pos
  intro p hp
  exact odd_sieve_factor_pos (mem_oddPrimesBelowCap.mp hp).2.2

/-- Exact splitting at the lower cap. Primes equal to `w` occur in the
interval product, while primes equal to `v` occur in neither product. -/
theorem finiteSieveDensity_split {N w v : ℕ} (hwv : w ≤ v) :
    finiteSieveDensity N v = finiteSieveDensity N w *
      ∏ p ∈ sievePrimesInInterval N w v, (1 - 1 / ((p : ℝ) - 1)) := by
  have hbelow : (sievePrimes N v).filter (fun p : ℕ => p < w) =
      sievePrimes N w := by
    ext p
    simp only [Finset.mem_filter, mem_sievePrimes]
    constructor
    · rintro ⟨⟨_, hp, hpN⟩, hpw⟩
      exact ⟨hpw, hp, hpN⟩
    · rintro ⟨hpw, hp, hpN⟩
      exact ⟨⟨lt_of_lt_of_le hpw hwv, hp, hpN⟩, hpw⟩
  simpa only [finiteSieveDensity, sievePrimesInInterval, hbelow, not_lt] using
    (Finset.prod_filter_mul_prod_filter_not (sievePrimes N v)
      (fun p : ℕ => p < w)
      (fun p : ℕ => (1 : ℝ) - 1 / ((p : ℝ) - 1))).symm

/-- The same exact splitting for the baseline product. -/
theorem oddPrimeSieveDensity_split {w v : ℕ} (hwv : w ≤ v) :
    oddPrimeSieveDensity v = oddPrimeSieveDensity w *
      ∏ p ∈ oddPrimesInInterval w v, (1 - 1 / ((p : ℝ) - 1)) := by
  have hbelow : (oddPrimesBelowCap v).filter (fun p : ℕ => p < w) =
      oddPrimesBelowCap w := by
    ext p
    simp only [Finset.mem_filter, mem_oddPrimesBelowCap]
    constructor
    · rintro ⟨⟨_, hp, hp2⟩, hpw⟩
      exact ⟨hpw, hp, hp2⟩
    · rintro ⟨hpw, hp, hp2⟩
      exact ⟨⟨lt_of_lt_of_le hpw hwv, hp, hp2⟩, hpw⟩
  simpa only [oddPrimeSieveDensity, oddPrimesInInterval, hbelow, not_lt] using
    (Finset.prod_filter_mul_prod_filter_not (oddPrimesBelowCap v)
      (fun p : ℕ => p < w)
      (fun p : ℕ => (1 : ℝ) - 1 / ((p : ℝ) - 1))).symm

/-- The exact quotient of the actual density, including the center-prime
exclusions and both interval endpoints. -/
theorem finiteSieveDensity_ratio_eq_interval_product
    {N w v : ℕ} (hN : Even N) (hwv : w ≤ v) :
    finiteSieveDensity N w / finiteSieveDensity N v =
      ∏ p ∈ sievePrimesInInterval N w v,
        ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  apply finite_prod_ratio_of_split
    (sievePrimes N w) (sievePrimes N v) (sievePrimesInInterval N w v)
    (fun p : ℕ => (1 : ℝ) - 1 / ((p : ℝ) - 1))
    (fun p : ℕ => ((p : ℝ) - 1) / ((p : ℝ) - 2))
    (finiteSieveDensity_pos hN v) (finiteSieveDensity_split hwv)
  intro p hp
  exact odd_sieve_factor_mul_ratio
    (two_lt_of_mem_sievePrimes hN (Finset.mem_filter.mp hp).1)

/-- The exact all-odd-prime quotient with the same endpoints. -/
theorem oddPrimeSieveDensity_ratio_eq_interval_product
    {w v : ℕ} (hwv : w ≤ v) :
    oddPrimeSieveDensity w / oddPrimeSieveDensity v =
      ∏ p ∈ oddPrimesInInterval w v,
        ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  apply finite_prod_ratio_of_split
    (oddPrimesBelowCap w) (oddPrimesBelowCap v) (oddPrimesInInterval w v)
    (fun p : ℕ => (1 : ℝ) - 1 / ((p : ℝ) - 1))
    (fun p : ℕ => ((p : ℝ) - 1) / ((p : ℝ) - 2))
    (oddPrimeSieveDensity_pos v) (oddPrimeSieveDensity_split hwv)
  intro p hp
  exact odd_sieve_factor_mul_ratio (mem_oddPrimesInInterval.mp hp).2.2.2

/-- For an even center the actual interval is exactly the all-odd-prime
interval with the divisors of the center removed. -/
theorem sievePrimesInInterval_eq_filter {N w v : ℕ} (hN : Even N) :
    sievePrimesInInterval N w v =
      (oddPrimesInInterval w v).filter (fun p : ℕ => ¬p ∣ N) := by
  ext p
  simp only [Finset.mem_filter, mem_sievePrimesInInterval, mem_oddPrimesInInterval]
  constructor
  · rintro ⟨hwp, hpv, hp, hpN⟩
    have hp2 : 2 < p := two_lt_of_mem_sievePrimes hN
      (mem_sievePrimes.mpr ⟨hpv, hp, hpN⟩)
    exact ⟨⟨hwp, hpv, hp, hp2⟩, hpN⟩
  · rintro ⟨⟨hwp, hpv, hp, _⟩, hpN⟩
    exact ⟨hwp, hpv, hp, hpN⟩

/-- Removing center-prime factors decreases the interval quotient. This
is the finite, uniform comparison used before any analytic dimension
estimate is supplied. It also applies when `2 ≤ w ≤ v`. -/
theorem finiteSieveDensity_ratio_le_all_odd_primes
    {N w v : ℕ} (hN : Even N) (hwv : w ≤ v) :
    finiteSieveDensity N w / finiteSieveDensity N v ≤
      ∏ p ∈ oddPrimesInInterval w v,
        ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  rw [finiteSieveDensity_ratio_eq_interval_product hN hwv]
  apply finite_prod_le_prod_of_subset_of_one_le
  · rw [sievePrimesInInterval_eq_filter hN]
    exact Finset.filter_subset _ _
  · intro p hp
    exact one_le_odd_sieve_ratio_factor (mem_oddPrimesInInterval.mp hp).2.2.2

/-- Equivalent comparison with the ratio of the literal baseline density. -/
theorem finiteSieveDensity_ratio_le_baseline
    {N w v : ℕ} (hN : Even N) (hwv : w ≤ v) :
    finiteSieveDensity N w / finiteSieveDensity N v ≤
      oddPrimeSieveDensity w / oddPrimeSieveDensity v := by
  rw [oddPrimeSieveDensity_ratio_eq_interval_product hwv]
  exact finiteSieveDensity_ratio_le_all_odd_primes hN hwv

/-- The density quotient is at least one, including empty intervals. -/
theorem one_le_finiteSieveDensity_ratio
    {N w v : ℕ} (hN : Even N) (hwv : w ≤ v) :
    1 ≤ finiteSieveDensity N w / finiteSieveDensity N v := by
  rw [finiteSieveDensity_ratio_eq_interval_product hN hwv]
  apply Finset.one_le_prod
  intro p hp
  exact one_le_odd_sieve_ratio_factor
    (two_lt_of_mem_sievePrimes hN (Finset.mem_filter.mp hp).1)

/-- The literal density decreases as its strict cap increases. -/
theorem finiteSieveDensity_antitone {N : ℕ} (hN : Even N) :
    Antitone (finiteSieveDensity N) := by
  intro w v hwv
  have h := (le_div_iff₀ (finiteSieveDensity_pos hN v)).mp
    (one_le_finiteSieveDensity_ratio hN hwv)
  simpa only [one_mul] using h

/-- Enlarging the set of excluded center-primes also decreases the
quotient: every multiple of an even center has no larger ratio. -/
theorem finiteSieveDensity_ratio_antitone_center_dvd
    {M N w v : ℕ} (hM : Even M) (hN : Even N)
    (hMN : M ∣ N) (hwv : w ≤ v) :
    finiteSieveDensity N w / finiteSieveDensity N v ≤
      finiteSieveDensity M w / finiteSieveDensity M v := by
  rw [finiteSieveDensity_ratio_eq_interval_product hN hwv,
    finiteSieveDensity_ratio_eq_interval_product hM hwv]
  apply finite_prod_le_prod_of_subset_of_one_le
  · intro p hp
    obtain ⟨hwp, hpv, hpprime, hpN⟩ := mem_sievePrimesInInterval.mp hp
    apply mem_sievePrimesInInterval.mpr
    exact ⟨hwp, hpv, hpprime, fun hpM => hpN (hpM.trans hMN)⟩
  · intro p hp
    exact one_le_odd_sieve_ratio_factor
      (two_lt_of_mem_sievePrimes hM (Finset.mem_filter.mp hp).1)

end

end ImbalancedChen
