import ImbalancedChen.RationalPowers

/-!
# Ordered prime factors for the bad-receiver count

The complement predicate `BadReceiver` is equivalent to the manuscript's
ordered bad region: the receiver has prime factors `r ≤ q` and
`q ^ num < r ^ den`. The converse checks every possible prime-factor witness
using uniqueness up to swapping the two factors. In particular, the existence
of one rejected witness is not silently treated as rejection of all witnesses.

The integer-power equivalence holds for all natural numerators and
denominators. A positive denominator is needed only when translating to real
powers. No analytic estimates are assumed.
-/

namespace ImbalancedChen

/-- Two factorizations into two primes agree up to swapping their factors.
Repeated factors are allowed. -/
theorem prime_mul_eq_prime_mul_iff {r q s t : ℕ}
    (hr : Nat.Prime r) (hq : Nat.Prime q)
    (hs : Nat.Prime s) (ht : Nat.Prime t) :
    r * q = s * t ↔ (r = s ∧ q = t) ∨ (r = t ∧ q = s) := by
  constructor
  · intro h
    have hdiv : r ∣ s * t := by
      rw [← h]
      exact dvd_mul_right r q
    rcases hr.dvd_mul.mp hdiv with hrs | hrt
    · have heq : r = s := (Nat.prime_dvd_prime_iff_eq hr hs).mp hrs
      subst s
      exact Or.inl ⟨rfl, (mul_right_inj' hr.ne_zero).mp h⟩
    · have heq : r = t := (Nat.prime_dvd_prime_iff_eq hr ht).mp hrt
      subst t
      have h' : r * q = r * s := h.trans (Nat.mul_comm s r)
      exact Or.inr ⟨rfl, (mul_right_inj' hr.ne_zero).mp h'⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Nat.mul_comm _ _

/-- Sorting removes the remaining swap ambiguity, including prime squares. -/
theorem ordered_prime_factors_unique {r q s t : ℕ}
    (hr : Nat.Prime r) (hq : Nat.Prime q)
    (hs : Nat.Prime s) (ht : Nat.Prime t)
    (hrq : r ≤ q) (hst : s ≤ t) (hprod : r * q = s * t) :
    r = s ∧ q = t := by
  rcases (prime_mul_eq_prime_mul_iff hr hq hs ht).mp hprod with
    hsame | ⟨hrt, hqs⟩
  · exact hsame
  · omega

/-- The manuscript's ordered integer-power bad region. -/
def OrderedBadReceiver (num den m : ℕ) : Prop :=
  ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q ∧
    r ≤ q ∧ q ^ num < r ^ den

/-- The complement of the accepted receiver predicate is exactly the ordered
bad region. No exponent restrictions are needed for this finite statement. -/
theorem badReceiver_iff_ordered_factors {num den m : ℕ} :
    BadReceiver num den m ↔
      ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q ∧
        r ≤ q ∧ q ^ num < r ^ den := by
  constructor
  · intro h
    obtain ⟨_, ⟨r, q, hr, hq, hm⟩, hbad⟩ := badReceiver_iff.mp h
    rcases le_total r q with hrq | hqr
    · exact ⟨r, q, hr, hq, hm, hrq, hbad r q hr hq hm⟩
    · have hm' : m = q * r := hm.trans (Nat.mul_comm r q)
      exact ⟨q, r, hq, hr, hm', hqr, hbad q r hq hr hm'⟩
  · rintro ⟨r, q, hr, hq, hm, hrq, hpow⟩
    apply badReceiver_iff.mpr
    refine ⟨?_, ⟨r, q, hr, hq, hm⟩, ?_⟩
    · rw [hm]
      exact Nat.not_prime_mul hr.ne_one hq.ne_one
    · intro s t hs ht hst
      have hfac : r * q = s * t := hm.symm.trans hst
      rcases (prime_mul_eq_prime_mul_iff hr hq hs ht).mp hfac with
        ⟨hrs, hqt⟩ | ⟨hrt, hqs⟩
      · simpa only [hrs, hqt] using hpow
      · have hswap : r ^ num < q ^ den :=
          lt_of_le_of_lt (pow_le_pow_left' hrq num)
            (lt_of_lt_of_le hpow (pow_le_pow_left' hrq den))
        simpa only [hrt, hqs] using hswap

theorem badReceiver_iff_orderedBadReceiver {num den m : ℕ} :
    BadReceiver num den m ↔ OrderedBadReceiver num den m :=
  badReceiver_iff_ordered_factors

/-- Strict badness is the strict complement of the rational-power acceptance
inequality, with a positive denominator. -/
theorem nat_pow_lt_iff_rpow_lt {r q num den : ℕ} (hden : 0 < den) :
    q ^ num < r ^ den ↔
      (q : ℝ) ^ ((num : ℝ) / (den : ℝ)) < (r : ℝ) := by
  simpa only [not_le] using
    (not_congr (nat_pow_le_iff_le_rpow (r := r) (q := q) (num := num) hden))

/-- Exact bridge from the finite complement predicate to the ordered analytic
region, retaining both prime-factor conditions and the factor ordering. -/
theorem badReceiver_iff_ordered_real_factors {num den m : ℕ}
    (hden : 0 < den) :
    BadReceiver num den m ↔
      ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q ∧ r ≤ q ∧
        (q : ℝ) ^ ((num : ℝ) / (den : ℝ)) < (r : ℝ) := by
  rw [badReceiver_iff_ordered_factors]
  constructor
  · rintro ⟨r, q, hr, hq, hm, hrq, hpow⟩
    exact ⟨r, q, hr, hq, hm, hrq, (nat_pow_lt_iff_rpow_lt hden).mp hpow⟩
  · rintro ⟨r, q, hr, hq, hm, hrq, hpow⟩
    exact ⟨r, q, hr, hq, hm, hrq, (nat_pow_lt_iff_rpow_lt hden).mpr hpow⟩

noncomputable section

/-- Ordered bad representations, indexed by the additive prime rather than
by a choice of factors, so each representation is counted only once. -/
def orderedBadPrimes (num den N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun p =>
    Nat.Prime p ∧ OrderedBadReceiver num den (N - p)

@[simp] theorem mem_orderedBadPrimes {num den N p : ℕ} :
    p ∈ orderedBadPrimes num den N ↔
      p < N ∧ Nat.Prime p ∧ OrderedBadReceiver num den (N - p) := by
  classical
  simp [orderedBadPrimes]

/-- The finite set used in the complement count is exactly the ordered bad
set; no inequality or multiplicity loss is introduced. -/
theorem badPrimes_eq_orderedBadPrimes (num den N : ℕ) :
    badPrimes num den N = orderedBadPrimes num den N := by
  classical
  ext p
  simp only [badPrimes, orderedBadPrimes, Finset.mem_filter,
    badReceiver_iff_orderedBadReceiver]

/-- The manuscript's ordered bad-region count is the exact complement count
`B`, when representations are indexed by the additive prime. -/
theorem B_eq_orderedBadPrimes_card (num den N : ℕ) :
    B num den N = (orderedBadPrimes num den N).card := by
  unfold B
  rw [badPrimes_eq_orderedBadPrimes]

/-- A direct real-power form of membership in the finite bad set. -/
theorem mem_badPrimes_iff_ordered_real_factors {num den N p : ℕ}
    (hden : 0 < den) :
    p ∈ badPrimes num den N ↔
      p < N ∧ Nat.Prime p ∧
        ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ N - p = r * q ∧ r ≤ q ∧
          (q : ℝ) ^ ((num : ℝ) / (den : ℝ)) < (r : ℝ) := by
  classical
  simp only [badPrimes, Finset.mem_filter, Finset.mem_range,
    badReceiver_iff_ordered_real_factors hden]

end

end ImbalancedChen
