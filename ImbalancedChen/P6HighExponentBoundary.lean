import ImbalancedChen.CurrentMainTheorem

/-!
# The exponent-one endpoint of the literal receiver condition

For every real exponent `b ≥ 1`, sorting the prime factors accepts every
prime-or-semiprime receiver. Consequently the literal count is exactly `D12`
and its complement vanishes, for every natural input `N`. Prime squares give
the sharp threshold: they are accepted exactly when `1 ≤ b`.

These are finite structural statements. They introduce no analytic bounds.
This draft has been checked against source declarations only, not compiled.
-/

namespace ImbalancedChen.P6

/-- With sorted prime factors, every exponent at least one accepts the
semiprime witness. -/
theorem ordered_prime_factors_accepted_of_one_le
    {b : ℝ} {r q : ℕ} (hb : 1 ≤ b) (hq : Nat.Prime q) (hrq : r ≤ q) :
    (r : ℝ) ≤ (q : ℝ) ^ b := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.one_lt.le
  have hrqR : (r : ℝ) ≤ (q : ℝ) := by exact_mod_cast hrq
  exact hrqR.trans (Real.self_le_rpow_of_one_le hqR hb)

/-- At and above exponent one, the real receiver predicate accepts precisely
all prime-or-semiprime receivers. Both possible initial factor orders are
handled explicitly. -/
theorem realImbalancedReceiver_iff_primeOrSemiprime_of_one_le
    {b : ℝ} {m : ℕ} (hb : 1 ≤ b) :
    RealImbalancedReceiver b m ↔ PrimeOrSemiprime m := by
  constructor
  · exact fun h => h.primeOrSemiprime
  · rintro (hprime | ⟨r, q, hr, hq, hm⟩)
    · exact Or.inl hprime
    · rcases le_total r q with hrq | hqr
      · exact Or.inr ⟨r, q, hr, hq, hm,
          ordered_prime_factors_accepted_of_one_le hb hq hrq⟩
      · exact Or.inr ⟨q, r, hq, hr, hm.trans (Nat.mul_comm r q),
          ordered_prime_factors_accepted_of_one_le hb hr hqr⟩

/-- There are no real bad receivers at or above exponent one. -/
theorem not_realBadReceiver_of_one_le {b : ℝ} {m : ℕ} (hb : 1 ≤ b) :
    ¬ RealBadReceiver b m := by
  rintro ⟨hreceiver, hbad⟩
  exact hbad ((realImbalancedReceiver_iff_primeOrSemiprime_of_one_le hb).mpr hreceiver)

/-- The ordered strict bad region is also empty at this endpoint. -/
theorem not_realOrderedBadReceiver_of_one_le {b : ℝ} {m : ℕ} (hb : 1 ≤ b) :
    ¬ RealOrderedBadReceiver b m := by
  rintro ⟨r, q, _hr, hq, _hm, hrq, hpow⟩
  exact (not_lt_of_ge (ordered_prime_factors_accepted_of_one_le hb hq hrq)) hpow

noncomputable section

/-- The accepted additive-prime set is exactly the Chen set for `b ≥ 1`. -/
theorem realImbalancedPrimes_eq_chenPrimes_of_one_le {b : ℝ} (hb : 1 ≤ b) (N : ℕ) :
    realImbalancedPrimes b N = chenPrimes N := by
  classical
  ext p
  rw [mem_realImbalancedPrimes, mem_chenPrimes,
    realImbalancedReceiver_iff_primeOrSemiprime_of_one_le hb]

/-- Exact finite endpoint equality; this is not an asymptotic estimate. -/
theorem RealDb_eq_D12_of_one_le {b : ℝ} (hb : 1 ≤ b) (N : ℕ) :
    RealDb b N = D12 N := by
  unfold RealDb D12
  rw [realImbalancedPrimes_eq_chenPrimes_of_one_le hb N]

theorem realBadPrimes_eq_empty_of_one_le {b : ℝ} (hb : 1 ≤ b) (N : ℕ) :
    realBadPrimes b N = ∅ := by
  classical
  ext p
  constructor
  · intro hp
    rcases mem_realBadPrimes.mp hp with ⟨_hpN, _hpprime, hreceiver, hbad⟩
    exact False.elim (not_realBadReceiver_of_one_le hb ⟨hreceiver, hbad⟩)
  · intro hp
    simp at hp

theorem RealB_eq_zero_of_one_le {b : ℝ} (hb : 1 ≤ b) (N : ℕ) :
    RealB b N = 0 := by
  unfold RealB
  rw [realBadPrimes_eq_empty_of_one_le hb N, Finset.card_empty]

theorem realOrderedBadPrimes_eq_empty_of_one_le {b : ℝ} (hb : 1 ≤ b) (N : ℕ) :
    realOrderedBadPrimes b N = ∅ := by
  classical
  ext p
  constructor
  · intro hp
    exact False.elim (not_realOrderedBadReceiver_of_one_le hb
      (mem_realOrderedBadPrimes.mp hp).2.2)
  · intro hp
    simp at hp

end

/-- Below exponent one, a prime square lies in the literal strict bad
region. The existing ordered-bad equivalence rejects every factor witness,
including the repeated-factor case. -/
theorem realBadReceiver_prime_sq_of_lt_one {b : ℝ} {p : ℕ}
    (hp : Nat.Prime p) (hb : b < 1) : RealBadReceiver b (p ^ 2) := by
  apply (realBadReceiver_iff_realOrderedBadReceiver hb).mpr
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  exact ⟨p, p, hp, hp, by rw [pow_two], le_rfl,
    Real.rpow_lt_self_of_one_lt hpR hb⟩

/-- Every prime square is accepted at and above exponent one. -/
theorem realImbalancedReceiver_prime_sq_of_one_le {b : ℝ} {p : ℕ}
    (hp : Nat.Prime p) (hb : 1 ≤ b) : RealImbalancedReceiver b (p ^ 2) := by
  exact Or.inr ⟨p, p, hp, hp, by rw [pow_two],
    ordered_prime_factors_accepted_of_one_le hb hp le_rfl⟩

/-- Prime squares witness that exponent one is the exact acceptance
threshold, over the full real exponent range. -/
theorem realImbalancedReceiver_prime_sq_iff_one_le {b : ℝ} {p : ℕ}
    (hp : Nat.Prime p) : RealImbalancedReceiver b (p ^ 2) ↔ 1 ≤ b := by
  constructor
  · intro haccepted
    by_contra hb
    exact (realBadReceiver_prime_sq_of_lt_one hp (lt_of_not_ge hb)).2 haccepted
  · exact realImbalancedReceiver_prime_sq_of_one_le hp

theorem realBadReceiver_prime_sq_iff_lt_one {b : ℝ} {p : ℕ}
    (hp : Nat.Prime p) : RealBadReceiver b (p ^ 2) ↔ b < 1 := by
  constructor
  · intro hbad
    by_contra hb
    exact not_realBadReceiver_of_one_le (le_of_not_gt hb) hbad
  · exact realBadReceiver_prime_sq_of_lt_one hp

end ImbalancedChen.P6
