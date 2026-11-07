import ImbalancedChen.RationalPowers

/-!
# P6: the prime-receiver and accepted-semiprime finite split

The prime-plus-prime part is independent of the exponent. The other part
retains the literal real-power bound on two prime receiver factors. Both
finite sets are indexed by the additive prime, rather than factor witnesses.
The partition and count identity hold for every real exponent.

This is an uncompiled source-review draft.
-/

namespace ImbalancedChen.P6

noncomputable section

/-- Additive primes in prime-plus-prime representations. The exponent argument
is retained for a common interface with the semiprime part and is unused. -/
def p6PrimePrimeAddends (_b : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun p => Nat.Prime p ∧ Nat.Prime (N - p)

/-- Additive primes with an accepted receiver that is a product of two primes.
Repeated prime factors are allowed, and each additive prime is counted once. -/
def p6AcceptedSemiprimeAddends (b : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun p => Nat.Prime p ∧
    ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ N - p = r * q ∧
      (r : ℝ) ≤ (q : ℝ) ^ b

@[simp] theorem p6Split_mem_primePrimeAddends {b : ℝ} {N p : ℕ} :
    p ∈ p6PrimePrimeAddends b N ↔
      p < N ∧ Nat.Prime p ∧ Nat.Prime (N - p) := by
  classical
  simp [p6PrimePrimeAddends]

@[simp] theorem p6Split_mem_acceptedSemiprimeAddends {b : ℝ} {N p : ℕ} :
    p ∈ p6AcceptedSemiprimeAddends b N ↔
      p < N ∧ Nat.Prime p ∧
        ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ N - p = r * q ∧
          (r : ℝ) ≤ (q : ℝ) ^ b := by
  classical
  simp [p6AcceptedSemiprimeAddends]

/-- The prime-plus-prime set is literally the same at any two exponents. -/
theorem p6Split_primePrimeAddends_independent (b c : ℝ) (N : ℕ) :
    p6PrimePrimeAddends b N = p6PrimePrimeAddends c N := by
  rfl

/-- The prime part has exactly the literal additive interpretation. -/
theorem p6Split_primePrimeAddends_iff_literal {b : ℝ} {N p : ℕ} :
    p ∈ p6PrimePrimeAddends b N ↔
      ∃ q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ N = p + q := by
  constructor
  · intro hp
    rcases p6Split_mem_primePrimeAddends.mp hp with ⟨hpN, hpPrime, hq⟩
    exact ⟨N - p, hpPrime, hq, by omega⟩
  · rintro ⟨q, hpPrime, hq, hN⟩
    have hqpos : 0 < q := hq.pos
    have hpN : p < N := by omega
    have hsub : N - p = q := by omega
    apply p6Split_mem_primePrimeAddends.mpr
    exact ⟨hpN, hpPrime, hsub.symm ▸ hq⟩

/-- The semiprime part has exactly the literal additive interpretation. -/
theorem p6Split_acceptedSemiprimeAddends_iff_literal
    {b : ℝ} {N p : ℕ} :
    p ∈ p6AcceptedSemiprimeAddends b N ↔
      ∃ r q : ℕ, Nat.Prime p ∧ Nat.Prime r ∧ Nat.Prime q ∧
        N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ b := by
  constructor
  · intro hp
    rcases p6Split_mem_acceptedSemiprimeAddends.mp hp with
      ⟨hpN, hpPrime, r, q, hr, hq, hsub, hpow⟩
    exact ⟨r, q, hpPrime, hr, hq, by omega, hpow⟩
  · rintro ⟨r, q, hpPrime, hr, hq, hN, hpow⟩
    have hreceiverpos : 0 < r * q := mul_pos hr.pos hq.pos
    have hpN : p < N := by omega
    have hsub : N - p = r * q := by omega
    exact p6Split_mem_acceptedSemiprimeAddends.mpr
      ⟨hpN, hpPrime, r, q, hr, hq, hsub, hpow⟩

/-- A product of two prime receiver factors cannot itself be prime. -/
theorem p6Split_prime_product_not_prime {m r q : ℕ}
    (hr : Nat.Prime r) (hq : Nat.Prime q) (hm : m = r * q) :
    ¬ Nat.Prime m := by
  rw [hm]
  exact Nat.not_prime_mul hr.ne_one hq.ne_one

/-- Membership in the accepted semiprime part excludes a prime receiver. -/
theorem p6Split_accepted_receiver_not_prime {b : ℝ} {N p : ℕ}
    (hp : p ∈ p6AcceptedSemiprimeAddends b N) :
    ¬ Nat.Prime (N - p) := by
  rcases p6Split_mem_acceptedSemiprimeAddends.mp hp with
    ⟨_, _, r, q, hr, hq, hsub, _⟩
  exact p6Split_prime_product_not_prime hr hq hsub

/-- The two finite parts are disjoint, including when receiver factors repeat. -/
theorem p6Split_disjoint (b : ℝ) (N : ℕ) :
    Disjoint (p6PrimePrimeAddends b N) (p6AcceptedSemiprimeAddends b N) := by
  apply Finset.disjoint_left.mpr
  intro p hpPrime hpSemi
  exact p6Split_accepted_receiver_not_prime hpSemi
    (p6Split_mem_primePrimeAddends.mp hpPrime).2.2

/-- Exact partition of accepted additive primes for any real exponent. -/
theorem p6Split_realImbalancedPrimes_eq_union (b : ℝ) (N : ℕ) :
    realImbalancedPrimes b N =
      p6PrimePrimeAddends b N ∪ p6AcceptedSemiprimeAddends b N := by
  classical
  ext p
  rw [mem_realImbalancedPrimes, Finset.mem_union,
    p6Split_mem_primePrimeAddends, p6Split_mem_acceptedSemiprimeAddends]
  constructor
  · rintro ⟨hpN, hpPrime, hreceiver⟩
    rcases hreceiver with hprime | hsemiprime
    · exact Or.inl ⟨hpN, hpPrime, hprime⟩
    · exact Or.inr ⟨hpN, hpPrime, hsemiprime⟩
  · rintro (⟨hpN, hpPrime, hprime⟩ | ⟨hpN, hpPrime, hsemiprime⟩)
    · exact ⟨hpN, hpPrime, Or.inl hprime⟩
    · exact ⟨hpN, hpPrime, Or.inr hsemiprime⟩

/-- The accepted count is exactly the sum of the two disjoint finite counts. -/
theorem p6Split_RealDb_eq_card_add_card (b : ℝ) (N : ℕ) :
    RealDb b N =
      (p6PrimePrimeAddends b N).card + (p6AcceptedSemiprimeAddends b N).card := by
  unfold RealDb
  rw [p6Split_realImbalancedPrimes_eq_union b N]
  exact Finset.card_union_of_disjoint (p6Split_disjoint b N)

end

end ImbalancedChen.P6
