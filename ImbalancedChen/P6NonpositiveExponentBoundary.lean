import ImbalancedChen.RationalPowers
import ImbalancedChen.Counting
import ImbalancedChen.CurrentMainTheorem

/-!
# The nonpositive real-exponent boundary

For every real `b ≤ 0`, no pair of prime factors satisfies the imbalance
inequality: the left side is strictly greater than one and the right side is
at most one. Thus `RealDb` is precisely the finite prime-plus-prime count,
and `RealB` is precisely the finite prime-plus-semiprime count. All sets are
indexed by the additive prime; factor witnesses never cause multiplicity.
These are finite arithmetic identities, with no analytic hypotheses.
-/

namespace ImbalancedChen.P6

/-- A prime base raised to a nonpositive real exponent is at most one. -/
theorem prime_rpow_le_one_of_nonpos {b : ℝ} {q : ℕ}
    (hb : b ≤ 0) (hq : Nat.Prime q) : (q : ℝ) ^ b ≤ 1 := by
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.one_lt.le
  exact Real.rpow_le_one_of_one_le_of_nonpos hqR hb

/-- The semiprime branch is impossible at every nonpositive real exponent. -/
theorem not_prime_factor_imbalance_of_nonpos {b : ℝ} {r q : ℕ}
    (hb : b ≤ 0) (hr : Nat.Prime r) (hq : Nat.Prime q) :
    ¬ (r : ℝ) ≤ (q : ℝ) ^ b := by
  have hrR : (1 : ℝ) < (r : ℝ) := by exact_mod_cast hr.one_lt
  exact not_le_of_gt (lt_of_le_of_lt (prime_rpow_le_one_of_nonpos hb hq) hrR)

/-- For arbitrary real `b ≤ 0`, the accepted receivers are exactly primes. -/
theorem realImbalancedReceiver_iff_prime_of_nonpos {b : ℝ} {m : ℕ}
    (hb : b ≤ 0) : RealImbalancedReceiver b m ↔ Nat.Prime m := by
  constructor
  · rintro (hm | ⟨r, q, hr, hq, _, hpow⟩)
    · exact hm
    · exact (not_prime_factor_imbalance_of_nonpos hb hr hq hpow).elim
  · exact Or.inl

/-- The product-of-two-primes condition allows repeated factors. -/
def SemiprimeReceiver (m : ℕ) : Prop :=
  ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q

/-- At a nonpositive exponent, every semiprime is bad, and all bad receivers
are semiprime. The prime and semiprime alternatives cannot overlap. -/
theorem realBadReceiver_iff_semiprime_of_nonpos {b : ℝ} {m : ℕ}
    (hb : b ≤ 0) : RealBadReceiver b m ↔ SemiprimeReceiver m := by
  constructor
  · rintro ⟨hreceiver, hbad⟩
    rcases hreceiver with hm | hfactors
    · exact (hbad (Or.inl hm)).elim
    · exact hfactors
  · rintro ⟨r, q, hr, hq, hm⟩
    refine ⟨Or.inr ⟨r, q, hr, hq, hm⟩, ?_⟩
    intro haccepted
    have hmprime : Nat.Prime m :=
      (realImbalancedReceiver_iff_prime_of_nonpos hb).mp haccepted
    have hmnot : ¬ Nat.Prime m := by
      rw [hm]
      exact Nat.not_prime_mul hr.ne_one hq.ne_one
    exact hmnot hmprime

noncomputable section

/-- Additive primes whose complementary receiver is prime. -/
def primePlusPrimePrimes (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun p => Nat.Prime p ∧ Nat.Prime (N - p)

/-- Prime-plus-prime representations, counted once per additive prime. -/
def primePlusPrimeCount (N : ℕ) : ℕ := (primePlusPrimePrimes N).card

/-- Additive primes whose complementary receiver has two prime factors. -/
def primePlusSemiprimePrimes (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun p => Nat.Prime p ∧ SemiprimeReceiver (N - p)

/-- Prime-plus-semiprime representations, counted once per additive prime. -/
def primePlusSemiprimeCount (N : ℕ) : ℕ := (primePlusSemiprimePrimes N).card

@[simp] theorem mem_primePlusPrimePrimes {N p : ℕ} :
    p ∈ primePlusPrimePrimes N ↔ p < N ∧ Nat.Prime p ∧ Nat.Prime (N - p) := by
  classical
  simp [primePlusPrimePrimes]

@[simp] theorem mem_primePlusSemiprimePrimes {N p : ℕ} :
    p ∈ primePlusSemiprimePrimes N ↔
      p < N ∧ Nat.Prime p ∧ SemiprimeReceiver (N - p) := by
  classical
  simp [primePlusSemiprimePrimes]

/-- The prime-plus-prime finite set gives literal additive representations. -/
theorem mem_primePlusPrimePrimes_iff_exists {N p : ℕ} :
    p ∈ primePlusPrimePrimes N ↔
      Nat.Prime p ∧ ∃ q : ℕ, Nat.Prime q ∧ N = p + q := by
  rw [mem_primePlusPrimePrimes]
  constructor
  · rintro ⟨hpN, hp, hq⟩
    exact ⟨hp, N - p, hq, by omega⟩
  · rintro ⟨hp, q, hq, hN⟩
    have hqpos := hq.pos
    have hpN : p < N := by omega
    have hsub : N - p = q := by omega
    exact ⟨hpN, hp, hsub.symm ▸ hq⟩

/-- Exact equality of accepted finite sets at the nonpositive boundary. -/
theorem realImbalancedPrimes_eq_primePlusPrimePrimes_of_nonpos
    {b : ℝ} (hb : b ≤ 0) (N : ℕ) :
    realImbalancedPrimes b N = primePlusPrimePrimes N := by
  classical
  ext p
  rw [mem_realImbalancedPrimes, mem_primePlusPrimePrimes,
    realImbalancedReceiver_iff_prime_of_nonpos hb]

/-- The accepted real-exponent count is exactly the prime-plus-prime count. -/
theorem RealDb_eq_primePlusPrimeCount_of_nonpos
    {b : ℝ} (hb : b ≤ 0) (N : ℕ) :
    RealDb b N = primePlusPrimeCount N := by
  unfold RealDb primePlusPrimeCount
  rw [realImbalancedPrimes_eq_primePlusPrimePrimes_of_nonpos hb]

/-- Exact equality of complement finite sets at the nonpositive boundary. -/
theorem realBadPrimes_eq_primePlusSemiprimePrimes_of_nonpos
    {b : ℝ} (hb : b ≤ 0) (N : ℕ) :
    realBadPrimes b N = primePlusSemiprimePrimes N := by
  classical
  ext p
  rw [mem_realBadPrimes, mem_primePlusSemiprimePrimes]
  change (p < N ∧ Nat.Prime p ∧ RealBadReceiver b (N - p)) ↔
    (p < N ∧ Nat.Prime p ∧ SemiprimeReceiver (N - p))
  rw [realBadReceiver_iff_semiprime_of_nonpos hb]

/-- `RealB` counts all semiprime receivers at each nonpositive exponent. -/
theorem RealB_eq_primePlusSemiprimeCount_of_nonpos
    {b : ℝ} (hb : b ≤ 0) (N : ℕ) :
    RealB b N = primePlusSemiprimeCount N := by
  unfold RealB primePlusSemiprimeCount
  rw [realBadPrimes_eq_primePlusSemiprimePrimes_of_nonpos hb]

/-- The exact prime/semiprime partition at the endpoint has no estimates. -/
theorem D12_eq_primePlusPrimeCount_add_primePlusSemiprimeCount (N : ℕ) :
    D12 N = primePlusPrimeCount N + primePlusSemiprimeCount N := by
  have h := D12_eq_RealDb_add_RealB (0 : ℝ) N
  rw [RealDb_eq_primePlusPrimeCount_of_nonpos (le_refl (0 : ℝ)),
    RealB_eq_primePlusSemiprimeCount_of_nonpos (le_refl (0 : ℝ))] at h
  exact h

/-- The complement is exactly the Chen count minus the prime-plus-prime count. -/
theorem RealB_eq_D12_sub_primePlusPrimeCount_of_nonpos
    {b : ℝ} (hb : b ≤ 0) (N : ℕ) :
    RealB b N = D12 N - primePlusPrimeCount N := by
  have h := D12_eq_RealDb_add_RealB b N
  rw [RealDb_eq_primePlusPrimeCount_of_nonpos hb] at h
  omega

/-- All nonpositive real exponents produce the same accepted count. -/
theorem RealDb_eq_of_nonpos {b c : ℝ} (hb : b ≤ 0) (hc : c ≤ 0) (N : ℕ) :
    RealDb b N = RealDb c N := by
  rw [RealDb_eq_primePlusPrimeCount_of_nonpos hb,
    RealDb_eq_primePlusPrimeCount_of_nonpos hc]

/-- All nonpositive real exponents produce the same semiprime complement. -/
theorem RealB_eq_of_nonpos {b c : ℝ} (hb : b ≤ 0) (hc : c ≤ 0) (N : ℕ) :
    RealB b N = RealB c N := by
  rw [RealB_eq_primePlusSemiprimeCount_of_nonpos hb,
    RealB_eq_primePlusSemiprimeCount_of_nonpos hc]

end

end ImbalancedChen.P6
