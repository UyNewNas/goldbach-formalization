import ImbalancedChen.Counting
import Mathlib.NumberTheory.AlmostPrime

/-!
# Multiplicity and the receiver-one correction

This module uses mathlib's `ArithmeticFunction.cardFactors`, written `Ω`, which
counts prime factors with multiplicity. For a positive receiver, `Ω m ≤ 2`
means exactly that `m = 1` or `m` is prime or a product of two primes.

The manuscript's `Ω ≤ 2` convention therefore differs from `D12` in
`ImbalancedChen.Counting` by precisely one representation when `N - 1` is
prime, and by zero otherwise. Both counts are indexed by the additive prime,
not by a choice of factorization. The carrier `Finset.range N` ensures that
the receiver is positive, so mathlib's convention `Ω 0 = 0` causes no extra
representation.

Only exact arithmetic and finite counting are used here. No analytic estimate
is assumed. Source API checked against mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; compilation remains a separate check.
-/

namespace ImbalancedChen

open scoped ArithmeticFunction.Omega

/-- Mathlib's exact multiplicity-two predicate is equivalent to a product of
two primes. Repeated prime factors are allowed. -/
theorem isSemiprime_iff_exists_primes_mul {m : ℕ} :
    Nat.IsSemiprime m ↔
      ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q := by
  constructor
  · rintro ⟨hm, hΩ⟩
    change m.primeFactorsList.length = 2 at hΩ
    obtain ⟨r, q, hlist⟩ := List.length_eq_two.mp hΩ
    refine ⟨r, q, ?_, ?_, ?_⟩
    · apply Nat.prime_of_mem_primeFactorsList (n := m)
      simp [hlist]
    · apply Nat.prime_of_mem_primeFactorsList (n := m)
      simp [hlist]
    · simpa [hlist] using (Nat.prod_primeFactorsList hm).symm
  · rintro ⟨r, q, hr, hq, rfl⟩
    exact hr.mul_isAlmostPrime_two hq

theorem PrimeOrSemiprime.pos {m : ℕ} (h : PrimeOrSemiprime m) : 0 < m := by
  rcases h with hp | ⟨r, q, hr, hq, rfl⟩
  · exact hp.pos
  · exact Nat.mul_pos hr.pos hq.pos

theorem PrimeOrSemiprime.cardFactors_eq_one_or_two {m : ℕ}
    (h : PrimeOrSemiprime m) : Ω m = 1 ∨ Ω m = 2 := by
  rcases h with hp | ⟨r, q, hr, hq, rfl⟩
  · exact Or.inl (ArithmeticFunction.cardFactors_apply_prime hp)
  · exact Or.inr (hr.mul_isAlmostPrime_two hq).2

@[simp] theorem not_primeOrSemiprime_one : ¬ PrimeOrSemiprime 1 := by
  intro h
  have hΩ := h.cardFactors_eq_one_or_two
  simp at hΩ

/-- The receiver-one case cannot be dropped from the `Ω ≤ 2` convention. -/
theorem cardFactors_le_two_iff_of_pos {m : ℕ} (hm : 0 < m) :
    Ω m ≤ 2 ↔ m = 1 ∨ PrimeOrSemiprime m := by
  constructor
  · intro hΩ
    have hcases : Ω m = 0 ∨ Ω m = 1 ∨ Ω m = 2 := by omega
    rcases hcases with hzero | hone | htwo
    · exact Or.inl
        ((ArithmeticFunction.cardFactors_eq_zero_iff_eq_zero_or_one.mp hzero).resolve_left
          (Nat.ne_of_gt hm))
    · exact Or.inr (Or.inl (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp hone))
    · exact Or.inr (Or.inr
        (isSemiprime_iff_exists_primes_mul.mp ⟨Nat.ne_of_gt hm, htwo⟩))
  · rintro (rfl | h)
    · simp
    · rcases h.cardFactors_eq_one_or_two with hone | htwo <;> omega

/-- A direct bridge to mathlib's at-most-two predicate, including its exclusion
of zero and its inclusion of one. -/
theorem isAtMostAlmostPrime_two_iff {m : ℕ} :
    Nat.IsAtMostAlmostPrime 2 m ↔ m = 1 ∨ PrimeOrSemiprime m := by
  constructor
  · rintro ⟨hm, hΩ⟩
    exact (cardFactors_le_two_iff_of_pos (Nat.pos_of_ne_zero hm)).mp hΩ
  · intro h
    have hm : 0 < m := by
      rcases h with rfl | hreceiver
      · exact Nat.zero_lt_one
      · exact hreceiver.pos
    exact ⟨Nat.ne_of_gt hm, (cardFactors_le_two_iff_of_pos hm).mpr h⟩

noncomputable section

/-- The manuscript's Chen prime set: prime additive summands with a positive
receiver having at most two prime factors, counted with multiplicity. -/
def omegaChenPrimes (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun p => Nat.Prime p ∧ Ω (N - p) ≤ 2

/-- The manuscript's Chen count, including the possible receiver `1`. -/
def D12Omega (N : ℕ) : ℕ := (omegaChenPrimes N).card

/-- The sole possible prime summand with receiver one. -/
def unitReceiverPrimes (N : ℕ) : Finset ℕ :=
  if Nat.Prime (N - 1) then {N - 1} else ∅

@[simp] theorem mem_omegaChenPrimes {N p : ℕ} :
    p ∈ omegaChenPrimes N ↔ p < N ∧ Nat.Prime p ∧ Ω (N - p) ≤ 2 := by
  classical
  simp [omegaChenPrimes]

@[simp] theorem mem_unitReceiverPrimes {N p : ℕ} :
    p ∈ unitReceiverPrimes N ↔ p < N ∧ Nat.Prime p ∧ N - p = 1 := by
  classical
  by_cases hprime : Nat.Prime (N - 1)
  · rw [unitReceiverPrimes, if_pos hprime, Finset.mem_singleton]
    constructor
    · rintro rfl
      have hge := hprime.two_le
      exact ⟨by omega, hprime, by omega⟩
    · rintro ⟨hpN, _, hunit⟩
      omega
  · rw [unitReceiverPrimes, if_neg hprime]
    simp only [Finset.notMem_empty, false_iff]
    rintro ⟨hpN, hp, hunit⟩
    have heq : p = N - 1 := by omega
    exact hprime (heq ▸ hp)

/-- Exact receiver partition, including the exceptional unit receiver. -/
theorem omegaChenPrimes_eq_chenPrimes_union (N : ℕ) :
    omegaChenPrimes N = chenPrimes N ∪ unitReceiverPrimes N := by
  classical
  ext p
  rw [mem_omegaChenPrimes, Finset.mem_union, mem_chenPrimes, mem_unitReceiverPrimes]
  constructor
  · rintro ⟨hpN, hp, hΩ⟩
    have hpos : 0 < N - p := by omega
    rcases (cardFactors_le_two_iff_of_pos hpos).mp hΩ with hunit | hreceiver
    · exact Or.inr ⟨hpN, hp, hunit⟩
    · exact Or.inl ⟨hpN, hp, hreceiver⟩
  · rintro (⟨hpN, hp, hreceiver⟩ | ⟨hpN, hp, hunit⟩)
    · refine ⟨hpN, hp, ?_⟩
      have hpos : 0 < N - p := by omega
      exact (cardFactors_le_two_iff_of_pos hpos).mpr (Or.inr hreceiver)
    · refine ⟨hpN, hp, ?_⟩
      simp [hunit]

theorem chenPrimes_disjoint_unitReceiverPrimes (N : ℕ) :
    Disjoint (chenPrimes N) (unitReceiverPrimes N) := by
  apply Finset.disjoint_left.mpr
  intro p hp hu
  have hreceiver := (mem_chenPrimes.mp hp).2.2
  have hunit := (mem_unitReceiverPrimes.mp hu).2.2
  rw [hunit] at hreceiver
  exact not_primeOrSemiprime_one hreceiver

@[simp] theorem card_unitReceiverPrimes (N : ℕ) :
    (unitReceiverPrimes N).card = if Nat.Prime (N - 1) then 1 else 0 := by
  classical
  by_cases hprime : Nat.Prime (N - 1) <;> simp [unitReceiverPrimes, hprime]

/-- The discrepancy is exactly the indicator that `N - 1` is prime. -/
theorem D12Omega_eq_D12_add_indicator (N : ℕ) :
    D12Omega N = D12 N + (if Nat.Prime (N - 1) then 1 else 0) := by
  classical
  unfold D12Omega D12
  rw [omegaChenPrimes_eq_chenPrimes_union,
    Finset.card_union_of_disjoint (chenPrimes_disjoint_unitReceiverPrimes N),
    card_unitReceiverPrimes]

theorem D12Omega_sub_D12_eq_indicator (N : ℕ) :
    D12Omega N - D12 N = if Nat.Prime (N - 1) then 1 else 0 := by
  have h := D12Omega_eq_D12_add_indicator N
  omega

theorem D12_le_D12Omega (N : ℕ) : D12 N ≤ D12Omega N := by
  have h := D12Omega_eq_D12_add_indicator N
  omega

theorem D12Omega_le_D12_add_one (N : ℕ) : D12Omega N ≤ D12 N + 1 := by
  have h := D12Omega_eq_D12_add_indicator N
  split_ifs at h <;> omega

theorem D12Omega_sub_D12_le_one (N : ℕ) : D12Omega N - D12 N ≤ 1 := by
  have h := D12Omega_le_D12_add_one N
  omega

/-- The complete finite identity in the manuscript's counting convention. -/
theorem D12Omega_eq_Db_add_B_add_indicator (num den N : ℕ) :
    D12Omega N = Db num den N + B num den N +
      (if Nat.Prime (N - 1) then 1 else 0) := by
  rw [D12Omega_eq_D12_add_indicator, D12_eq_Db_add_B num den N]

theorem D12Omega_le_Db_add_B_add_one (num den N : ℕ) :
    D12Omega N ≤ Db num den N + B num den N + 1 := by
  rw [← D12_eq_Db_add_B num den N]
  exact D12Omega_le_D12_add_one N

/-- The real-valued count inequality avoids truncated subtraction and retains
the manuscript's required correction by at most one. -/
theorem D12Omega_sub_B_sub_one_le_Db (num den N : ℕ) :
    (D12Omega N : ℝ) - (B num den N : ℝ) - 1 ≤ (Db num den N : ℝ) := by
  have h : (D12Omega N : ℝ) ≤ (Db num den N : ℝ) + (B num den N : ℝ) + 1 := by
    exact_mod_cast D12Omega_le_Db_add_B_add_one num den N
  linarith

end

end ImbalancedChen
