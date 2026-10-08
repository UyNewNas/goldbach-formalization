import Mathlib

/-!
# Finite counting core for the imbalanced Chen transfer

This file proves only the exact finite decomposition underlying the manuscript's
transfer argument. It does not assume or prove a Chen lower bound, a sieve upper
bound, a prime number theorem, or any claimed numerical analytic constant.

Representations are indexed by the additive prime `p`, so different witnesses for
the receiver do not cause multiple counting. The receiver `1` is excluded from
`PrimeOrSemiprime`; thus `D12` is not silently identified with the manuscript's
`Omega <= 2` convention, which can also count the receiver `1`.

For a positive denominator, `r ^ den <= q ^ num` is the exact integer-power
version of the rational-exponent imbalance condition. The partition theorems
hold for all natural `num` and `den`, without needing analytic restrictions on
the exponent. Equivalence to a real-power formulation is a separate obligation.
-/

namespace ImbalancedChen

/-- A receiver is a prime or a product of two primes, with multiplicity allowed. -/
def PrimeOrSemiprime (m : ℕ) : Prop :=
  Nat.Prime m ∨ ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q

/-- Exact rational-exponent receiver condition; the denominator is `den`.

No factor ordering is needed: the existential quantifier allows the factors to
be exchanged, and each additive prime is still counted only once. -/
def ImbalancedReceiver (num den m : ℕ) : Prop :=
  Nat.Prime m ∨
    ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q ∧ r ^ den ≤ q ^ num

/-- The receivers removed from the prime-or-semiprime count. -/
def BadReceiver (num den m : ℕ) : Prop :=
  PrimeOrSemiprime m ∧ ¬ ImbalancedReceiver num den m

theorem ImbalancedReceiver.primeOrSemiprime {num den m : ℕ}
    (h : ImbalancedReceiver num den m) : PrimeOrSemiprime m := by
  rcases h with hprime | ⟨r, q, hr, hq, hm, _⟩
  · exact Or.inl hprime
  · exact Or.inr ⟨r, q, hr, hq, hm⟩

/-- An accepted semiprime witness suffices, independently of other witnesses. -/
theorem imbalancedReceiver_of_factors {num den m r q : ℕ}
    (hr : Nat.Prime r) (hq : Nat.Prime q) (hm : m = r * q)
    (hpow : r ^ den ≤ q ^ num) : ImbalancedReceiver num den m :=
  Or.inr ⟨r, q, hr, hq, hm, hpow⟩

/-- Explicit factor description of a removed receiver.

Every prime factorization of a bad receiver violates the imbalance inequality.
This avoids making an unproved uniqueness-of-factorization claim in the count. -/
theorem badReceiver_iff {num den m : ℕ} :
    BadReceiver num den m ↔
      (¬ Nat.Prime m) ∧
      (∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q) ∧
      (∀ r q : ℕ, Nat.Prime r → Nat.Prime q → m = r * q → q ^ num < r ^ den) := by
  constructor
  · rintro ⟨hreceiver, hbad⟩
    have hnotprime : ¬ Nat.Prime m := fun hm => hbad (Or.inl hm)
    refine ⟨hnotprime, ?_, ?_⟩
    · rcases hreceiver with hm | hfactors
      · exact (hnotprime hm).elim
      · exact hfactors
    · intro r q hr hq hm
      exact lt_of_not_ge fun hpow => hbad (Or.inr ⟨r, q, hr, hq, hm, hpow⟩)
  · rintro ⟨hnotprime, hfactors, hbad⟩
    refine ⟨Or.inr hfactors, ?_⟩
    rintro (hm | ⟨r, q, hr, hq, hm, hpow⟩)
    · exact hnotprime hm
    · exact (not_lt_of_ge hpow) (hbad r q hr hq hm)

noncomputable section

/-- Additive primes whose receiver is prime or semiprime. -/
def chenPrimes (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun p => Nat.Prime p ∧ PrimeOrSemiprime (N - p)

/-- Additive primes with an imbalanced receiver, each counted once. -/
def imbalancedPrimes (num den N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun p => Nat.Prime p ∧ ImbalancedReceiver num den (N - p)

/-- Additive primes removed from `chenPrimes`. -/
def badPrimes (num den N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun p => Nat.Prime p ∧ BadReceiver num den (N - p)

def D12 (N : ℕ) : ℕ := (chenPrimes N).card

def Db (num den N : ℕ) : ℕ := (imbalancedPrimes num den N).card

def B (num den N : ℕ) : ℕ := (badPrimes num den N).card

@[simp] theorem mem_chenPrimes {N p : ℕ} :
    p ∈ chenPrimes N ↔ p < N ∧ Nat.Prime p ∧ PrimeOrSemiprime (N - p) := by
  classical
  simp [chenPrimes]

@[simp] theorem mem_imbalancedPrimes {num den N p : ℕ} :
    p ∈ imbalancedPrimes num den N ↔
      p < N ∧ Nat.Prime p ∧ ImbalancedReceiver num den (N - p) := by
  classical
  simp [imbalancedPrimes]

@[simp] theorem mem_badPrimes {num den N p : ℕ} :
    p ∈ badPrimes num den N ↔
      p < N ∧ Nat.Prime p ∧ PrimeOrSemiprime (N - p) ∧
        ¬ ImbalancedReceiver num den (N - p) := by
  classical
  unfold badPrimes
  rw [Finset.mem_filter, Finset.mem_range]
  rfl

theorem imbalancedPrimes_subset_chenPrimes (num den N : ℕ) :
    imbalancedPrimes num den N ⊆ chenPrimes N := by
  intro p hp
  rcases mem_imbalancedPrimes.mp hp with ⟨hpN, hpprime, hreceiver⟩
  exact mem_chenPrimes.mpr ⟨hpN, hpprime, hreceiver.primeOrSemiprime⟩

theorem badPrimes_subset_chenPrimes (num den N : ℕ) :
    badPrimes num den N ⊆ chenPrimes N := by
  intro p hp
  rcases mem_badPrimes.mp hp with ⟨hpN, hpprime, hreceiver, _⟩
  exact mem_chenPrimes.mpr ⟨hpN, hpprime, hreceiver⟩

/-- The two pieces of the finite transfer decomposition are disjoint. -/
theorem imbalancedPrimes_disjoint_badPrimes (num den N : ℕ) :
    Disjoint (imbalancedPrimes num den N) (badPrimes num den N) := by
  apply Finset.disjoint_left.mpr
  intro p hgood hbad
  exact (mem_badPrimes.mp hbad).2.2.2 (mem_imbalancedPrimes.mp hgood).2.2

/-- Exact finite partition, with no analytic hypotheses. -/
theorem chenPrimes_eq_union (num den N : ℕ) :
    chenPrimes N = imbalancedPrimes num den N ∪ badPrimes num den N := by
  classical
  ext p
  rw [Finset.mem_union, mem_chenPrimes, mem_imbalancedPrimes, mem_badPrimes]
  constructor
  · rintro ⟨hpN, hpprime, hreceiver⟩
    by_cases hgood : ImbalancedReceiver num den (N - p)
    · exact Or.inl ⟨hpN, hpprime, hgood⟩
    · exact Or.inr ⟨hpN, hpprime, hreceiver, hgood⟩
  · rintro (⟨hpN, hpprime, hgood⟩ | ⟨hpN, hpprime, hreceiver, _⟩)
    · exact ⟨hpN, hpprime, hgood.primeOrSemiprime⟩
    · exact ⟨hpN, hpprime, hreceiver⟩

/-- The exact additive-prime counting identity. -/
theorem D12_eq_Db_add_B (num den N : ℕ) :
    D12 N = Db num den N + B num den N := by
  unfold D12 Db B
  rw [chenPrimes_eq_union num den N]
  exact Finset.card_union_of_disjoint (imbalancedPrimes_disjoint_badPrimes num den N)

/-- The count subtraction is exact even in natural numbers. -/
theorem Db_eq_D12_sub_B (num den N : ℕ) :
    Db num den N = D12 N - B num den N := by
  have h := D12_eq_Db_add_B num den N
  omega

theorem B_le_D12 (num den N : ℕ) : B num den N ≤ D12 N := by
  have h := D12_eq_Db_add_B num den N
  omega

/-- An untruncated real-valued form for use with analytic bounds. -/
theorem Db_cast_eq_D12_sub_B (num den N : ℕ) :
    (Db num den N : ℝ) = (D12 N : ℝ) - (B num den N : ℝ) := by
  have h : (D12 N : ℝ) = (Db num den N : ℝ) + (B num den N : ℝ) := by
    exact_mod_cast D12_eq_Db_add_B num den N
  linarith

/-- The finite transfer inequality. The analytic estimates are explicit
hypotheses, not axioms or disguised conclusions of this theorem. -/
theorem finite_transfer {num den N : ℕ} {lower upper : ℝ}
    (hLower : lower ≤ (D12 N : ℝ)) (hUpper : (B num den N : ℝ) ≤ upper) :
    lower - upper ≤ (Db num den N : ℝ) := by
  rw [Db_cast_eq_D12_sub_B num den N]
  linarith

/-- A strictly positive transfer margin gives an actual additive prime. -/
theorem exists_imbalanced_of_lower_gt_upper {num den N : ℕ} {lower upper : ℝ}
    (hLower : lower ≤ (D12 N : ℝ)) (hUpper : (B num den N : ℝ) ≤ upper)
    (hmargin : upper < lower) :
    ∃ p : ℕ, p < N ∧ Nat.Prime p ∧ ImbalancedReceiver num den (N - p) := by
  have htransfer := finite_transfer hLower hUpper
  have hreal : (0 : ℝ) < (Db num den N : ℝ) := by linarith
  have hnat : 0 < Db num den N := by exact_mod_cast hreal
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hnat
  exact ⟨p, mem_imbalancedPrimes.mp hp⟩

end

end ImbalancedChen
