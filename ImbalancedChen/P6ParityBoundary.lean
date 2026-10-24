import ImbalancedChen.CurrentMainTheorem
import ImbalancedChen.Multiplicity
import Mathlib.Algebra.Ring.Parity

/-!
# Actual receiver parity and the additive-prime-two correction

Source-only draft, 2026-10-24. Not compiled or kernel checked.
The natural subtraction bound is explicit: without `p ≤ N`, parity of
`N - p` would be false because natural subtraction can truncate to zero.
The finite sets below use the existing literal real-exponent receiver.
Pinned source APIs: mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
The source SHA256 and dependency hashes are recorded in the adjacent CP.md.
-/

namespace ImbalancedChen.P6

/-- Every receiver in the actual prime-or-semiprime convention is at least two.
This is stronger than positivity and explicitly excludes the unit receiver. -/
theorem primeOrSemiprime_two_le {m : ℕ} (hm : PrimeOrSemiprime m) :
    2 ≤ m := by
  rcases hm with hm | ⟨r, q, hr, hq, rfl⟩
  · exact hm.two_le
  · have hmul := Nat.mul_le_mul hr.two_le hq.two_le
    omega

/-- An odd additive prime below an even target has an odd actual receiver. -/
theorem receiver_odd_of_even_of_prime_ne_two {N p : ℕ}
    (hN : Even N) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hpN : p ≤ N) :
    Odd (N - p) := by
  exact (Nat.odd_sub' hpN).mpr
    ⟨fun _ => hN, fun _ => hp.odd_of_ne_two hp2⟩

/-- Oddness concerns every factor witness, independently of factor ordering. -/
theorem receiver_factors_odd {N p r q : ℕ}
    (hN : Even N) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hpN : p ≤ N)
    (hm : N - p = r * q) : Odd r ∧ Odd q := by
  have hodd := receiver_odd_of_even_of_prime_ne_two hN hp hp2 hpN
  rw [hm] at hodd
  exact Nat.odd_mul.mp hodd

/-- In particular every ordered bad-semiprime witness has both factors odd. -/
theorem realOrderedBadReceiver_has_odd_factors {b : ℝ} {N p : ℕ}
    (hN : Even N) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hpN : p ≤ N)
    (hm : RealOrderedBadReceiver b (N - p)) :
    ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ N - p = r * q ∧
      r ≤ q ∧ (q : ℝ) ^ b < (r : ℝ) ∧ Odd r ∧ Odd q := by
  obtain ⟨r, q, hr, hq, hmul, hrq, hpow⟩ := hm
  obtain ⟨hrodd, hqodd⟩ := receiver_factors_odd hN hp hp2 hpN hmul
  exact ⟨r, q, hr, hq, hmul, hrq, hpow, hrodd, hqodd⟩

noncomputable section

/-- The actual accepted prime set after deleting the sole even additive prime.
No factor witness or different receiver convention is counted here. -/
def realGoodPrimes (b : ℝ) (N : ℕ) : Finset ℕ :=
  (realImbalancedPrimes b N).erase 2

@[simp] theorem mem_realGoodPrimes {b : ℝ} {N p : ℕ} :
    p ∈ realGoodPrimes b N ↔
      p ≠ 2 ∧ p < N ∧ Nat.Prime p ∧ RealImbalancedReceiver b (N - p) := by
  classical
  simp [realGoodPrimes]

theorem realGoodPrimes_subset_realImbalancedPrimes (b : ℝ) (N : ℕ) :
    realGoodPrimes b N ⊆ realImbalancedPrimes b N := by
  intro p hp
  exact Finset.mem_of_mem_erase hp

/-- Membership already prevents subtraction from reaching zero or one,
without any assumption on the real exponent. -/
theorem receiver_two_le_of_mem_realImbalancedPrimes {b : ℝ} {N p : ℕ}
    (hp : p ∈ realImbalancedPrimes b N) : 2 ≤ N - p := by
  exact primeOrSemiprime_two_le
    (mem_realImbalancedPrimes.mp hp).2.2.primeOrSemiprime

theorem receiver_two_le_of_mem_realGoodPrimes {b : ℝ} {N p : ℕ}
    (hp : p ∈ realGoodPrimes b N) : 2 ≤ N - p := by
  exact receiver_two_le_of_mem_realImbalancedPrimes
    (realGoodPrimes_subset_realImbalancedPrimes b N hp)

/-- The upper endpoint is `N - 2`, including for small targets. -/
theorem prime_le_sub_two_of_mem_realImbalancedPrimes {b : ℝ} {N p : ℕ}
    (hp : p ∈ realImbalancedPrimes b N) : p ≤ N - 2 := by
  have hpN := (mem_realImbalancedPrimes.mp hp).1
  have hm := receiver_two_le_of_mem_realImbalancedPrimes hp
  omega

theorem prime_le_sub_two_of_mem_realGoodPrimes {b : ℝ} {N p : ℕ}
    (hp : p ∈ realGoodPrimes b N) : p ≤ N - 2 := by
  exact prime_le_sub_two_of_mem_realImbalancedPrimes
    (realGoodPrimes_subset_realImbalancedPrimes b N hp)

/-- The set cannot count either truncated boundary, even at small `N`. -/
theorem realGoodPrimes_boundary_excluded (b : ℝ) (N : ℕ) :
    N ∉ realGoodPrimes b N ∧ N - 1 ∉ realGoodPrimes b N := by
  constructor
  · intro hp
    have hpN := (mem_realGoodPrimes.mp hp).2.1
    omega
  · intro hp
    have hm := receiver_two_le_of_mem_realGoodPrimes hp
    omega

theorem receiver_odd_of_mem_realGoodPrimes {b : ℝ} {N p : ℕ}
    (hN : Even N) (hp : p ∈ realGoodPrimes b N) : Odd (N - p) := by
  obtain ⟨hp2, hpN, hpprime, _⟩ := mem_realGoodPrimes.mp hp
  exact receiver_odd_of_even_of_prime_ne_two hN hpprime hp2 hpN.le

theorem ordered_factors_odd_of_mem_realGoodPrimes {b : ℝ} {N p r q : ℕ}
    (hN : Even N) (hp : p ∈ realGoodPrimes b N)
    (hm : N - p = r * q) (_hrq : r ≤ q) : Odd r ∧ Odd q := by
  have hodd := receiver_odd_of_mem_realGoodPrimes hN hp
  rw [hm] at hodd
  exact Nat.odd_mul.mp hodd

/-- The unique possible excluded additive prime is exactly two. -/
theorem excluded_realImbalancedPrime_eq_two {b : ℝ} {N p : ℕ}
    (hp : p ∈ realImbalancedPrimes b N)
    (hgood : p ∉ realGoodPrimes b N) : p = 2 := by
  by_contra hp2
  exact hgood (Finset.mem_erase.mpr ⟨hp2, hp⟩)

/-- Exact count correction, with no parity or large-target hypothesis. -/
theorem RealDb_eq_realGoodPrimes_card_add_indicator (b : ℝ) (N : ℕ) :
    RealDb b N = (realGoodPrimes b N).card +
      (if 2 ∈ realImbalancedPrimes b N then 1 else 0) := by
  classical
  unfold RealDb realGoodPrimes
  by_cases htwo : 2 ∈ realImbalancedPrimes b N
  · simpa only [if_pos htwo] using (Finset.card_erase_add_one htwo).symm
  · simp [htwo]

/-- Natural subtraction loses precisely the membership indicator of two. -/
theorem RealDb_sub_realGoodPrimes_card_eq_indicator (b : ℝ) (N : ℕ) :
    RealDb b N - (realGoodPrimes b N).card =
      (if 2 ∈ realImbalancedPrimes b N then 1 else 0) := by
  classical
  have h := RealDb_eq_realGoodPrimes_card_add_indicator b N
  omega

theorem RealDb_sub_realGoodPrimes_card_le_one (b : ℝ) (N : ℕ) :
    RealDb b N - (realGoodPrimes b N).card ≤ 1 := by
  classical
  rw [RealDb_sub_realGoodPrimes_card_eq_indicator]
  split_ifs <;> omega

theorem RealDb_le_realGoodPrimes_card_add_one (b : ℝ) (N : ℕ) :
    RealDb b N ≤ (realGoodPrimes b N).card + 1 := by
  classical
  have h := RealDb_eq_realGoodPrimes_card_add_indicator b N
  split_ifs at h <;> omega

/-- The same correction in real numbers uses ordinary subtraction. -/
theorem RealDb_cast_sub_realGoodPrimes_card_eq_indicator (b : ℝ) (N : ℕ) :
    (RealDb b N : ℝ) - ((realGoodPrimes b N).card : ℝ) =
      (if 2 ∈ realImbalancedPrimes b N then (1 : ℝ) else 0) := by
  classical
  have h := RealDb_eq_realGoodPrimes_card_add_indicator b N
  by_cases htwo : 2 ∈ realImbalancedPrimes b N
  · simp only [if_pos htwo] at h ⊢
    have hR : (RealDb b N : ℝ) = ((realGoodPrimes b N).card : ℝ) + 1 := by
      exact_mod_cast h
    linarith
  · simp only [if_neg htwo, Nat.add_zero] at h
    simp [htwo, h]

end

end ImbalancedChen.P6
