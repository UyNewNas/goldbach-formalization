import ImbalancedChen.Part3ActualRamanujanLevelZetaFactors

/-! Independent arithmetic beneath the Fricke coefficient assembly.
Multiplication of the actual signed frequency by p raises its valuation
and gives a division-free recurrence of the actual local Ramanujan sums.
It identifies the prime-divisible and prime-free local correction factors.
No held Fourier-coefficient module is imported.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Finset Complex
open scoped BigOperators
open ImbalancedChen.Part3.ActualLevelDirichletFactors
open ImbalancedChen.Part3.ActualRamanujanLevelZetaFactors

namespace ImbalancedChen.Part3.RamanujanPrimeFrequencyRecurrence20261026b

private theorem geometric_prefix_shift (q : ℂ) (m : ℕ) :
    (∑ j ∈ range (m + 1 + 1), q ^ j) =
      1 + q * ∑ j ∈ range (m + 1), q ^ j := by
  rw [Finset.sum_range_succ']
  simp only [pow_zero, pow_succ']
  rw [← Finset.mul_sum]
  ring

theorem prime_frequency_valuation {p : ℕ} (hp : p.Prime)
    {n : ℤ} (hn : n ≠ 0) :
    padicValNat p (((p : ℤ) * n).natAbs) = padicValNat p n.natAbs + 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [Int.natAbs_mul, Int.natAbs_natCast,
    padicValNat.mul hp.ne_zero (Int.natAbs_ne_zero.mpr hn), padicValNat_self]
  omega

/-- A genuine recurrence in the actual signed frequency, valid for every
complex X: all nonzero-frequency local sums have finite support. -/
theorem full_localTail_prime_frequency {p : ℕ} (hp : p.Prime)
    {n : ℤ} (hn : n ≠ 0) (X : ℂ) :
    localTail p ((p : ℤ) * n) 0 X =
      (1 - X) + (p : ℂ) * X * localTail p n 0 X := by
  have hpn : (p : ℤ) * n ≠ 0 := mul_ne_zero (by exact_mod_cast hp.ne_zero) hn
  rw [full_localTail_nonzero_factor hp hpn X,
    full_localTail_nonzero_factor hp hn X, prime_frequency_valuation hp hn,
    geometric_prefix_shift]
  ring

private theorem tail_one_eq_full_sub_one {p : ℕ} (hp : p.Prime)
    {n : ℤ} (hn : n ≠ 0) (X : ℂ) :
    localTail p n 1 X = localTail p n 0 X - 1 := by
  rw [localTail_nonzero_eq_polynomial hp hn 1 X,
    localTail_nonzero_eq_polynomial hp hn 0 X]
  simp [nonzeroLocalPolynomial] <;> ring

/-- The prime-restricted channel has a division-free connection to the
full local factors at frequency n and p*n. -/
theorem restricted_localTail_prime_frequency {p : ℕ} (hp : p.Prime)
    {n : ℤ} (hn : n ≠ 0) (X : ℂ) :
    (1 - X) * localTail p ((p : ℤ) * n) 1 X =
      X * ((p : ℂ) * localTail p n 0 X - localTail p ((p : ℤ) * n) 0 X) := by
  have hpn : (p : ℤ) * n ≠ 0 := mul_ne_zero (by exact_mod_cast hp.ne_zero) hn
  rw [tail_one_eq_full_sub_one hp hpn X, full_localTail_prime_frequency hp hn X]
  ring

theorem prime_free_localTail {p : ℕ} (hp : p.Prime)
    {n : ℤ} (hn : n ≠ 0) (hpn : ¬(p : ℤ) ∣ n) (X : ℂ) :
    localTail p n 0 X = 1 - X ∧ localTail p n 1 X = -X := by
  have hd : ¬p ∣ n.natAbs := by
    intro h
    exact hpn (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h))
  have hv : padicValNat p n.natAbs = 0 := padicValNat.eq_zero_of_not_dvd hd
  have hf : localTail p n 0 X = 1 - X := by
    rw [full_localTail_nonzero_factor hp hn X, hv]
    simp
  refine ⟨hf, ?_⟩
  rw [tail_one_eq_full_sub_one hp hn X, hf]
  ring

/-- A local Euler correction with both frequency branches explicit.
No quotient frequency is invented when p does not divide n. -/
theorem localCorrection_frequency_split {p : ℕ} (hp : p.Prime)
    {n : ℤ} (hn : n ≠ 0) (X : ℂ) (hX : X ≠ 1) :
    localTail p n 1 X / localTail p n 0 X =
      if hpn : (p : ℤ) ∣ n then
        X * ((p : ℂ) * localTail p (n / (p : ℤ)) 0 X - localTail p n 0 X) /
          ((1 - X) * localTail p n 0 X)
      else -X / (1 - X) := by
  classical
  by_cases hd : (p : ℤ) ∣ n
  · rw [dif_pos hd]
    have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hm : (p : ℤ) * (n / (p : ℤ)) = n := Int.mul_ediv_cancel' hd
    have hq : n / (p : ℤ) ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hm
      exact hn hm.symm
    have h := restricted_localTail_prime_frequency hp hq X
    rw [hm] at h
    have hden : 1 - X ≠ 0 := sub_ne_zero.mpr hX.symm
    rw [← h, mul_div_mul_left _ _ hden]
  · rw [dif_neg hd]
    obtain ⟨hf, ht⟩ := prime_free_localTail hp hn hd X
    rw [hf, ht]

end ImbalancedChen.Part3.RamanujanPrimeFrequencyRecurrence20261026b
