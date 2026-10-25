import ImbalancedChen.P0RamanujanGeneralGcdIdentity
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Exact prime-power values and a gcd bound for the actual physical Ramanujan
sum. The Moebius divisor sum has exactly two potentially nonzero terms at
p^(k+1), namely the divisors 1 and p. No CRT or multiplicativity input is
used, and the frequency is an arbitrary signed integer.
-/

namespace ImbalancedChen.Part3.RamanujanPrimePowerValues20261025a

noncomputable section

open Finset
open scoped BigOperators
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode
open ImbalancedChen.Part3.RamanujanGeneralGcdIdentity20261025a

/-- Exact two-term evaluation before dividing into the three valuation
cases. It includes prime moduli when k=0. -/
theorem ramanujan_prime_pow_difference {p : ℕ} (hp : p.Prime)
    (k : ℕ) (n : ℤ) :
    ramanujan (p ^ (k + 1)) n =
      (if ((p ^ (k + 1) : ℕ) : ℤ) ∣ n then
        ((p ^ (k + 1) : ℕ) : ℂ) else 0) -
      (if ((p ^ k : ℕ) : ℤ) ∣ n then ((p ^ k : ℕ) : ℂ) else 0) := by
  classical
  letI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let F : ℕ → ℂ := fun j =>
    if ((p ^ (k + 1) / p ^ j : ℕ) : ℤ) ∣ n then
      (ArithmeticFunction.moebius (p ^ j) : ℂ) *
        ((p ^ (k + 1) / p ^ j : ℕ) : ℂ)
    else 0
  have hformula : ramanujan (p ^ (k + 1)) n =
      ∑ j ∈ range (k + 2), F j := by
    have h := ramanujan_eq_moebius_quotient_sum
      (c := p ^ (k + 1)) n
    rw [Nat.sum_divisors_prime_pow hp] at h
    simpa only [F, Nat.add_assoc] using h
  have hsubset : ({0, 1} : Finset ℕ) ⊆ range (k + 2) := by
    intro j hj
    simp only [mem_insert, mem_singleton] at hj
    rcases hj with rfl | rfl <;> simp only [mem_range] <;> omega
  have htail (j : ℕ) (_hj : j ∈ range (k + 2))
      (hnot : j ∉ ({0, 1} : Finset ℕ)) : F j = 0 := by
    have hj0 : j ≠ 0 := by intro hj; exact hnot (by simp [hj])
    have hj1 : j ≠ 1 := by intro hj; exact hnot (by simp [hj])
    have hmu : ArithmeticFunction.moebius (p ^ j) = 0 := by
      rw [ArithmeticFunction.moebius_apply_prime_pow hp hj0, if_neg hj1]
    simp only [F, hmu, Int.cast_zero, zero_mul, ite_self]
  have htwo : (∑ j ∈ range (k + 2), F j) = F 0 + F 1 := by
    calc
      _ = ∑ j ∈ ({0, 1} : Finset ℕ), F j :=
        (sum_subset hsubset htail).symm
      _ = _ := by simp
  have hquot : p ^ (k + 1) / p = p ^ k := by
    rw [pow_succ, Nat.mul_div_cancel (p ^ k) hp.pos]
  rw [hformula, htwo]
  simp only [F, pow_zero, pow_one, Nat.div_one,
    ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime hp, hquot,
    Int.cast_one, Int.cast_neg, one_mul, neg_one_mul]
  split_ifs <;> ring

/-- The three exact valuation cases: the full level divides the argument,
only the preceding power divides it, or neither power divides it. -/
theorem ramanujan_prime_pow_values {p : ℕ} (hp : p.Prime)
    (k : ℕ) (n : ℤ) :
    ramanujan (p ^ (k + 1)) n =
      if ((p ^ (k + 1) : ℕ) : ℤ) ∣ n then
        ((p ^ k : ℕ) : ℂ) * ((p : ℂ) - 1)
      else if ((p ^ k : ℕ) : ℤ) ∣ n then -((p ^ k : ℕ) : ℂ)
      else 0 := by
  rw [ramanujan_prime_pow_difference hp k n]
  have hstep : ((p ^ k : ℕ) : ℤ) ∣ ((p ^ (k + 1) : ℕ) : ℤ) := by
    refine ⟨(p : ℤ), ?_⟩
    simp only [pow_succ, Nat.cast_mul]
  by_cases hhigh : ((p ^ (k + 1) : ℕ) : ℤ) ∣ n
  · have hlow : ((p ^ k : ℕ) : ℤ) ∣ n := dvd_trans hstep hhigh
    simp only [if_pos hhigh, if_pos hlow, pow_succ, Nat.cast_mul]
    ring
  · by_cases hlow : ((p ^ k : ℕ) : ℤ) ∣ n <;>
      simp [hhigh, hlow]

/-- A quantitative gcd bound at every actual prime-power modulus. It is
proved from the exact values, including the possibly nonzero middle case. -/
theorem norm_ramanujan_prime_pow_le_gcd {p : ℕ} (hp : p.Prime)
    (k : ℕ) (n : ℤ) :
    ‖ramanujan (p ^ (k + 1)) n‖ ≤
      ((p ^ (k + 1)).gcd n.natAbs : ℝ) := by
  rw [ramanujan_prime_pow_values hp k n]
  have hmodpos : 0 < p ^ (k + 1) := pow_pos hp.pos _
  have hgpos : 0 < (p ^ (k + 1)).gcd n.natAbs :=
    Nat.gcd_pos_of_pos_left n.natAbs hmodpos
  have hstep : p ^ k ∣ p ^ (k + 1) := by
    rw [pow_succ]
    exact dvd_mul_right _ _
  by_cases hhigh : ((p ^ (k + 1) : ℕ) : ℤ) ∣ n
  · have hnat : p ^ (k + 1) ∣ n.natAbs :=
      Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hhigh)
    rw [if_pos hhigh, Nat.gcd_eq_left hnat]
    have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
    have hnonneg : 0 ≤ ((p ^ k : ℕ) : ℝ) * ((p : ℝ) - 1) :=
      mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hpR)
    have hreal : ((p ^ k : ℕ) : ℂ) * ((p : ℂ) - 1) =
        ((((p ^ k : ℕ) : ℝ) * ((p : ℝ) - 1) : ℝ) : ℂ) := by
      push_cast <;> rfl
    rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    simp only [pow_succ, Nat.cast_mul]
    nlinarith [show 0 ≤ ((p ^ k : ℕ) : ℝ) by positivity]
  · rw [if_neg hhigh]
    by_cases hlow : ((p ^ k : ℕ) : ℤ) ∣ n
    · rw [if_pos hlow, norm_neg]
      have hnat : p ^ k ∣ n.natAbs :=
        Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hlow)
      have hle : p ^ k ≤ (p ^ (k + 1)).gcd n.natAbs :=
        Nat.le_of_dvd hgpos (Nat.dvd_gcd hstep hnat)
      have hnorm : ‖((p ^ k : ℕ) : ℂ)‖ = ((p ^ k : ℕ) : ℝ) := by
        simp
      rw [hnorm]
      exact_mod_cast hle
    · simp only [if_neg hlow, norm_zero]
      exact Nat.cast_nonneg _

end
end ImbalancedChen.Part3.RamanujanPrimePowerValues20261025a