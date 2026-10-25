import ImbalancedChen.P0RamanujanMoebiusExpansion
import ImbalancedChen.Part3CenteredFourier
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The shorter complete additive-character sums in the literal Ramanujan
Moebius expansion are evaluated by the existing full-modulus additive
orthogonality theorem. Divisor complementation then gives the exact
formula sum_{d | gcd(c, |n|)} d * mu(c/d) for the actual physical sum.
This uses no CRT and supplies no unknown analytic or arithmetic premise.
-/

namespace ImbalancedChen.Part3.RamanujanGeneralGcdIdentity20261025a

noncomputable section

open Finset
open scoped BigOperators
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode
open ImbalancedChen.Part3.RamanujanMoebiusExpansion20261025a

private theorem stdAddChar_int_fourier {q : ℕ} [NeZero q] (b : ℤ) :
    ZMod.stdAddChar (b : ZMod q) =
      AddCircle.fourier 1 (((b : ℝ) / (q : ℝ)) : UnitAddCircle) := by
  rw [ZMod.stdAddChar_coe, AddCircle.fourier_coe_apply]
  push_cast
  congr 1
  ring

private theorem sum_zmod_eq_range {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ u : ZMod q, f u) = ∑ k ∈ range q, f (k : ZMod q) := by
  apply sum_bij (fun u _hu => u.val)
  · intro u _hu
    exact mem_range.mpr u.val_lt
  · intro u _hu v _hv huv
    have h := congrArg (fun k : ℕ => (k : ZMod q)) huv
    simpa only [ZMod.natCast_zmod_val] using h
  · intro k hk
    exact ⟨(k : ZMod q), mem_univ _, ZMod.val_natCast_of_lt (mem_range.mp hk)⟩
  · intro u _hu
    simp only [ZMod.natCast_zmod_val]

/-- The full complete additive-character sum, with a signed integer
frequency and the same period-one Fourier convention as the physical sum. -/
theorem complete_fourier_sum {q : ℕ} [NeZero q] (n : ℤ) :
    (∑ k ∈ range q,
      AddCircle.fourier 1
        ((((n * (k : ℤ) : ℤ) : ℝ) / (q : ℝ)) : UnitAddCircle)) =
      if (q : ℤ) ∣ n then (q : ℂ) else 0 := by
  classical
  calc
    _ = ∑ k ∈ range q,
        ZMod.stdAddChar ((n : ZMod q) * (k : ZMod q)) := by
      apply sum_congr rfl
      intro k _hk
      simpa only [Int.cast_mul, Int.cast_natCast] using
        (stdAddChar_int_fourier (q := q) (n * (k : ℤ))).symm
    _ = ∑ u : ZMod q, ZMod.stdAddChar ((n : ZMod q) * u) :=
      (sum_zmod_eq_range _).symm
    _ = if (n : ZMod q) = 0 then (q : ℂ) else 0 := by
      simpa only [mul_comm] using
        ImbalancedChen.Part3.sum_stdAddChar_mul_eq q (n : ZMod q)
    _ = _ := by rw [ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The exact divisor-selected Fourier sum is a shorter complete sum.
The lower modulus c/d is proved positive, rather than assumed as a field. -/
theorem divisor_multiple_character_sum {c d : ℕ}
    (hc : c ≠ 0) (hdc : d ∣ c) (n : ℤ) :
    (∑ k ∈ range (c / d),
      AddCircle.fourier 1
        ((((n * ((d * k : ℕ) : ℤ) : ℤ) : ℝ) / (c : ℝ)) : UnitAddCircle)) =
      if ((c / d : ℕ) : ℤ) ∣ n then ((c / d : ℕ) : ℂ) else 0 := by
  classical
  have hd : d ≠ 0 := by
    intro hd
    subst d
    exact hc (Nat.eq_zero_of_zero_dvd hdc)
  have hq : c / d ≠ 0 := by
    intro hq
    have hmul : d * (c / d) = c := Nat.mul_div_cancel' hdc
    rw [hq, mul_zero] at hmul
    exact hc hmul.symm
  letI : NeZero (c / d) := ⟨hq⟩
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hqR : ((c / d : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hmulR : (c : ℝ) = (d : ℝ) * ((c / d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdc).symm
  have hratio (k : ℕ) :
      (((n * ((d * k : ℕ) : ℤ) : ℤ) : ℝ) / (c : ℝ)) =
        (((n * (k : ℤ) : ℤ) : ℝ) / ((c / d : ℕ) : ℝ)) := by
    rw [hmulR]
    push_cast
    field_simp [hdR, hqR] <;> ring
  calc
    _ = ∑ k ∈ range (c / d),
        AddCircle.fourier 1
          ((((n * (k : ℤ) : ℤ) : ℝ) / ((c / d : ℕ) : ℝ)) : UnitAddCircle) := by
      apply sum_congr rfl
      intro k _hk
      exact congrArg (fun x : ℝ => AddCircle.fourier 1 (x : UnitAddCircle)) (hratio k)
    _ = _ := complete_fourier_sum n

/-- An exact evaluated divisor formula for the actual physical Ramanujan
sum. The only condition in each summand is ordinary integer divisibility. -/
theorem ramanujan_eq_moebius_quotient_sum {c : ℕ} [NeZero c] (n : ℤ) :
    ramanujan c n =
      ∑ d ∈ c.divisors,
        if ((c / d : ℕ) : ℤ) ∣ n then
          (ArithmeticFunction.moebius d : ℂ) * ((c / d : ℕ) : ℂ)
        else 0 := by
  rw [ramanujan_moebius_divisor_multiples]
  apply sum_congr rfl
  intro d hd
  rw [divisor_multiple_character_sum (NeZero.ne c) (Nat.dvd_of_mem_divisors hd)]
  simp only [mul_ite, mul_zero]

/-- Divisor complementation puts the formula in the usual d*mu(c/d)
order, still without suppressing any common-divisor condition. -/
theorem ramanujan_eq_moebius_divisor_sum {c : ℕ} [NeZero c] (n : ℤ) :
    ramanujan c n =
      ∑ d ∈ c.divisors,
        if (d : ℤ) ∣ n then (ArithmeticFunction.moebius (c / d) : ℂ) * (d : ℂ)
        else 0 := by
  let F : ℕ → ℂ := fun d =>
    if (d : ℤ) ∣ n then (ArithmeticFunction.moebius (c / d) : ℂ) * (d : ℂ)
    else 0
  calc
    ramanujan c n =
        ∑ d ∈ c.divisors,
          if ((c / d : ℕ) : ℤ) ∣ n then
            (ArithmeticFunction.moebius d : ℂ) * ((c / d : ℕ) : ℂ)
          else 0 := ramanujan_eq_moebius_quotient_sum n
    _ = ∑ d ∈ c.divisors, F (c / d) := by
      apply sum_congr rfl
      intro d hd
      dsimp only [F]
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) (NeZero.ne c)]
    _ = ∑ d ∈ c.divisors, F d := Nat.sum_div_divisors c F
    _ = _ := rfl

/-- General exact Ramanujan gcd/Moebius identity for every positive modulus
and every signed integer additive argument, including n=0 and c=1. -/
theorem ramanujan_eq_gcd_moebius {c : ℕ} [NeZero c] (n : ℤ) :
    ramanujan c n =
      ∑ d ∈ (c.gcd n.natAbs).divisors,
        (d : ℂ) * (ArithmeticFunction.moebius (c / d) : ℂ) := by
  classical
  have hdiv (d : ℕ) : d ∣ n.natAbs ↔ (d : ℤ) ∣ n := by
    rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
  have hfilter :
      (c.gcd n.natAbs).divisors =
        c.divisors.filter (fun d => (d : ℤ) ∣ n) := by
    simpa only [hdiv] using gcd_divisors_eq_filter c n.natAbs (NeZero.ne c)
  rw [ramanujan_eq_moebius_divisor_sum, ← sum_filter, ← hfilter]
  apply sum_congr rfl
  intro d _hd
  exact mul_comm _ _

end
end ImbalancedChen.Part3.RamanujanGeneralGcdIdentity20261025a