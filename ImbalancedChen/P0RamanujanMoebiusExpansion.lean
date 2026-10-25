import ImbalancedChen.Part3RamanujanSpecialCase
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The coprime indicator is expanded into the actual integer Moebius function
on common divisors. Finite distributivity then gives a divisor expansion of
an arbitrary coprime-gated residue sum, and hence of the literal physical
Ramanujan sum. The selected residues are reindexed by their exact multiples.
No CRT, cancellation estimate, or final Ramanujan evaluation is assumed.
-/

namespace ImbalancedChen.Part3.RamanujanMoebiusExpansion20261025a

noncomputable section

open Finset
open scoped BigOperators
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode

/-- The common divisors are exactly the divisors of the gcd. The positive
modulus guard avoids the intentionally empty divisor finset of zero. -/
theorem gcd_divisors_eq_filter (c a : ℕ) (hc : c ≠ 0) :
    (c.gcd a).divisors = c.divisors.filter (fun d => d ∣ a) := by
  have hg : c.gcd a ≠ 0 :=
    (Nat.gcd_pos_of_pos_left a (Nat.pos_of_ne_zero hc)).ne'
  ext d
  simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff, hc, hg,
    and_true]

/-- Exact integer coprime indicator, with no assumed arithmetic supplier. -/
theorem coprime_indicator_moebius (c a : ℕ) (hc : c ≠ 0) :
    (if c.Coprime a then (1 : ℤ) else 0) =
      ∑ d ∈ c.divisors with d ∣ a, ArithmeticFunction.moebius d := by
  have hsum :
      (∑ d ∈ (c.gcd a).divisors, ArithmeticFunction.moebius d) =
        if c.gcd a = 1 then (1 : ℤ) else 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℤ => f (c.gcd a))
      ArithmeticFunction.moebius_mul_coe_zeta
    simpa only [ArithmeticFunction.coe_mul_zeta_apply,
      ArithmeticFunction.one_apply] using h
  rw [gcd_divisors_eq_filter c a hc] at hsum
  simpa only [Nat.coprime_iff_gcd_eq_one] using hsum.symm

/-- The same indicator in the complex coefficient field of the physical
finite Fourier sums. This is a cast of the integer divisor identity. -/
theorem coprime_indicator_moebius_complex (c a : ℕ) (hc : c ≠ 0) :
    (if c.Coprime a then (1 : ℂ) else 0) =
      ∑ d ∈ c.divisors with d ∣ a, (ArithmeticFunction.moebius d : ℂ) := by
  exact_mod_cast coprime_indicator_moebius c a hc

/-- A genuinely arbitrary residue weight may be carried through the exact
Moebius expansion. The inner sum remains over the original residue range. -/
theorem coprime_weighted_sum_moebius (c : ℕ) (hc : c ≠ 0)
    (f : ℕ → ℂ) :
    (∑ a ∈ range c, if a.Coprime c then f a else 0) =
      ∑ d ∈ c.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ∑ a ∈ range c with d ∣ a, f a := by
  classical
  have hpoint (a : ℕ) :
      (if a.Coprime c then f a else 0) =
        ∑ d ∈ c.divisors,
          if d ∣ a then (ArithmeticFunction.moebius d : ℂ) * f a else 0 := by
    calc
      (if a.Coprime c then f a else 0) =
          (if c.Coprime a then (1 : ℂ) else 0) * f a := by
        rw [Nat.coprime_comm a c]
        split_ifs <;> simp
      _ = (∑ d ∈ c.divisors with d ∣ a,
            (ArithmeticFunction.moebius d : ℂ)) * f a := by
        rw [coprime_indicator_moebius_complex c a hc]
      _ = _ := by simp only [sum_filter, sum_mul, ite_mul, zero_mul]
  simp_rw [hpoint]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _hd
  simp only [sum_filter, mul_sum, mul_ite, mul_zero]

/-- Exact reindexing of a divisor-selected residue sum by multiplication.
This is a finite bijection, not a density or asymptotic assertion. -/
theorem sum_residue_multiples {c d : ℕ} (hc : c ≠ 0) (hdc : d ∣ c)
    (f : ℕ → ℂ) :
    (∑ a ∈ range c with d ∣ a, f a) =
      ∑ k ∈ range (c / d), f (d * k) := by
  classical
  have hd : d ≠ 0 := by
    intro hd
    subst d
    exact hc (Nat.eq_zero_of_zero_dvd hdc)
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  obtain ⟨m, rfl⟩ := hdc
  rw [Nat.mul_div_cancel_left m hdpos]
  symm
  apply sum_bij (fun k _hk => d * k)
  · intro k hk
    exact mem_filter.mpr
      ⟨mem_range.mpr ((Nat.mul_lt_mul_left hdpos).2 (mem_range.mp hk)),
        dvd_mul_right d k⟩
  · intro k _hk l _hl hkl
    exact Nat.mul_left_cancel hdpos hkl
  · intro a ha
    obtain ⟨haRange, haDiv⟩ := mem_filter.mp ha
    obtain ⟨k, rfl⟩ := haDiv
    exact ⟨k, mem_range.mpr ((Nat.mul_lt_mul_left hdpos).1
      (mem_range.mp haRange)), rfl⟩
  · intro k _hk
    rfl

/-- The actual positive-frequency Ramanujan sum has the literal Moebius
expansion over divisor-selected complete residues. -/
theorem ramanujan_moebius_divisor_filter {c : ℕ} [NeZero c] (n : ℤ) :
    ramanujan c n =
      ∑ d ∈ c.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ∑ a ∈ range c with d ∣ a,
          AddCircle.fourier 1
            ((((n * (a : ℤ) : ℤ) : ℝ) / (c : ℝ)) : UnitAddCircle) := by
  rw [ramanujan, kloosterman]
  simp only [zero_mul, add_zero]
  exact coprime_weighted_sum_moebius c (NeZero.ne c) _

/-- All inner ranges are now the exact shorter complete ranges c/d.
The remaining additive-character evaluation has not been assumed. -/
theorem ramanujan_moebius_divisor_multiples {c : ℕ} [NeZero c] (n : ℤ) :
    ramanujan c n =
      ∑ d ∈ c.divisors, (ArithmeticFunction.moebius d : ℂ) *
        ∑ k ∈ range (c / d),
          AddCircle.fourier 1
            ((((n * ((d * k : ℕ) : ℤ) : ℤ) : ℝ) / (c : ℝ)) : UnitAddCircle) := by
  rw [ramanujan_moebius_divisor_filter]
  apply sum_congr rfl
  intro d hd
  rw [sum_residue_multiples (NeZero.ne c) (Nat.dvd_of_mem_divisors hd)]

end
end ImbalancedChen.Part3.RamanujanMoebiusExpansion20261025a