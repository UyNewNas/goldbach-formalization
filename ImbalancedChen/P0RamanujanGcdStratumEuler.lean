import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

An exact finite gcd-stratum supplier for the general Ramanujan-sum route.
The residues 0 <= a < c are partitioned by gcd(c,a). The size of the
stratum d is Euler phi(c/d). This module aggregates those fibers for an
arbitrary additive weight and proves the cumulative Euler identity over
divisors that are multiples of a prescribed d. The modulus-zero case is
included: its residue range and its divisor finset are both empty.

This is the finite gcd/divisor-count primitive, not a claimed formula for
the actual complex Ramanujan sum. The remaining character-sum/Mobius
reduction is not a hypothesis or a conclusion of this module.
-/

namespace ImbalancedChen.Part3.RamanujanGcdStratumEuler20261025a

open Finset
open scoped BigOperators

/-- Every additive function of the residue gcd has the exact Euler-weighted
finite divisor distribution. There is no coprimality or CRT premise. -/
theorem sum_gcd_strata {A : Type*} [AddCommMonoid A]
    (c : ℕ) (F : ℕ → A) :
    (∑ a ∈ range c, F (c.gcd a)) =
      ∑ d ∈ c.divisors, (c / d).totient • F d := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  have hmap : ∀ a ∈ range c, c.gcd a ∈ c.divisors := by
    intro a _ha
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left c a, hc⟩
  calc
    (∑ a ∈ range c, F (c.gcd a)) =
        ∑ d ∈ c.divisors, ∑ a ∈ range c with c.gcd a = d, F d :=
      (sum_fiberwise_of_maps_to' hmap F).symm
    _ = ∑ d ∈ c.divisors, (c / d).totient • F d := by
      apply sum_congr rfl
      intro d hd
      rw [sum_const, ← Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]

/-- A predicate on the gcd may select any collection of strata. Its exact
residue count is the sum of the corresponding Euler masses. -/
theorem card_gcd_strata (c : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    #{a ∈ range c | P (c.gcd a)} =
      ∑ d ∈ c.divisors with P d, (c / d).totient := by
  classical
  have h := sum_gcd_strata c (fun d => if P d then (1 : ℕ) else 0)
  simpa only [card_eq_sum_ones, sum_filter, nsmul_eq_mul,
    mul_ite, mul_one, mul_zero] using h

/-- The prescribed-divisor cumulative gcd count. This includes divisors d
that do not divide c; in that case both sides count no residue. -/
theorem card_divides_gcd (c d : ℕ) :
    #{a ∈ range c | d ∣ c.gcd a} =
      ∑ e ∈ c.divisors with d ∣ e, (c / e).totient :=
  card_gcd_strata c (fun e => d ∣ e)

/-- Exact number of multiples of d in the half-open complete residue range,
when d divides the modulus. Zero and modulus one are included. -/
theorem card_residue_multiples {c d : ℕ} (hdc : d ∣ c) :
    #{a ∈ range c | d ∣ a} = c / d := by
  classical
  by_cases hd : d = 0
  · subst d
    have hc : c = 0 := Nat.eq_zero_of_zero_dvd hdc
    simp [hc]
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  obtain ⟨m, rfl⟩ := hdc
  rw [Nat.mul_div_cancel_left m hdpos]
  symm
  rw [← card_range m]
  apply card_bij (fun a _ha => d * a)
  · intro a ha
    apply mem_filter.mpr
    exact ⟨mem_range.mpr ((Nat.mul_lt_mul_left hdpos).2 (mem_range.mp ha)),
      dvd_mul_right d a⟩
  · intro a _ha b _hb hab
    exact Nat.mul_left_cancel hdpos hab
  · intro b hb
    obtain ⟨hbRange, hbDiv⟩ := mem_filter.mp hb
    obtain ⟨a, rfl⟩ := hbDiv
    exact ⟨a, mem_range.mpr ((Nat.mul_lt_mul_left hdpos).1
      (mem_range.mp hbRange)), rfl⟩

/-- The cumulative Euler divisor identity needed by a gcd partition:
all strata whose gcd is a multiple of d have total mass c/d. -/
theorem sum_totient_multiple_divisors {c d : ℕ} (hdc : d ∣ c) :
    (∑ e ∈ c.divisors with d ∣ e, (c / e).totient) = c / d := by
  classical
  have hfilter :
      (range c).filter (fun a => d ∣ c.gcd a) =
        (range c).filter (fun a => d ∣ a) := by
    ext a
    simp only [mem_filter, Nat.dvd_gcd_iff, hdc, true_and]
  have h := card_divides_gcd c d
  rw [hfilter, card_residue_multiples hdc] at h
  exact h.symm

/-- The first gcd moment is consequently an exact divisor/Euler sum,
without any estimate or unknown arithmetic input. -/
theorem sum_residue_gcd (c : ℕ) :
    (∑ a ∈ range c, c.gcd a) =
      ∑ d ∈ c.divisors, (c / d).totient * d := by
  simpa only [nsmul_eq_mul] using sum_gcd_strata c (fun d : ℕ => d)

end ImbalancedChen.Part3.RamanujanGcdStratumEuler20261025a