import ImbalancedChen.P5OriginalOneLongDivisorIntervals
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Cast.Field

-- UNCOMPILED_ZERO_CREDIT. Original primitive (3)/(E1), no roughness premise.
-- This closes the exact PrimitiveCoprimeDensity boundary of OneLong Phase2
-- by finite Mobius inversion and the actual half-open-interval endpoint count.

namespace ImbalancedChen
namespace OriginalPrimitiveCoprimeDensity

noncomputable section
open scoped BigOperators
open Finset
open OriginalOneLongDivisorIntervals

def muR (d : ℕ) : ℝ := (ArithmeticFunction.moebius d : ℤ)

theorem muR_abs_le_one (d : ℕ) : |muR d| ≤ 1 := by
  unfold muR
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))

theorem sum_muR_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, muR d) = if n = 1 then 1 else 0 := by
  have hZ : (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
      (if n = 1 then (1 : ℤ) else 0) := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply,
      ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  unfold muR
  exact_mod_cast hZ

theorem coprime_indicator_moebius (q n : ℕ) (hq : 0 < q) :
    (if q.Coprime n then (1 : ℝ) else 0) =
      ∑ d ∈ q.divisors, if d ∣ n then muR d else 0 := by
  have hg : n.gcd q ≠ 0 := Nat.gcd_ne_zero_right hq.ne'
  have hfilter : q.divisors.filter (fun d => d ∣ n) = (n.gcd q).divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdq, _⟩, hdn⟩
      exact ⟨Nat.dvd_gcd hdn hdq, hg⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨hd.trans (Nat.gcd_dvd_right n q), hq.ne'⟩,
        hd.trans (Nat.gcd_dvd_left n q)⟩
  rw [← Finset.sum_filter, hfilter, sum_muR_divisors]
  simp only [Nat.coprime_comm, Nat.Coprime]

def multiples (A B d : ℕ) : ℕ := ((Ico A B).filter (fun n => d ∣ n)).card

theorem multiples_quotient (A B d : ℕ) (hd : 0 < d) :
    multiples A B d = lowerQuotient B d - lowerQuotient A d := by
  have h := sum_divisible_interval (R := ℕ) A B d hd (fun _ => 1)
  simpa [multiples] using h

-- Both endpoint errors are retained. The stronger constant one is enough;
-- the manuscript's safely closed constant two is supplied below.
theorem quotient_length_abs_error (A B d : ℕ) (hAB : A ≤ B) (hd : 0 < d) :
    |((lowerQuotient B d - lowerQuotient A d : ℕ) : ℝ) -
      ((B - A : ℕ) : ℝ) / (d : ℝ)| ≤ 1 := by
  have hm := quotient_mono A B d hd hAB
  have hAlo : (A : ℝ) ≤ (d : ℝ) * (lowerQuotient A d : ℝ) := by
    exact_mod_cast (le_smul_ceilDiv (β := ℕ) hd : A ≤ d * (A ⌈/⌉ d))
  have hBlo : (B : ℝ) ≤ (d : ℝ) * (lowerQuotient B d : ℝ) := by
    exact_mod_cast (le_smul_ceilDiv (β := ℕ) hd : B ≤ d * (B ⌈/⌉ d))
  have hAhi : (d : ℝ) * (lowerQuotient A d : ℝ) ≤ (A : ℝ) + d := by
    exact_mod_cast ceil_product_le A d hd
  have hBhi : (d : ℝ) * (lowerQuotient B d : ℝ) ≤ (B : ℝ) + d := by
    exact_mod_cast ceil_product_le B d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Nat.cast_sub hm, Nat.cast_sub hAB, abs_le]
  constructor
  · have h : ((B : ℝ) - A) / (d : ℝ) ≤
        (lowerQuotient B d : ℝ) - lowerQuotient A d + 1 :=
      (div_le_iff₀ hdR).2 (by nlinarith)
    linarith
  · have h : (lowerQuotient B d : ℝ) - lowerQuotient A d ≤
        ((B : ℝ) - A + d) / (d : ℝ) :=
      (le_div_iff₀ hdR).2 (by nlinarith)
    rw [add_div, div_self hdR.ne'] at h
    linarith

theorem multiples_abs_error (A B d : ℕ) (hAB : A ≤ B) (hd : 0 < d) :
    |(multiples A B d : ℝ) - ((B - A : ℕ) : ℝ) / (d : ℝ)| ≤ 1 := by
  rw [multiples_quotient A B d hd]
  exact quotient_length_abs_error A B d hAB hd

theorem coprime_count_moebius (A B q : ℕ) (hq : 0 < q) :
    (part3IntervalCoprimeCount A B q : ℝ) =
      ∑ d ∈ q.divisors, muR d * (multiples A B d : ℝ) := by
  classical
  calc
    _ = ∑ n ∈ Ico A B, if q.Coprime n then (1 : ℝ) else 0 := by
      simp [part3IntervalCoprimeCount]
    _ = ∑ n ∈ Ico A B, ∑ d ∈ q.divisors, if d ∣ n then muR d else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact coprime_indicator_moebius q n hq
    _ = ∑ d ∈ q.divisors, ∑ n ∈ Ico A B, if d ∣ n then muR d else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      calc
        _ = muR d * ∑ n ∈ Ico A B, if d ∣ n then (1 : ℝ) else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n hn
          split_ifs <;> ring
        _ = _ := by simp [multiples]

theorem multiples_period (q d : ℕ) (hd : 0 < d) (hdq : d ∣ q) :
    multiples 0 q d = q / d := by
  rw [multiples_quotient 0 q d hd]
  have hq : lowerQuotient q d = q / d := by
    conv_lhs => rw [← Nat.mul_div_cancel' hdq]
    simp [lowerQuotient, smul_ceilDiv hd]
  simp [hq, lowerQuotient]

-- Totient normalization is derived from the SAME complete-period source count.
-- No independent Euler approximation or changed mean is inserted.
theorem reciprocal_moebius_totient (q : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, muR d / (d : ℝ)) = (q.totient : ℝ) / (q : ℝ) := by
  have hperiod := coprime_count_moebius 0 q q hq
  have hcount : part3IntervalCoprimeCount 0 q q = q.totient := by
    simp [part3IntervalCoprimeCount, Nat.totient]
  rw [hcount] at hperiod
  have hmain : (q.totient : ℝ) = (q : ℝ) * ∑ d ∈ q.divisors, muR d / (d : ℝ) := by
    rw [hperiod, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [multiples_period q d (Nat.pos_of_mem_divisors hd) (Nat.dvd_of_mem_divisors hd),
      Nat.cast_div_charZero (Nat.dvd_of_mem_divisors hd)]
    ring
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [hmain]
  field_simp

theorem primitive_coprime_density_error (A B q : ℕ) (hAB : A ≤ B) (hq : 0 < q) :
    |(part3IntervalCoprimeCount A B q : ℝ) -
      ((B - A : ℕ) : ℝ) * (q.totient : ℝ) / (q : ℝ)| ≤ (q.divisors.card : ℝ) := by
  have hmain : ((B - A : ℕ) : ℝ) * (q.totient : ℝ) / (q : ℝ) =
      ∑ d ∈ q.divisors, muR d * (((B - A : ℕ) : ℝ) / (d : ℝ)) := by
    calc
      _ = ((B - A : ℕ) : ℝ) * ((q.totient : ℝ) / (q : ℝ)) := by ring
      _ = ((B - A : ℕ) : ℝ) * ∑ d ∈ q.divisors, muR d / (d : ℝ) := by
        rw [reciprocal_moebius_totient q hq]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        ring
  rw [coprime_count_moebius A B q hq, hmain, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ q.divisors, |muR d * (multiples A B d : ℝ) -
        muR d * (((B - A : ℕ) : ℝ) / (d : ℝ))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ q.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [← mul_sub, abs_mul]
      exact (mul_le_mul (muR_abs_le_one d)
        (multiples_abs_error A B d hAB (Nat.pos_of_mem_divisors hd))
        (abs_nonneg _) (by norm_num)).trans (by norm_num)
    _ = (q.divisors.card : ℝ) := by simp

-- Direct supplier for the Phase2 interface, with the stated safe factor two.
theorem primitiveCoprimeDensity_two_tau (q : ℕ) (hq : 0 < q) :
    PrimitiveCoprimeDensity q (2 * (q.divisors.card : ℝ)) := by
  intro A B hAB
  exact (primitive_coprime_density_error A B q hAB hq).trans
    (by nlinarith [Nat.cast_nonneg q.divisors.card])

end
end OriginalPrimitiveCoprimeDensity
end ImbalancedChen
