import ImbalancedChen.Part3LongSlotDistribution
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

-- UNCOMPILED_ZERO_CREDIT. Frozen Phase 2 source, no formal checker run.
-- Original sections 7--8/(E1),(E5), and root derivation sections 2--3/(3)--(6).
-- This module supplies actual arithmetic inserted-divisor interval estimates.
-- It does not assume a rough-long distribution theorem.

namespace ImbalancedChen
namespace OriginalOneLongDivisorIntervals

noncomputable section
open scoped BigOperators
open Finset

def lowerQuotient (L d : ℕ) : ℕ := L ⌈/⌉ d

-- The interval is half-open at both scales. No real-boundary deletion occurs.
theorem mem_quotient_interval (L U d v : ℕ) (hd : 0 < d) :
    v ∈ Ico (lowerQuotient L d) (lowerQuotient U d) ↔
      d * v ∈ Ico L U := by
  simp only [mem_Ico, lowerQuotient]
  constructor
  · intro hv
    refine ⟨(ceilDiv_le_iff_le_mul hd).1 hv.1, ?_⟩
    by_contra h
    have h' : U ⌈/⌉ d ≤ v := (ceilDiv_le_iff_le_mul hd).2 (by omega)
    omega
  · intro hv
    refine ⟨(ceilDiv_le_iff_le_mul hd).2 hv.1, ?_⟩
    by_contra h
    have h' : U ≤ d * v := (ceilDiv_le_iff_le_mul hd).1 (by omega)
    omega

-- Literal divisor reindexing; no small divisor is frozen into a common scale.
theorem sum_divisible_interval {R : Type*} [AddCommMonoid R]
    (L U d : ℕ) (hd : 0 < d) (f : ℕ → R) :
    (∑ n ∈ (Ico L U).filter (fun n => d ∣ n), f n) =
      ∑ v ∈ Ico (lowerQuotient L d) (lowerQuotient U d), f (d * v) := by
  classical
  refine Finset.sum_bij (fun n _ => n / d) ?_ ?_ ?_ ?_
  · intro n hn
    apply (mem_quotient_interval L U d (n / d) hd).2
    rw [Nat.mul_div_cancel' (mem_filter.mp hn).2]
    exact (mem_filter.mp hn).1
  · intro n hn n' hn' h
    have he := congrArg (fun v => d * v) h
    simpa only [Nat.mul_div_cancel' (mem_filter.mp hn).2,
      Nat.mul_div_cancel' (mem_filter.mp hn').2] using he
  · intro v hv
    refine ⟨d * v, mem_filter.mpr
      ⟨(mem_quotient_interval L U d v hd).1 hv, dvd_mul_right d v⟩, ?_⟩
    exact Nat.mul_div_cancel_left v hd
  · intro n hn
    rw [Nat.mul_div_cancel' (mem_filter.mp hn).2]

def divisorAPMass (L U q a m d : ℕ) : ℝ :=
  ∑ n ∈ (Ico L U).filter (fun n => d ∣ n),
    if m * n ≡ a [MOD q] then 1 else 0

def divisorCoprimeMass (L U q m d : ℕ) : ℝ :=
  (∑ n ∈ (Ico L U).filter (fun n => d ∣ n),
    if (m * n).Coprime q then (1 : ℝ) else 0) / (q.totient : ℝ)

def divisorRemainder (L U q a m d : ℕ) : ℝ :=
  divisorAPMass L U q a m d - divisorCoprimeMass L U q m d

theorem divisorAPMass_reindex (L U q a m d : ℕ) (hd : 0 < d) :
    divisorAPMass L U q a m d =
      (part3LongSlotAPCount (lowerQuotient L d) (lowerQuotient U d) q a (m * d) : ℝ) := by
  unfold divisorAPMass
  rw [sum_divisible_interval L U d hd]
  simp [part3LongSlotAPCount, mul_assoc]

theorem divisorCoprimeMass_reindex (L U q m d : ℕ) (hd : 0 < d) :
    divisorCoprimeMass L U q m d =
      (part3LongSlotCoprimeCount (lowerQuotient L d) (lowerQuotient U d) q (m * d) : ℝ) /
        (q.totient : ℝ) := by
  unfold divisorCoprimeMass
  rw [sum_divisible_interval L U d hd]
  simp [part3LongSlotCoprimeCount, mul_assoc]

theorem divisorRemainder_reindex (L U q a m d : ℕ) (hd : 0 < d) :
    divisorRemainder L U q a m d =
      part3LongSlotRemainder (lowerQuotient L d) (lowerQuotient U d) q a (m * d) := by
  rw [divisorRemainder, divisorAPMass_reindex L U q a m d hd,
    divisorCoprimeMass_reindex L U q m d hd]
  rfl

-- The primitive quantifier is before ALL endpoints, short factors and divisors.
-- The error is exactly 2, independent of d, q, a, m, L, U and support order.
theorem divisorRemainder_abs_le_two (L U q a m d : ℕ)
    (hd : 0 < d) (hq : 0 < q) (ha : a.Coprime q) :
    |divisorRemainder L U q a m d| ≤ 2 := by
  rw [divisorRemainder_reindex L U q a m d hd]
  exact part3LongSlotRemainder_abs_le_two _ _ q a (m * d) hq ha

theorem divisorRemainder_eq_zero_of_nonunit (L U q a m d : ℕ)
    (hd : 0 < d) (ha : a.Coprime q) (hmd : ¬(m * d).Coprime q) :
    divisorRemainder L U q a m d = 0 := by
  rw [divisorRemainder_reindex L U q a m d hd]
  exact part3LongSlotRemainder_eq_zero_of_not_coprime _ _ q a (m * d) ha hmd

-- The coprime mean itself vanishes for nonunits, not just the discrepancy.
theorem divisorCoprimeMass_eq_zero_of_nonunit (L U q m d : ℕ)
    (hd : 0 < d) (hmd : ¬(m * d).Coprime q) :
    divisorCoprimeMass L U q m d = 0 := by
  rw [divisorCoprimeMass_reindex L U q m d hd]
  have hc (v : ℕ) : ¬((m * d) * v).Coprime q := by
    intro hv
    exact hmd (Nat.coprime_mul_iff_left.mp hv).1
  simp [part3LongSlotCoprimeCount, hc]

-- For units, the precise primitive-source mass is retained. No unrestricted
-- Euler density is substituted for this exact count.
theorem divisorCoprimeMass_eq_exact_mean (L U q m d : ℕ)
    (hd : 0 < d) (hmd : (m * d).Coprime q) :
    divisorCoprimeMass L U q m d =
      (part3IntervalCoprimeCount (lowerQuotient L d) (lowerQuotient U d) q : ℝ) /
        (q.totient : ℝ) := by
  rw [divisorCoprimeMass_reindex L U q m d hd]
  have hc (v : ℕ) : ((m * d) * v).Coprime q ↔ q.Coprime v := by
    constructor
    · intro hv
      exact (Nat.coprime_mul_iff_left.mp hv).2.symm
    · intro hv
      exact Nat.coprime_mul_iff_left.mpr ⟨hmd, hv.symm⟩
  simp only [part3LongSlotCoprimeCount, part3IntervalCoprimeCount, hc]

theorem quotient_mono (L U d : ℕ) (hd : 0 < d) (hLU : L ≤ U) :
    lowerQuotient L d ≤ lowerQuotient U d := by
  apply (ceilDiv_le_iff_le_mul hd).2
  exact hLU.trans (le_smul_ceilDiv (β := ℕ) hd)

theorem ceil_product_le (U d : ℕ) (hd : 0 < d) :
    d * lowerQuotient U d ≤ U + d := by
  by_cases hz : lowerQuotient U d = 0
  · simp [hz]
  · have hb : 0 < lowerQuotient U d := Nat.pos_of_ne_zero hz
    have hn : ¬ U ≤ d * (lowerQuotient U d - 1) := by
      intro h
      have hc : lowerQuotient U d ≤ lowerQuotient U d - 1 :=
        (ceilDiv_le_iff_le_mul hd).2 h
      omega
    have he : d * lowerQuotient U d = d * (lowerQuotient U d - 1) + d := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
    omega

-- The rounding cost is one, uniformly even for an interval shorter than d.
theorem quotient_length_le (L U d : ℕ) (hd : 0 < d) (hLU : L ≤ U) :
    ((lowerQuotient U d - lowerQuotient L d : ℕ) : ℝ) ≤
      ((U - L : ℕ) : ℝ) / (d : ℝ) + 1 := by
  have hm := quotient_mono L U d hd hLU
  have hlo : (L : ℝ) ≤ (d : ℝ) * (lowerQuotient L d : ℝ) := by
    exact_mod_cast (le_smul_ceilDiv (β := ℕ) hd : L ≤ d * (L ⌈/⌉ d))
  have hhi : (d : ℝ) * (lowerQuotient U d : ℝ) ≤ (U : ℝ) + d := by
    exact_mod_cast ceil_product_le U d hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Nat.cast_sub hm, Nat.cast_sub hLU]
  calc
    _ ≤ ((U : ℝ) - L + d) / (d : ℝ) := (le_div_iff₀ hdR).2 (by nlinarith)
    _ = ((U : ℝ) - L) / (d : ℝ) + 1 := by rw [add_div, div_self hdR.ne']

-- This is the exact remaining elementary classical primitive from original (3):
-- for ALL endpoints A<=B, coprime count has error <=Tq about its totient density.
-- The standard Mobius-inversion estimate permits Tq=2*tau(q). It concerns no
-- rough coefficient, no short sequence, and no Brun order.
def PrimitiveCoprimeDensity (q : ℕ) (Tq : ℝ) : Prop :=
  ∀ A B : ℕ, A ≤ B →
    |(part3IntervalCoprimeCount A B q : ℝ) -
      ((B - A : ℕ) : ℝ) * (q.totient : ℝ) / (q : ℝ)| ≤ Tq

def meanError (q : ℕ) (Tq : ℝ) : ℝ :=
  1 / (q : ℝ) + Tq / (q.totient : ℝ)

def atomMain (L U q m d : ℕ) : ℝ :=
  if (m * d).Coprime q then ((U - L : ℕ) : ℝ) / ((d : ℝ) * (q : ℝ)) else 0

theorem meanError_nonneg (q : ℕ) (Tq : ℝ) (hT : 0 ≤ Tq) :
    0 ≤ meanError q Tq := by unfold meanError; positivity

-- Exact quantitative coprime-mean supplier for each ACTUAL inserted divisor.
-- Deleted q-primes are retained by the compatibility indicator in atomMain.
theorem divisorCoprimeMass_le_main (L U q m d : ℕ) (Tq : ℝ)
    (hLU : L ≤ U) (hd : 0 < d) (hq : 0 < q) (hT : 0 ≤ Tq)
    (hprimitive : PrimitiveCoprimeDensity q Tq) :
    divisorCoprimeMass L U q m d ≤ atomMain L U q m d + meanError q Tq := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hphi : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  by_cases hmd : (m * d).Coprime q
  · rw [divisorCoprimeMass_eq_exact_mean L U q m d hd hmd]
    have hraw := (abs_le.mp (hprimitive _ _ (quotient_mono L U d hd hLU))).2
    have hdivide :
        (part3IntervalCoprimeCount (lowerQuotient L d) (lowerQuotient U d) q : ℝ) /
          (q.totient : ℝ) ≤
        ((lowerQuotient U d - lowerQuotient L d : ℕ) : ℝ) / (q : ℝ) +
          Tq / (q.totient : ℝ) := by
      have hraw' :
          (part3IntervalCoprimeCount (lowerQuotient L d) (lowerQuotient U d) q : ℝ) ≤
          ((lowerQuotient U d - lowerQuotient L d : ℕ) : ℝ) * (q.totient : ℝ) /
            (q : ℝ) + Tq := by linarith
      calc
        _ ≤ _ := div_le_div_of_nonneg_right hraw' hphi.le
        _ = _ := by field_simp [hphi.ne', hqR.ne']; ring
    have hlength := div_le_div_of_nonneg_right (quotient_length_le L U d hd hLU) hqR.le
    unfold atomMain meanError
    rw [if_pos hmd]
    calc
      _ ≤ _ := hdivide
      _ ≤ (((U - L : ℕ) : ℝ) / (d : ℝ) + 1) / (q : ℝ) + Tq / (q.totient : ℝ) :=
        add_le_add_right hlength _
      _ = _ := by field_simp; ring
  · rw [divisorCoprimeMass_eq_zero_of_nonunit L U q m d hd hmd]
    simp only [atomMain, if_neg hmd, zero_add]
    exact meanError_nonneg q Tq hT

theorem divisorAPMass_le_main (L U q a m d : ℕ) (Tq : ℝ)
    (hLU : L ≤ U) (hd : 0 < d) (hq : 0 < q) (ha : a.Coprime q) (hT : 0 ≤ Tq)
    (hprimitive : PrimitiveCoprimeDensity q Tq) :
    divisorAPMass L U q a m d ≤ atomMain L U q m d + (meanError q Tq + 2) := by
  have hp := divisorCoprimeMass_le_main L U q m d Tq hLU hd hq hT hprimitive
  have hc := (abs_le.mp (divisorRemainder_abs_le_two L U q a m d hd hq ha)).2
  unfold divisorRemainder at hc
  linarith

-- Any finite Brun polynomial therefore has an actual unrough atom bound.
-- The coefficients can be complex, and the divisor support is not regrouped.
theorem finite_divisor_polynomial_norm_le (S : Finset ℕ) (b : ℕ → ℂ)
    (L U q a m : ℕ) (hd : ∀ d ∈ S, 0 < d)
    (hq : 0 < q) (ha : a.Coprime q) :
    ‖∑ d ∈ S, b d * (divisorRemainder L U q a m d : ℂ)‖ ≤
      2 * ∑ d ∈ S, ‖b d‖ := by
  calc
    _ ≤ ∑ d ∈ S, ‖b d * (divisorRemainder L U q a m d : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ S, ‖b d‖ * 2 := by
      apply Finset.sum_le_sum
      intro d hdS
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (divisorRemainder_abs_le_two L U q a m d (hd d hdS) hq ha) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

-- The bound needed after simultaneous short/modulus restoration. The same
-- arbitrary primitive moving a is used in both count and exact source mean.
theorem full_finite_expanded_norm_le
    (Q M S : Finset ℕ) (rho alpha b : ℕ → ℂ) (L U a : ℕ)
    (hq : ∀ q ∈ Q, 0 < q) (ha : ∀ q ∈ Q, a.Coprime q)
    (hd : ∀ d ∈ S, 0 < d) :
    ‖∑ q ∈ Q, rho q * ∑ m ∈ M, alpha m *
      ∑ d ∈ S, b d * (divisorRemainder L U q a m d : ℂ)‖ ≤
      2 * (∑ q ∈ Q, ‖rho q‖) * (∑ m ∈ M, ‖alpha m‖) *
        (∑ d ∈ S, ‖b d‖) := by
  have hm (q : ℕ) (hqQ : q ∈ Q) :
      ‖∑ m ∈ M, alpha m * ∑ d ∈ S, b d * (divisorRemainder L U q a m d : ℂ)‖ ≤
        (∑ m ∈ M, ‖alpha m‖) * (2 * ∑ d ∈ S, ‖b d‖) := by
    calc
      _ ≤ ∑ m ∈ M, ‖alpha m * ∑ d ∈ S, b d * (divisorRemainder L U q a m d : ℂ)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ m ∈ M, ‖alpha m‖ * (2 * ∑ d ∈ S, ‖b d‖) := by
        apply Finset.sum_le_sum
        intro m hmM
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (finite_divisor_polynomial_norm_le S b L U q a m hd (hq q hqQ) (ha q hqQ))
          (norm_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]
  calc
    _ ≤ ∑ q ∈ Q, ‖rho q * ∑ m ∈ M, alpha m *
      ∑ d ∈ S, b d * (divisorRemainder L U q a m d : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Q, ‖rho q‖ * ((∑ m ∈ M, ‖alpha m‖) * (2 * ∑ d ∈ S, ‖b d‖)) := by
      apply Finset.sum_le_sum
      intro q hqQ
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hm q hqQ) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end
end OriginalOneLongDivisorIntervals
end ImbalancedChen
