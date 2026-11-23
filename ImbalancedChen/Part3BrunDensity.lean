import ImbalancedChen.Part3BrunWeights
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Totient

/-!
# Reciprocal density of the finite Brun upper weight

The average over one period of the prime set gives the reciprocal divisor
sum. The same period gives the Euler product for the rough indicator, so
the pointwise Brun bracket controls the density gap with its exact next rank.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators

private theorem average_divisor_expansion (S : Finset ℕ) (M : ℕ) (w : ℕ → ℝ)
    (hM : M ≠ 0) (hS : ∀ d ∈ S, d ∣ M) :
    (∑ n ∈ Ioc 0 M, ∑ d ∈ S, if d ∣ n then w d else 0) / (M : ℝ) =
      ∑ d ∈ S, w d / (d : ℝ) := by
  rw [sum_comm, sum_div]
  apply sum_congr rfl
  intro d hd
  rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.cast_div_charZero (hS d hd)]
  calc
    _ = (w d / (d : ℝ)) * ((M : ℝ) / M) := by ring
    _ = _ := by rw [div_self (Nat.cast_ne_zero.mpr hM), mul_one]

private theorem brunDivisors_dvd_period (P : Finset ℕ) (h : ℕ) :
    ∀ d ∈ brunDivisors P h, d ∣ ∏ p ∈ P, p := by
  intro d hd
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hd
  exact prod_dvd_prod_of_subset u.2 P id (mem_powersetCard.mp (mem_sigma.mp hu).2).1

private theorem brunGapDivisors_dvd_period (P : Finset ℕ) (h : ℕ) :
    ∀ d ∈ brunGapDivisors P h, d ∣ ∏ p ∈ P, p := by
  intro d hd
  obtain ⟨s, hs, rfl⟩ := mem_image.mp hd
  exact prod_dvd_prod_of_subset s P id (mem_powersetCard.mp hs).1

private theorem brunRoughIndicator_period_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑ n ∈ Ioc 0 (∏ p ∈ P, p), (brunRoughIndicator P n : ℝ)) =
      ((∏ p ∈ P, p).totient : ℝ) := by
  let M := ∏ p ∈ P, p
  have hcop (n : ℕ) : (P.filter fun p => p ∣ n).card = 0 ↔ M.Coprime n := by
    rw [card_eq_zero, filter_eq_empty_iff, Nat.coprime_prod_left_iff]
    exact ⟨fun h p hp => (hP p hp).coprime_iff_not_dvd.mpr (h hp),
      fun h p hp => (hP p hp).coprime_iff_not_dvd.mp (h p hp)⟩
  have hI : Ioc 0 M = Ico 1 (1 + M) := by
    ext n
    simp only [mem_Ioc, mem_Ico]
    omega
  calc
    _ = ∑ n ∈ Ioc 0 M, if M.Coprime n then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro n _
      simp only [brunRoughIndicator, hcop, apply_ite ((↑) : ℤ → ℝ), Int.cast_one, Int.cast_zero]
    _ = _ := by
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, hI, Nat.filter_coprime_Ico_eq_totient]

/-- The reciprocal Brun upper density exceeds the Euler product by at
most the reciprocal mass of the exact next rank. -/
theorem brunDensity_gap_bounds (P : Finset ℕ) (h : ℕ) (hP : ∀ p ∈ P, p.Prime) (hh : Even h) :
    0 ≤ (∑ d ∈ brunDivisors P h, (-1 : ℝ) ^ d.primeFactors.card / (d : ℝ)) -
        (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) ∧
    (∑ d ∈ brunDivisors P h, (-1 : ℝ) ^ d.primeFactors.card / (d : ℝ)) -
        (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) ≤ ∑ d ∈ brunGapDivisors P h, (d : ℝ)⁻¹ := by
  let M := ∏ p ∈ P, p
  have hM : 0 < M := prod_pos fun p hp => (hP p hp).pos
  have hMreal : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hA : (∑ n ∈ Ioc 0 M, (brunProjector P h n : ℝ)) / (M : ℝ) =
      ∑ d ∈ brunDivisors P h, (-1 : ℝ) ^ d.primeFactors.card / (d : ℝ) := by
    calc
      _ = (∑ n ∈ Ioc 0 M, ∑ d ∈ brunDivisors P h,
          if d ∣ n then (-1 : ℝ) ^ d.primeFactors.card else 0) / (M : ℝ) := by
        congr 1
        apply sum_congr rfl
        intro n _
        simp only [brunProjector_eq_divisor_sum P h n hP, Int.cast_sum,
          apply_ite ((↑) : ℤ → ℝ), Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_zero]
      _ = _ := average_divisor_expansion _ M _ hM.ne' (brunDivisors_dvd_period P h)
  have hV : (∑ n ∈ Ioc 0 M, (brunRoughIndicator P n : ℝ)) / (M : ℝ) =
      ∏ p ∈ P, (1 - (p : ℝ)⁻¹) := by
    have hpf : M.primeFactors = P := Nat.primeFactors_prod hP
    have htot : (M.totient : ℝ) = (M : ℝ) * ∏ p ∈ P, (1 - (p : ℝ)⁻¹) := by
      have hr := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors M)
      simpa only [hpf, Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub,
        Rat.cast_one, Rat.cast_inv] using hr
    rw [brunRoughIndicator_period_sum P hP, htot, mul_div_cancel_left₀ _ hMreal.ne']
  have hG : (∑ n ∈ Ioc 0 M,
      ((brunProjector P h n : ℝ) - (brunProjector P (h + 1) n : ℝ))) / (M : ℝ) =
      ∑ d ∈ brunGapDivisors P h, (d : ℝ)⁻¹ := by
    calc
      _ = (∑ n ∈ Ioc 0 M, ∑ d ∈ brunGapDivisors P h, if d ∣ n then (1 : ℝ) else 0) /
          (M : ℝ) := by
        congr 1
        apply sum_congr rfl
        intro n _
        simp only [← Int.cast_sub, brunProjector_gap_eq_divisor_sum P h n hP hh,
          Int.cast_sum, apply_ite ((↑) : ℤ → ℝ), Int.cast_one, Int.cast_zero]
      _ = _ := by
        simpa only [one_div] using average_divisor_expansion _ M (fun _ => 1) hM.ne'
          (brunGapDivisors_dvd_period P h)
  rw [← hA, ← hV, ← sub_div, ← sum_sub_distrib, ← hG]
  constructor
  · exact div_nonneg (sum_nonneg fun n _ => sub_nonneg.mpr (by
      exact_mod_cast (brunProjector_brackets P h n hP hh).2.1)) hMreal.le
  · apply div_le_div_of_nonneg_right _ hMreal.le
    apply sum_le_sum
    intro n _
    apply sub_le_sub_left
    exact_mod_cast (brunProjector_brackets P h n hP hh).1

/-- The literal reciprocal upper density is nonnegative and costs at most
one plus the factorial gap. The prime set can omit any modulus primes. -/
theorem brunDensity_nonneg_le (P : Finset ℕ) (h : ℕ) (hP : ∀ p ∈ P, p.Prime) (hh : Even h) :
    0 ≤ (∑ d ∈ brunDivisors P h, (-1 : ℝ) ^ d.primeFactors.card / (d : ℝ)) ∧
    (∑ d ∈ brunDivisors P h, (-1 : ℝ) ^ d.primeFactors.card / (d : ℝ)) ≤
      1 + (∑ p ∈ P, (p : ℝ)⁻¹) ^ (h + 1) / (h + 1).factorial := by
  have hfactor_nonneg (p : ℕ) (hp : p ∈ P) : 0 ≤ 1 - (p : ℝ)⁻¹ := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hp1)
  have hV0 : 0 ≤ ∏ p ∈ P, (1 - (p : ℝ)⁻¹) := prod_nonneg hfactor_nonneg
  have hV1 : (∏ p ∈ P, (1 - (p : ℝ)⁻¹)) ≤ 1 :=
    prod_le_one hfactor_nonneg (fun p _ => sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg p)))
  obtain ⟨hAV, hgap⟩ := brunDensity_gap_bounds P h hP hh
  refine ⟨hV0.trans (sub_nonneg.mp hAV), ?_⟩
  linarith [hgap.trans (brunGapDivisors_sum_reciprocal_le P h hP)]

end

end ImbalancedChen.Part3
