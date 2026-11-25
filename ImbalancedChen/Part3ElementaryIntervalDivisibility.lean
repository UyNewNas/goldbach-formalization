import ImbalancedChen.Part3ElementaryTauDeletionFiber
import Mathlib.Data.Nat.Factorization.Basic

namespace ImbalancedChen.Part3.ElementaryTauTruncation.IntervalPayment

noncomputable section

open Classical Finset
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- An exact count on the genuine positive interval (A,B]. -/
theorem interval_multiples_card_eq_div_sub {A B : ℕ} (hAB : A ≤ B) (d : ℕ) :
    ((Ioc A B).filter (fun n => d ∣ n)).card = B / d - A / d := by
  have hsub : (Ioc 0 A).filter (fun n => d ∣ n) ⊆
      (Ioc 0 B).filter (fun n => d ∣ n) := by
    intro n hn
    obtain ⟨hnI, hdn⟩ := Finset.mem_filter.mp hn
    obtain ⟨h0n, hnA⟩ := Finset.mem_Ioc.mp hnI
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨h0n, hnA.trans hAB⟩, hdn⟩
  have hset : (Ioc A B).filter (fun n => d ∣ n) =
      ((Ioc 0 B).filter (fun n => d ∣ n)) \
        ((Ioc 0 A).filter (fun n => d ∣ n)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hAn, hnB⟩, hdn⟩
      refine ⟨⟨⟨lt_of_le_of_lt (Nat.zero_le A) hAn, hnB⟩, hdn⟩, ?_⟩
      rintro ⟨⟨_h0n, hnA⟩, _hdn⟩
      exact (not_le_of_gt hAn) hnA
    · rintro ⟨⟨⟨h0n, hnB⟩, hdn⟩, hnA⟩
      refine ⟨⟨?_, hnB⟩, hdn⟩
      by_contra h
      exact hnA ⟨⟨h0n, le_of_not_gt h⟩, hdn⟩
  rw [hset, Finset.card_sdiff_of_subset hsub,
    Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div]

/-- The real interval length divided by d, plus one endpoint allowance. -/
theorem interval_multiples_card_le_length_div_add_one {A B d : ℕ}
    (hAB : A ≤ B) (hd : 0 < d) :
    (((Ioc A B).filter (fun n => d ∣ n)).card : ℝ) ≤
      ((B : ℝ) - (A : ℝ)) / (d : ℝ) + 1 := by
  rw [interval_multiples_card_eq_div_sub hAB, Nat.cast_sub (Nat.div_le_div_right hAB)]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hBlo : ((B / d : ℕ) : ℝ) * d ≤ B := by
    exact_mod_cast Nat.div_mul_le_self B d
  have hAhi : (A : ℝ) < (d : ℝ) * (((A / d : ℕ) : ℝ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ A hd
  have hBq : ((B / d : ℕ) : ℝ) ≤ (B : ℝ) / d :=
    (le_div_iff₀ hdR).mpr hBlo
  have hAq : (A : ℝ) / d < ((A / d : ℕ) : ℝ) + 1 :=
    (div_lt_iff₀ hdR).mpr (by nlinarith [hAhi])
  rw [sub_div]
  linarith

/-- The divisor carrier is exactly the bounded positive divisible carrier. -/
theorem truncated_divisor_carrier_eq {n D : ℕ} (hn : 0 < n) :
    n.divisors.filter (fun d => d ≤ D) = (Icc 1 D).filter (fun d => d ∣ n) := by
  ext d
  constructor
  · intro hd
    obtain ⟨hdn, hdD⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdn, hdD⟩,
        (Nat.mem_divisors.mp hdn).1⟩
  · intro hd
    obtain ⟨hdI, hdn⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hdn, hn.ne'⟩, (Finset.mem_Icc.mp hdI).2⟩

/-- Exact finite interchange, before applying any interval estimate. -/
theorem sum_interval_divisor_weights_swap (A B D : ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ Ioc A B, ∑ d ∈ (Icc 1 D).filter (fun d => d ∣ n), w d) =
      ∑ d ∈ Icc 1 D, w d * (((Ioc A B).filter (fun n => d ∣ n)).card : ℝ) := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- Deterministic payment for any nonnegative divisor weight. -/
theorem sum_interval_divisor_weights_le {A B D : ℕ} (w : ℕ → ℝ)
    (hAB : A ≤ B) (hw : ∀ d ∈ Icc 1 D, 0 ≤ w d) :
    (∑ n ∈ Ioc A B, ∑ d ∈ (Icc 1 D).filter (fun d => d ∣ n), w d) ≤
      ∑ d ∈ Icc 1 D, w d * (((B : ℝ) - (A : ℝ)) / (d : ℝ) + 1) := by
  rw [sum_interval_divisor_weights_swap]
  apply Finset.sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left
    (interval_multiples_card_le_length_div_add_one hAB (by
      have := (Finset.mem_Icc.mp hd).1
      omega)) (hw d hd)

/-- Finite tau truncation plus a literal interval count, with no analytic supplier. -/
theorem sum_fouvryTau_interval_payment {K A B D : ℕ}
    (hK : 2 ≤ K) (hAB : A ≤ B) (hcut : B ^ (K - 1) ≤ D ^ K) :
    (∑ n ∈ Ioc A B, (fouvryTau K n : ℝ)) ≤
      (K : ℝ) * ∑ d ∈ Icc 1 D,
        (fouvryTau (K - 1) d : ℝ) * (((B : ℝ) - (A : ℝ)) / (d : ℝ) + 1) := by
  have hpoint : ∀ n ∈ Ioc A B, (fouvryTau K n : ℝ) ≤
      (K : ℝ) * ∑ d ∈ (Icc 1 D).filter (fun d => d ∣ n),
        (fouvryTau (K - 1) d : ℝ) := by
    intro n hn
    obtain ⟨hAn, hnB⟩ := Finset.mem_Ioc.mp hn
    have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le A) hAn
    have hpow : n ^ (K - 1) ≤ B ^ (K - 1) :=
      pow_le_pow_left₀ (Nat.zero_le n) hnB _
    have hnat := fouvryTau_le_truncated_divisor_sum hK (by omega : 1 ≤ n)
      (hpow.trans hcut)
    rw [truncated_divisor_carrier_eq hnpos] at hnat
    exact_mod_cast hnat
  calc
    (∑ n ∈ Ioc A B, (fouvryTau K n : ℝ)) ≤
        ∑ n ∈ Ioc A B, (K : ℝ) *
          ∑ d ∈ (Icc 1 D).filter (fun d => d ∣ n), (fouvryTau (K - 1) d : ℝ) :=
      Finset.sum_le_sum hpoint
    _ = (K : ℝ) * (∑ n ∈ Ioc A B,
        ∑ d ∈ (Icc 1 D).filter (fun d => d ∣ n), (fouvryTau (K - 1) d : ℝ)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (K : ℝ) * ∑ d ∈ Icc 1 D,
        (fouvryTau (K - 1) d : ℝ) * (((B : ℝ) - (A : ℝ)) / (d : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left
        (sum_interval_divisor_weights_le (fun d => (fouvryTau (K - 1) d : ℝ)) hAB
          (fun d _hd => Nat.cast_nonneg _)) (Nat.cast_nonneg K)

/-- The separated reciprocal and ordinary payments needed by the E1 route. -/
theorem sum_fouvryTau_interval_payment_split {K A B D : ℕ}
    (hK : 2 ≤ K) (hAB : A ≤ B) (hcut : B ^ (K - 1) ≤ D ^ K) :
    (∑ n ∈ Ioc A B, (fouvryTau K n : ℝ)) ≤
      (K : ℝ) * (((B : ℝ) - (A : ℝ)) *
        (∑ d ∈ Icc 1 D, (fouvryTau (K - 1) d : ℝ) / (d : ℝ)) +
        ∑ d ∈ Icc 1 D, (fouvryTau (K - 1) d : ℝ)) := by
  calc
    (∑ n ∈ Ioc A B, (fouvryTau K n : ℝ)) ≤
        (K : ℝ) * ∑ d ∈ Icc 1 D,
          (fouvryTau (K - 1) d : ℝ) * (((B : ℝ) - (A : ℝ)) / (d : ℝ) + 1) :=
      sum_fouvryTau_interval_payment hK hAB hcut
    _ = _ := by
      congr 1
      calc
        (∑ d ∈ Icc 1 D,
            (fouvryTau (K - 1) d : ℝ) * (((B : ℝ) - (A : ℝ)) / (d : ℝ) + 1)) =
            ∑ d ∈ Icc 1 D, (((B : ℝ) - (A : ℝ)) *
              ((fouvryTau (K - 1) d : ℝ) / (d : ℝ)) + (fouvryTau (K - 1) d : ℝ)) := by
          apply Finset.sum_congr rfl
          intro d _hd
          ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]

end

end ImbalancedChen.Part3.ElementaryTauTruncation.IntervalPayment
