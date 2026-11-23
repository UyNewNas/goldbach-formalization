import ImbalancedChen.Part3RoughAuxiliarySWNormalization
import Mathlib.Algebra.BigOperators.Module
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Partial summation for the exact auxiliary-coprimality discrepancy

An interval estimate for the unweighted slot also controls the same slot with
a complex profile. The cost is the final weight plus the total variation on
the common interval. Both the progression and the coprime mean are weighted.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Filter Finset
open scoped BigOperators

private def swSummand (α : ℕ → ℂ) (k q b n : ℕ) : ℂ :=
  (if Nat.ModEq q n b ∧ Nat.Coprime n k then α n else 0) -
    (if Nat.Coprime n (k * q) then α n else 0) / (Nat.totient q : ℂ)

private theorem auxiliarySWError_eq_sum (S : Finset ℕ) (α : ℕ → ℂ) (k q b : ℕ) :
    auxiliarySWError S α k q b = ∑ n ∈ S, swSummand α k q b n := by
  simp only [auxiliarySWError, swSummand, sum_sub_distrib, sum_div]

private theorem swSummand_mul_weight (α w : ℕ → ℂ) (k q b n : ℕ) :
    swSummand (fun j => w j * α j) k q b n = w n * swSummand α k q b n := by
  unfold swSummand
  split_ifs <;> ring

/-- Uniform interval-prefix bounds transfer to the weighted discrepancy by
discrete partial summation. The weight may be complex and need not be smooth. -/
theorem auxiliarySWError_weighted_Ioc_norm_le
    (L H k q b : ℕ) (α w : ℕ → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hPrefix : ∀ T : ℕ, T ≤ H → ‖auxiliarySWError (Ioc L T) α k q b‖ ≤ E) :
    ‖auxiliarySWError (Ioc L H) (fun n => w n * α n) k q b‖ ≤
      (‖w H‖ + ∑ n ∈ Ioc L (H - 1), ‖w (n + 1) - w n‖) * E := by
  by_cases hLH : L < H
  · let f (n : ℕ) : ℂ := if L < n then swSummand α k q b n else 0
    have hprefixEq (T : ℕ) : (∑ n ∈ range (T + 1), f n) =
        auxiliarySWError (Ioc L T) α k q b := by
      rw [auxiliarySWError_eq_sum]
      simp only [f, ← sum_filter]
      congr 1
      ext n
      simp only [mem_Ioc, mem_filter, mem_range]
      omega
    have hweighted : auxiliarySWError (Ioc L H) (fun n => w n * α n) k q b =
        ∑ n ∈ Ioc L H, w n * f n := by
      rw [auxiliarySWError_eq_sum]
      apply sum_congr rfl
      intro n hn
      simp only [swSummand_mul_weight, f, if_pos (mem_Ioc.mp hn).1]
    have hzero : auxiliarySWError (Ioc L L) α k q b = 0 := by
      simp [auxiliarySWError]
    have hAbel := sum_Ioc_by_parts w f hLH
    simp only [smul_eq_mul, hprefixEq, hzero, sub_zero, mul_zero] at hAbel
    rw [hweighted, hAbel]
    calc
      _ ≤ ‖w H * auxiliarySWError (Ioc L H) α k q b‖ +
          ‖∑ n ∈ Ioc L (H - 1),
            (w (n + 1) - w n) * auxiliarySWError (Ioc L n) α k q b‖ := norm_sub_le _ _
      _ ≤ ‖w H‖ * E + ∑ n ∈ Ioc L (H - 1), ‖w (n + 1) - w n‖ * E := by
        apply add_le_add
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hPrefix H le_rfl) (norm_nonneg _)
        · refine (norm_sum_le _ _).trans (sum_le_sum ?_)
          intro n hn
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hPrefix n ((mem_Ioc.mp hn).2.trans
            (Nat.sub_le _ _))) (norm_nonneg _)
      _ = _ := by rw [add_mul, sum_mul]
  · rw [Ioc_eq_empty_of_le (Nat.le_of_not_gt hLH)]
    simp only [auxiliarySWError, sum_empty, zero_div, sub_zero, norm_zero]
    exact mul_nonneg (add_nonneg (norm_nonneg _) (sum_nonneg fun _ _ => norm_nonneg _)) hE

/-- The chart roughness cutoff has logarithm at least the square root of
the logarithm of the complete scale, eventually. -/
theorem eventually_log_roughCutoff_ge_sqrt_log :
    ∀ᶠ x : ℝ in atTop,
      (Real.log x) ^ (1 / 2 : ℝ) ≤
        Real.log (x ^ (1 / (Real.log (Real.log x)) ^ 3)) := by
  have h3 := (isLittleO_log_rpow_rpow_atTop (3 : ℝ)
    (show (0 : ℝ) < 1 / 2 by norm_num)).eventuallyLE
  filter_upwards [Real.tendsto_log_atTop.eventually h3,
    eventually_gt_atTop (Real.exp (Real.exp 1))] with x hx3 hx
  have hxpos := (Real.exp_pos _).trans hx
  have hlog : Real.exp 1 < Real.log x := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hx
  have hlogpos := (Real.exp_pos _).trans hlog
  have hloglog : 1 < Real.log (Real.log x) := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hlog
  have hloglogpos : 0 < Real.log (Real.log x) := zero_lt_one.trans hloglog
  have hc : (Real.log (Real.log x)) ^ 3 ≤ (Real.log x) ^ (1 / 2 : ℝ) := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hloglogpos.le (3 : ℝ)),
      Real.norm_of_nonneg (Real.rpow_nonneg hlogpos.le (1 / 2 : ℝ))] at hx3
    simpa only [Real.rpow_ofNat] using hx3
  rw [Real.log_rpow hxpos, div_mul_eq_mul_div, one_mul]
  apply (le_div_iff₀ (pow_pos hloglogpos 3)).mpr
  calc
    _ ≤ (Real.log x) ^ (1 / 2 : ℝ) * (Real.log x) ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hlogpos.le _)
    _ = Real.log x := by rw [← Real.rpow_add hlogpos, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
      Real.rpow_one]

/-- The chart cutoffis monotone once the double logarithm reaches three. -/
theorem roughCutoff_mono_of_exp_exp_three {x y : ℝ}
    (hx : Real.exp (Real.exp 3) ≤ x) (hxy : x ≤ y) :
    x ^ (1 / (Real.log (Real.log x)) ^ 3) ≤ y ^ (1 / (Real.log (Real.log y)) ^ 3) := by
  have hxpos := (Real.exp_pos _).trans_le hx
  have hypos := hxpos.trans_le hxy
  have hlogx : Real.exp 3 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos (Real.exp 3)) hx
  have hlogxpos := (Real.exp_pos _).trans_le hlogx
  have hlogxy := Real.log_le_log hxpos hxy
  have hlogypos := hlogxpos.trans_le hlogxy
  let a := Real.log (Real.log x)
  let b := Real.log (Real.log y)
  have ha : 3 ≤ a := by
    simpa only [a, Real.log_exp] using Real.log_le_log (Real.exp_pos 3) hlogx
  have hab : a ≤ b := Real.log_le_log hlogxpos hlogxy
  have ha0 : 0 < a := (by norm_num : (0 : ℝ) < 3).trans_le ha
  have hb0 := ha0.trans_le hab
  have hdiff : Real.log b - Real.log a ≤ (b - a) / a := by
    have h := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    rw [Real.log_div hb0.ne' ha0.ne'] at h
    convert h using 1
    field_simp
  have hdiff' : 3 * (Real.log b - Real.log a) ≤ b - a := by
    calc
      _ ≤ 3 * ((b - a) / a) := mul_le_mul_of_nonneg_left hdiff (by norm_num)
      _ ≤ a * ((b - a) / a) :=
        mul_le_mul_of_nonneg_right ha (div_nonneg (sub_nonneg.mpr hab) ha0.le)
      _ = _ := by field_simp
  have hscaled : Real.exp a / a ^ 3 ≤ Real.exp b / b ^ 3 := by
    apply (Real.log_le_log_iff (div_pos (Real.exp_pos _) (pow_pos ha0 _))
      (div_pos (Real.exp_pos _) (pow_pos hb0 _))).mp
    rw [Real.log_div (Real.exp_pos a).ne' (pow_pos ha0 3).ne',
      Real.log_div (Real.exp_pos b).ne' (pow_pos hb0 3).ne', Real.log_exp, Real.log_exp,
      Real.log_pow, Real.log_pow]
    norm_num
    linarith
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hxpos _) (Real.rpow_pos_of_pos hypos _)).mp
  rw [Real.log_rpow hxpos, Real.log_rpow hypos]
  change 1 / a ^ 3 * Real.log x ≤ 1 / b ^ 3 * Real.log y
  rw [← Real.exp_log hlogxpos, ← Real.exp_log hlogypos]
  change 1 / a ^ 3 * Real.exp a ≤ 1 / b ^ 3 * Real.exp b
  simpa only [div_mul_eq_mul_div, one_mul] using hscaled

/-- Summing the prime estimates at the quotient scales `H / m` loses one
harmonic factor. Every quotient in the sum exceeds the actual chart cutoff. -/
theorem eventually_roughPrimeFactor_sum_logAccuracy (A : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop, ∀ z : ℝ, x ^ (1 / (Real.log (Real.log x)) ^ 3) ≤ z →
      ∀ H : ℕ, (H : ℝ) ≤ 2 * x →
      (∑ m ∈ Icc 1 (H / (⌊z⌋₊ + 1)),
        C * (H / m : ℕ) / Real.log (H / m : ℕ) ^ (2 * (A + 1))) ≤
        3 * C * H / Real.log x ^ A := by
  filter_upwards [eventually_log_roughCutoff_ge_sqrt_log,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with x hcut hlog hx
  intro z hzcut H hH
  let M := H / (⌊z⌋₊ + 1)
  change (∑ m ∈ Icc 1 M, C * (H / m : ℕ) / Real.log (H / m : ℕ) ^ (2 * (A + 1))) ≤ _
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlogpos : 0 < Real.log x := zero_lt_one.trans_le hlog
  have hbasepos : 0 < x ^ (1 / (Real.log (Real.log x)) ^ 3) := Real.rpow_pos_of_pos hxpos _
  have hz : 0 < z := hbasepos.trans_le hzcut
  have hlogz := hcut.trans (Real.log_le_log hbasepos hzcut)
  have hsum : (∑ m ∈ Icc 1 M, (1 : ℝ) / m) ≤ 3 * Real.log x := by
    have hharm : (∑ m ∈ Icc 1 M, (1 : ℝ) / m) ≤ 1 + Real.log M := by
      simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
        one_div] using harmonic_le_one_add_log M
    have hM : (M : ℝ) ≤ 2 * x := (Nat.cast_le.mpr (Nat.div_le_self _ _)).trans hH
    have hlogM : Real.log M ≤ Real.log 2 + Real.log x := by
      rcases Nat.eq_zero_or_pos M with hM0 | hM0
      · simp only [hM0, Nat.cast_zero, Real.log_zero]
        exact add_nonneg (Real.log_nonneg (by norm_num)) hlogpos.le
      · rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hxpos.ne']
        exact Real.log_le_log (Nat.cast_pos.mpr hM0) hM
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  calc
    _ ≤ ∑ m ∈ Icc 1 M, (C * H / Real.log x ^ (A + 1)) * (1 / (m : ℝ)) := by
      apply sum_le_sum
      intro m hm
      obtain ⟨hm1, hmM⟩ := mem_Icc.mp hm
      have hmpos : 0 < m := hm1
      have hmul : m * (⌊z⌋₊ + 1) ≤ H := by
        simpa [mul_comm] using (Nat.le_div_iff_mul_le (by positivity)).mp hmM
      have hdiv : ⌊z⌋₊ + 1 ≤ H / m := (Nat.le_div_iff_mul_le hmpos).mpr (by
        simpa [mul_comm] using hmul)
      have hquot : z < (H / m : ℕ) := (Nat.lt_succ_floor z).trans_le (Nat.cast_le.mpr hdiv)
      have hlower : (Real.log x) ^ (1 / 2 : ℝ) ≤ Real.log (H / m : ℕ) :=
        hlogz.trans (Real.log_le_log hz hquot.le)
      have hden : Real.log x ^ (A + 1) ≤ Real.log (H / m : ℕ) ^ (2 * (A + 1)) := by
        have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hlogpos.le _) hlower (2 * (A + 1))
        have heq : ((Real.log x) ^ (1 / 2 : ℝ)) ^ (2 * (A + 1)) =
            Real.log x ^ (A + 1) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hlogpos.le, ← Real.rpow_natCast]
          congr 1
          push_cast
          ring
        exact heq ▸ hpow
      calc
        _ ≤ C * (H / m : ℕ) / Real.log x ^ (A + 1) :=
          div_le_div_of_nonneg_left (by positivity) (pow_pos hlogpos _) hden
        _ ≤ C * ((H : ℝ) / m) / Real.log x ^ (A + 1) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left Nat.cast_div_le hC) (by positivity)
        _ = _ := by ring
    _ = (C * H / Real.log x ^ (A + 1)) * (∑ m ∈ Icc 1 M, (1 : ℝ) / m) := by
      rw [mul_sum]
    _ ≤ (C * H / Real.log x ^ (A + 1)) * (3 * Real.log x) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      rw [pow_succ]
      field_simp

end

end ImbalancedChen.Part3
