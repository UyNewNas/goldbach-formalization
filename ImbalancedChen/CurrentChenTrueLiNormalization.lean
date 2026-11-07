import MathlibNt.SieveTheory.Distribution.BombieriVinogradov
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Leading constant of the genuine logarithmic integral

The genuine normalized logarithmic integral used by the ordinary prime-AP
supplier has leading coefficient one.  Its exact integration-by-parts
remainder is bounded by splitting the squared logarithmic density at `sqrt x`.
The final statements concern the actual `trueLogarithmicIntegral`, with no
asymptotic supplier assumed by the caller.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

/-- An explicit elementary upper bound for the exact squared-log remainder. -/
theorem currentChen_squaredLogIntegral_le {x : ℝ} (hx : 4 ≤ x) :
    (∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2) ≤
      Real.sqrt x / Real.log 2 ^ 2 + 4 * x / Real.log x ^ 2 := by
  have hxpos : 0 < x := by linarith
  have hx0 : 0 ≤ x := hxpos.le
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hsqrt0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsqrt2 : 2 ≤ Real.sqrt x := by
    nlinarith [Real.sq_sqrt hx0]
  have hsqrtx : Real.sqrt x ≤ x := by
    nlinarith [Real.sq_sqrt hx0]
  have hint := liuLogarithmicSquaredIntegrand_intervalIntegrable (by linarith : 2 ≤ x)
  have hint₁ := liuLogarithmicSquaredIntegrand_intervalIntegrable hsqrt2
  have hint₂ : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2)
      volume (Real.sqrt x) x :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hsqrtx, Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ x)]
      exact Set.Icc_subset_Icc hsqrt2 (le_refl _))
  have hfirst : (∫ t in (2 : ℝ)..Real.sqrt x, 1 / Real.log t ^ 2) ≤
      Real.sqrt x / Real.log 2 ^ 2 := by
    calc
      (∫ t in (2 : ℝ)..Real.sqrt x, 1 / Real.log t ^ 2) ≤
          ∫ _t in (2 : ℝ)..Real.sqrt x, 1 / Real.log 2 ^ 2 := by
        apply intervalIntegral.integral_mono_on hsqrt2 hint₁ intervalIntegrable_const
        intro t ht
        apply one_div_le_one_div_of_le (sq_pos_of_pos hlog2)
        have hlogs := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ht.1
        nlinarith
      _ = (Real.sqrt x - 2) / Real.log 2 ^ 2 := by
        simp [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv]
      _ ≤ Real.sqrt x / Real.log 2 ^ 2 :=
        (div_le_div_iff_of_pos_right (sq_pos_of_pos hlog2)).2 (by linarith)
  have hsecond : (∫ t in Real.sqrt x..x, 1 / Real.log t ^ 2) ≤
      4 * x / Real.log x ^ 2 := by
    calc
      (∫ t in Real.sqrt x..x, 1 / Real.log t ^ 2) ≤
          ∫ _t in Real.sqrt x..x, 4 / Real.log x ^ 2 := by
        apply intervalIntegral.integral_mono_on hsqrtx hint₂ intervalIntegrable_const
        intro t ht
        calc
          1 / Real.log t ^ 2 ≤ 1 / (Real.log x / 2) ^ 2 := by
            apply one_div_le_one_div_of_le (sq_pos_of_pos (div_pos hlogx (by norm_num)))
            have hlogs : Real.log x / 2 ≤ Real.log t := by
              calc
                Real.log x / 2 = Real.log (Real.sqrt x) := (Real.log_sqrt hx0).symm
                _ ≤ Real.log t := Real.log_le_log (Real.sqrt_pos.2 hxpos) ht.1
            nlinarith
          _ = 4 / Real.log x ^ 2 := by
            field_simp [hlogx.ne']; ring
      _ = (x - Real.sqrt x) * (4 / Real.log x ^ 2) := by
        simp [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv]
        ring
      _ ≤ 4 * x / Real.log x ^ 2 := by
        rw [show 4 * x / Real.log x ^ 2 = x * (4 / Real.log x ^ 2) by ring]
        exact mul_le_mul_of_nonneg_right (by linarith)
          (div_nonneg (by norm_num) (sq_nonneg _))
  rw [← intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂]
  exact add_le_add hfirst hsecond

/-- The normalized true logarithmic integral is squeezed between one and
an explicit error tending to zero. -/
theorem currentChen_trueLi_normalized_bounds {x : ℝ} (hx : 4 ≤ x) :
    1 ≤ trueLogarithmicIntegral x * Real.log x / x ∧
      trueLogarithmicIntegral x * Real.log x / x ≤
        1 + (1 / Real.log 2 ^ 2) * (Real.log x / Real.sqrt x) + 4 / Real.log x := by
  have hxpos : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hxpos.le
  have hrem := liuLogarithmicIntegralRemainder_eq (2 / Real.log 2)
    (by linarith : 2 ≤ x)
  have heq : trueLogarithmicIntegral x = x / Real.log x +
      ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
    change liuLogarithmicIntegral (2 / Real.log 2) x = _
    unfold liuLogarithmicIntegralRemainder at hrem
    linarith
  have hscale : 0 ≤ Real.log x / x := (div_pos hlogx hxpos).le
  have hlower := div_log_le_liuLogarithmicIntegral (by linarith : 2 ≤ x)
  have hupper := mul_le_mul_of_nonneg_right (currentChen_squaredLogIntegral_le hx) hscale
  constructor
  · have h := mul_le_mul_of_nonneg_right hlower hscale
    change x / Real.log x * (Real.log x / x) ≤
      trueLogarithmicIntegral x * (Real.log x / x) at h
    convert h using 1 <;> field_simp [hxpos.ne', hlogx.ne']
  · rw [heq]
    have hident :
        (x / Real.log x + ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2) * Real.log x / x =
          1 + (∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2) * (Real.log x / x) := by
      field_simp [hxpos.ne', hlogx.ne']
    rw [hident]
    have hident₂ :
        (Real.sqrt x / Real.log 2 ^ 2 + 4 * x / Real.log x ^ 2) * (Real.log x / x) =
          (1 / Real.log 2 ^ 2) * (Real.log x / Real.sqrt x) + 4 / Real.log x := by
      have hlog2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
      have hsqrt_div : Real.sqrt x / x = 1 / Real.sqrt x := by
        apply (div_eq_div_iff hxpos.ne' hsqrtpos.ne').2
        simpa only [one_mul, ← pow_two] using hsq
      calc
        (Real.sqrt x / Real.log 2 ^ 2 + 4 * x / Real.log x ^ 2) * (Real.log x / x) =
            (1 / Real.log 2 ^ 2) * (Real.log x * (Real.sqrt x / x)) +
              4 / Real.log x := by
          field_simp [hxpos.ne', hlogx.ne', hlog2]
        _ = (1 / Real.log 2 ^ 2) * (Real.log x / Real.sqrt x) + 4 / Real.log x := by
          rw [hsqrt_div]
          ring
    rw [hident₂] at hupper
    linarith

/-- The actual genuine logarithmic integral has leading constant one on
natural targets. -/
theorem tendsto_currentChen_trueLi_normalized :
    Tendsto (fun N : ℕ => trueLogarithmicIntegral N * Real.log N / (N : ℝ))
      atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun N : ℕ => Real.log (N : ℝ) / Real.sqrt (N : ℝ))
      atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have herror : Tendsto (fun N : ℕ =>
      1 + (1 / Real.log 2 ^ 2) * (Real.log (N : ℝ) / Real.sqrt (N : ℝ)) +
        4 / Real.log (N : ℝ)) atTop (𝓝 1) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds.add (hsmall.const_mul (1 / Real.log 2 ^ 2))).add
        (hlog.const_div_atTop (4 : ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds herror
  · filter_upwards [eventually_ge_atTop (4 : ℕ)] with N hN
    exact (currentChen_trueLi_normalized_bounds (by exact_mod_cast hN)).1
  · filter_upwards [eventually_ge_atTop (4 : ℕ)] with N hN
    exact (currentChen_trueLi_normalized_bounds (by exact_mod_cast hN)).2

/-- The leading-one upper bound needed by actual ordinary upper means. -/
theorem eventually_currentChen_trueLi_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      trueLogarithmicIntegral N ≤ (1 + ε) * (N : ℝ) / Real.log N := by
  have hnorm : ∀ᶠ N : ℕ in atTop,
      trueLogarithmicIntegral N * Real.log N / (N : ℝ) < 1 + ε :=
    tendsto_currentChen_trueLi_normalized.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [hnorm, eventually_ge_atTop (2 : ℕ)] with N hnorm hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  apply (le_div_iff₀ hlog).2
  have h := (div_lt_iff₀ hNpos).1 hnorm
  linarith

end

end ImbalancedChen
