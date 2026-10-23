import ImbalancedChen.ActualSieveGapTailDecay
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperSourcePTail

set_option Elab.async false

/-!
# Explicit constants and scalar decay for the actual sieve gap tail

The reference constant is obtained from the actual Suzuki amplitude and the
proved first-interval lower factor.  The final scalar limit concerns the
displayed tail envelope alone; comparison of a T3 integral to that envelope
is a separate obligation.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- Exact reference value of the normalized actual gap at three. -/
theorem actualSieveGap_normalized_at_three :
    actualSieveGap 3 / (2 * Real.exp Real.eulerMascheroniConstant) =
      (1 - Real.log 2) / 3 := by
  have hAmplitude := suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
    jr1965Section13HatSourceContract
  have hUpper : suzukiContinuousUpperFactor 3 =
      2 * Real.exp Real.eulerMascheroniConstant / 3 := by
    have h := suzukiLowerSieveAmplitude_eq_three_mul_upperFactor
    rw [hAmplitude] at h
    linarith
  have hLower : suzukiContinuousLowerFactor 3 =
      2 * Real.exp Real.eulerMascheroniConstant * Real.log 2 / 3 := by
    rw [suzukiContinuousLowerFactor, suzukiContinuousLowerTail,
      one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval
        jr1965Section13HatSourceContract (by norm_num : (2 : ℝ) ≤ 3)
        (by norm_num : (3 : ℝ) ≤ 4),
      suzukiLowerSieveFactorFirstInterval_eq_log (by norm_num : (2 : ℝ) ≤ 3)
        (by norm_num : (3 : ℝ) ≤ 4), hAmplitude]
    norm_num
  rw [actualSieveGap, hUpper, hLower]
  field_simp [ne_of_gt (Real.exp_pos Real.eulerMascheroniConstant)]

/-- A convenient explicit tail constant, with no numerical certificate premise. -/
theorem actualSieveGap_normalized_le_three_div_sq {s : ℝ} (hs : 3 ≤ s) :
    actualSieveGap s / (2 * Real.exp Real.eulerMascheroniConstant) ≤ 3 / s ^ 2 := by
  have h := actualSieveGap_normalized_le_quadratic_tail
    (s0 := (3 : ℝ)) (by norm_num) hs
  rw [actualSieveGap_normalized_at_three] at h
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hc : (1 - Real.log (2 : ℝ)) / 3 ≤ (1 : ℝ) / 3 := by linarith
  have hspos : 0 < s := by linarith
  calc
    actualSieveGap s / (2 * Real.exp Real.eulerMascheroniConstant) ≤
        ((1 - Real.log 2) / 3) * (3 / s) ^ 2 := h
    _ ≤ ((1 : ℝ) / 3) * (3 / s) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = 3 / s ^ 2 := by field_simp [ne_of_gt hspos]

/-- Every fixed logarithmic power is absorbed by the positive small parameter. -/
theorem tendsto_mul_log_div_pow_zero (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun h : ℝ => h * Real.log (a / h) ^ n) (𝓝[>] 0) (𝓝 0) := by
  have hInv : Tendsto (fun h : ℝ => a / h) (𝓝[>] 0) atTop := by
    simpa only [div_eq_mul_inv] using
      (tendsto_inv_nhdsGT_zero : Tendsto (fun h : ℝ => h⁻¹) (𝓝[>] 0) atTop).const_mul_atTop ha
  have hLimit := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero).comp hInv).const_mul a
  simp only [one_mul, add_zero, mul_zero, Function.comp_def] at hLimit
  apply hLimit.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hhpos : 0 < h := hh
  field_simp [ne_of_gt ha, ne_of_gt hhpos]

/-- The scalar envelope used for rough activation tends to zero from the right.
This does not assume or assert that a particular T3 integral is bounded by it. -/
theorem tendsto_roughActivationTailEnvelope_zero {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun h : ℝ => 18 * h / (c - h) ^ 2 *
      (Real.log (a / h) ^ 2 + 2 * Real.log (a / h) + 2))
      (𝓝[>] 0) (𝓝 0) := by
  have hId : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hOne : Tendsto (fun h : ℝ => h * Real.log (a / h)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [pow_one] using tendsto_mul_log_div_pow_zero 1 ha
  have hTwo := tendsto_mul_log_div_pow_zero 2 ha
  have hDifference : Tendsto (fun h : ℝ => c - h) (𝓝[>] 0) (𝓝 c) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := c)).sub hId
  have hDen : Tendsto (fun h : ℝ => 18 / (c - h) ^ 2)
      (𝓝[>] 0) (𝓝 (18 / c ^ 2)) := by
    exact tendsto_const_nhds.div (hDifference.pow 2) (pow_ne_zero 2 (ne_of_gt hc))
  have hNumer := (hTwo.add (hOne.const_mul 2)).add (hId.const_mul 2)
  have hProduct := hDen.mul hNumer
  simp only [mul_zero, add_zero] at hProduct
  convert hProduct using 1
  ext h
  ring

/-- The manuscript's explicit rational specialization of the scalar envelope. -/
theorem tendsto_roughActivationTailEnvelope_rational_zero :
    Tendsto (fun h : ℝ => 18 * h / ((19 : ℝ) / 192 - h) ^ 2 *
      (Real.log (((19 : ℝ) / 96) / h) ^ 2 +
        2 * Real.log (((19 : ℝ) / 96) / h) + 2))
      (𝓝[>] 0) (𝓝 0) := by
  exact tendsto_roughActivationTailEnvelope_zero (by norm_num) (by norm_num)

end

end ImbalancedChen
