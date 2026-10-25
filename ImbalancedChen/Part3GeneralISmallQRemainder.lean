import ImbalancedChen.Part3GeneralComplexISeries
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
Actual small-q remainder of the general complex-order I series. The remainder
is factored through the derivative quotient of the proved entire core. No
asymptotic, ODE, or connection formula is supplied as a hypothesis.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

noncomputable section
open scoped Topology
open Set Filter

namespace ImbalancedChen.Part3.GeneralISmallQRemainderSourceOnly

open GeneralComplexISeriesSourceOnly

def generalICoreDifferenceQuotient (mu z : ℂ) : ℂ :=
  z⁻¹ * (generalICore mu z - generalICore mu 0)

theorem positive_half_base_cpow_product (alpha mu : ℂ) {q : ℝ} (hq : 0 < q) :
    (q : ℂ) ^ alpha * (((q / 2 : ℝ) : ℂ) ^ mu) =
      ((2 : ℂ) ^ mu)⁻¹ * (q : ℂ) ^ (alpha + mu) := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  rw [Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.div_cpow_ofReal_nonneg hq.le (by norm_num : (0 : ℝ) ≤ 2),
    Complex.cpow_add alpha mu hqC]
  ring

theorem positive_half_base_cpow_product_sq (alpha mu : ℂ) {q : ℝ} (hq : 0 < q) :
    ((q : ℂ) ^ alpha * (((q / 2 : ℝ) : ℂ) ^ mu)) *
        (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)) =
      (((2 : ℂ) ^ mu)⁻¹ / 4) * (q : ℂ) ^ (alpha + mu + 2) := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  rw [positive_half_base_cpow_product alpha mu hq]
  have hz : (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)) = (q : ℂ) ^ (2 : ℕ) / 4 := by
    push_cast
    ring
  rw [hz, Complex.cpow_add (alpha + mu) 2 hqC, Complex.cpow_two]
  ring

theorem tendsto_positive_core_coordinate_punctured :
    Tendsto (fun q : ℝ => (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)))
      (𝓝[>] 0) (𝓝[≠] (0 : ℂ)) := by
  have hz : Tendsto (fun q : ℝ => (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)))
      (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    have hc : Continuous (fun q : ℝ => (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))) := by
      fun_prop
    have hzero : Tendsto (fun q : ℝ => (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)))
        (𝓝 0) (𝓝 (0 : ℂ)) := by simpa using hc.tendsto 0
    exact hzero.mono_left nhdsWithin_le_nhds
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hz
  filter_upwards [self_mem_nhdsWithin] with q hq
  change (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)) ≠ 0
  exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (div_pos hq (by norm_num)).ne')

/-- The actual core remainder quotient has a finite limit, supplied by its
proved analyticity rather than by a postulated Taylor estimate. -/
theorem tendsto_generalICoreDifferenceQuotient {mu : ℂ} (hmu : -1 < mu.re) :
    Tendsto (fun q : ℝ => generalICoreDifferenceQuotient mu
      (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))) (𝓝[>] 0)
      (𝓝 (deriv (generalICore mu) 0)) := by
  have hd := (analyticAt_generalICore hmu 0).differentiableAt.hasDerivAt
  simpa only [generalICoreDifferenceQuotient, zero_add, smul_eq_mul] using
    hd.tendsto_slope_zero.comp tendsto_positive_core_coordinate_punctured

theorem tendsto_positive_real_cpow_zero {beta : ℂ} (hbeta : 0 < beta.re) :
    Tendsto (fun q : ℝ => (q : ℂ) ^ beta) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
  have hb : beta ≠ 0 := by
    intro h
    simpa [h] using hbeta
  have h := (Complex.continuousAt_ofReal_cpow_const 0 beta (Or.inl hbeta)).tendsto
  simpa only [Complex.ofReal_zero, Complex.zero_cpow hb] using
    h.mono_left nhdsWithin_le_nhds

/-- Exact factorization of the genuine leading-term error. -/
theorem generalI_scaled_remainder_eq (alpha mu : ℂ) {q : ℝ} (hq : 0 < q) :
    (q : ℂ) ^ alpha *
        (generalI mu q - (((q / 2 : ℝ) : ℂ) ^ mu) / Complex.Gamma (mu + 1)) =
      ((((2 : ℂ) ^ mu)⁻¹ / 4) * (q : ℂ) ^ (alpha + mu + 2)) *
        generalICoreDifferenceQuotient mu (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)) := by
  let z : ℂ := (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ))
  have hz : z ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (div_pos hq (by norm_num)).ne')
  have hdiff : z * generalICoreDifferenceQuotient mu z =
      generalICore mu z - generalICore mu 0 := by
    simp only [generalICoreDifferenceQuotient, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]
  calc
    _ = ((q : ℂ) ^ alpha * (((q / 2 : ℝ) : ℂ) ^ mu)) *
        (generalICore mu z - generalICore mu 0) := by
      rw [generalICore_zero]
      dsimp [generalI, z]
      ring
    _ = (((q : ℂ) ^ alpha * (((q / 2 : ℝ) : ℂ) ^ mu)) * z) *
        generalICoreDifferenceQuotient mu z := by rw [← hdiff]; ring
    _ = _ := rw [show z = (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)) from rfl,
      positive_half_base_cpow_product_sq alpha mu hq]

/-- A genuine order-dependent second-term remainder, with the full complex
power range allowed by its positive real exponent. -/
theorem tendsto_generalI_scaled_remainder_zero {alpha mu : ℂ}
    (hmu : -1 < mu.re) (hexponent : 0 < (alpha + mu + 2).re) :
    Tendsto (fun q : ℝ => (q : ℂ) ^ alpha *
      (generalI mu q - (((q / 2 : ℝ) : ℂ) ^ mu) / Complex.Gamma (mu + 1)))
      (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
  have h := ((tendsto_positive_real_cpow_zero hexponent).const_mul
    (((2 : ℂ) ^ mu)⁻¹ / 4)).mul (tendsto_generalICoreDifferenceQuotient hmu)
  have hzero : Tendsto
      (fun q : ℝ => ((((2 : ℂ) ^ mu)⁻¹ / 4) * (q : ℂ) ^ (alpha + mu + 2)) *
        generalICoreDifferenceQuotient mu (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)))
      (𝓝[>] 0) (𝓝 (0 : ℂ)) := by simpa only [mul_zero, zero_mul] using h
  apply hzero.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (generalI_scaled_remainder_eq alpha mu hq).symm

/-- The negative-order remainder needed to identify the second K coefficient.
In particular it holds throughout `0 < re nu < 1`. -/
theorem tendsto_generalI_neg_order_remainder {nu : ℂ} (hnu : nu.re < 1) :
    Tendsto (fun q : ℝ => (q : ℂ) ^ (-nu) *
      (generalI (-nu) q - (((q / 2 : ℝ) : ℂ) ^ (-nu)) / Complex.Gamma (1 - nu)))
      (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
  have hm : -1 < (-nu).re := by simp only [Complex.neg_re]; linarith
  have he : 0 < ((-nu) + (-nu) + 2).re := by
    simp only [Complex.add_re, Complex.neg_re, Complex.ofNat_re]
    linarith
  simpa only [show -nu + 1 = 1 - nu by ring] using
    (tendsto_generalI_scaled_remainder_zero (alpha := -nu) hm he)

private theorem tendsto_core_small_q {mu : ℂ} (hmu : -1 < mu.re) :
    Tendsto (fun q : ℝ => generalICore mu (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)))
      (𝓝[>] 0) (𝓝 ((Complex.Gamma (mu + 1))⁻¹)) := by
  simpa only [generalICore_zero] using ((continuous_generalICore hmu).tendsto 0).comp
    (tendsto_positive_core_coordinate_punctured.mono_right nhdsWithin_le_nhds)

theorem tendsto_generalI_power_scaled_zero {alpha mu : ℂ} (hmu : -1 < mu.re)
    (hexponent : 0 < (alpha + mu).re) :
    Tendsto (fun q : ℝ => (q : ℂ) ^ alpha * generalI mu q)
      (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
  have h := ((tendsto_positive_real_cpow_zero hexponent).const_mul
    (((2 : ℂ) ^ mu)⁻¹)).mul (tendsto_core_small_q hmu)
  have hzero : Tendsto (fun q : ℝ =>
      (((2 : ℂ) ^ mu)⁻¹ * (q : ℂ) ^ (alpha + mu)) *
        generalICore mu (((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)))
      (𝓝[>] 0) (𝓝 (0 : ℂ)) := by simpa only [mul_zero, zero_mul] using h
  apply hzero.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  rw [generalI, ← mul_assoc, positive_half_base_cpow_product alpha mu hq]

theorem tendsto_q_order_mul_generalI_zero {nu : ℂ} (hnu : 0 < nu.re) :
    Tendsto (fun q : ℝ => (q : ℂ) ^ nu * generalI nu q)
      (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
  apply tendsto_generalI_power_scaled_zero (by linarith : -1 < nu.re)
  simp only [Complex.add_re]
  linarith

theorem tendsto_q_neg_order_mul_generalI {nu : ℂ} (hnu : -1 < nu.re) :
    Tendsto (fun q : ℝ => (q : ℂ) ^ (-nu) * generalI nu q)
      (𝓝[>] 0) (𝓝 (((2 : ℂ) ^ nu)⁻¹ * (Complex.Gamma (nu + 1))⁻¹)) := by
  have h := (tendsto_core_small_q hnu).const_mul (((2 : ℂ) ^ nu)⁻¹)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  rw [generalI, ← mul_assoc, positive_half_base_cpow_product (-nu) nu hq,
    neg_add_cancel, Complex.cpow_zero, mul_one]

end ImbalancedChen.Part3.GeneralISmallQRemainderSourceOnly
