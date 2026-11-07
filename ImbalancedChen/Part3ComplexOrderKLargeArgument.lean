import ImbalancedChen.Part3ComplexOrderKEntire
import ImbalancedChen.Part3ActualHalfOrderKWronskian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
For arbitrary fixed complex order, the actual cosh-Laplace K integral
satisfies sqrt(q) exp(q) K_nu(q) -> sqrt(pi/2). The change of variable
u=v/sqrt(q), the eventual Gaussian majorant, and the pointwise Gaussian
limit are all proved. No ODE solution selection or asymptotic is assumed.
-/

namespace ImbalancedChen.Part3.ComplexOrderKLargeArgument20261025a
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ComplexOrderKBridgeSourceOnly
open ActualHalfOrderKWronskianSourceOnly (cosh_eq_one_add_two_sinh_half_sq)

def scaledKernel (ν : ℂ) (q v : ℝ) : ℂ :=
  (Real.exp (-q * (Real.cosh (v / Real.sqrt q) - 1)) : ℂ) *
    Complex.cosh (ν * ((v / Real.sqrt q : ℝ) : ℂ))

theorem cosh_quadratic_at_zero {u : ℝ} (hu : 0 ≤ u) :
    1 + u ^ 2 / 2 ≤ Real.cosh u := by
  have hh := Real.self_le_sinh_iff.mpr (show 0 ≤ u / 2 by positivity)
  have hs : 0 ≤ Real.sinh (u / 2) := (show 0 ≤ u / 2 by positivity).trans hh
  have hm := mul_nonneg (sub_nonneg.mpr hh)
    (add_nonneg hs (show 0 ≤ u / 2 by positivity))
  rw [cosh_eq_one_add_two_sinh_half_sq]
  nlinarith only [hm]

theorem scaledKernel_integral (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    (∫ v in Ioi (0 : ℝ), scaledKernel ν q v) =
      ((Real.sqrt q * Real.exp q : ℝ) : ℂ) * complexOrderK ν q := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hpoint (v : ℝ) : scaledKernel ν q v =
      (Real.exp q : ℂ) * complexOrderIntegrand ν q (v / Real.sqrt q) := by
    unfold scaledKernel complexOrderIntegrand
    have he : -q * (Real.cosh (v / Real.sqrt q) - 1) =
        q + -q * Real.cosh (v / Real.sqrt q) := by ring
    rw [he, Real.exp_add, Complex.ofReal_mul]
    ring
  have hscale : (∫ v in Ioi (0 : ℝ), complexOrderIntegrand ν q (v / Real.sqrt q)) =
      (Real.sqrt q : ℂ) * complexOrderK ν q := by
    simpa only [one_div, inv_inv, mul_zero, Complex.real_smul,
      complexOrderK, mul_comm, ← div_eq_mul_inv] using
      integral_comp_mul_left_Ioi (complexOrderIntegrand ν q) 0 (one_div_pos.mpr hs)
  simp_rw [hpoint]
  rw [integral_const_mul, hscale, Complex.ofReal_mul]
  ring

/-- A universal Gaussian majorant once q dominates the square real order. -/
theorem scaledKernel_norm_le_gaussian (ν : ℂ) {q v : ℝ}
    (hq : 0 < q) (horder : 2 * ν.re ^ 2 ≤ q) (hv : 0 ≤ v) :
    ‖scaledKernel ν q v‖ ≤ Real.exp (-(v ^ 2 / 4)) := by
  let u : ℝ := v / Real.sqrt q
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hu : 0 ≤ u := div_nonneg hv hs.le
  have hfactor : q * u ^ 2 = v ^ 2 := by
    dsimp [u]
    rw [div_pow, Real.sq_sqrt hq.le]
    field_simp [hq.ne'] <;> ring
  have hcosh := cosh_quadratic_at_zero hu
  have hc : ‖Complex.cosh (ν * (u : ℂ))‖ ≤ Real.exp ((ν.re * u) ^ 2 / 2) := by
    have hh : ‖Complex.cosh (ν * (u : ℂ))‖ ≤ Real.cosh (ν.re * u) := by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        using norm_complex_cosh_le_real_cosh (ν * (u : ℂ))
    exact hh.trans (Real.cosh_le_exp_half_sq _)
  have hdecay : -q * (Real.cosh u - 1) + (ν.re * u) ^ 2 / 2 ≤ -(v ^ 2 / 4) := by
    have h1 := mul_le_mul_of_nonneg_left hcosh hq.le
    have h2 := mul_le_mul_of_nonneg_right horder (sq_nonneg u)
    nlinarith only [h1, h2, hfactor]
  calc
    ‖scaledKernel ν q v‖ = Real.exp (-q * (Real.cosh u - 1)) *
        ‖Complex.cosh (ν * (u : ℂ))‖ := by
      simp only [scaledKernel, u, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-q * (Real.cosh u - 1)) * Real.exp ((ν.re * u) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
    _ = Real.exp (-q * (Real.cosh u - 1) + (ν.re * u) ^ 2 / 2) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hdecay

theorem gaussianMajorant_integrable :
    IntegrableOn (fun v : ℝ => Real.exp (-(v ^ 2 / 4))) (Ioi 0) := by
  have h := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).integrableOn
  convert h using 1
  funext v
  congr 1
  ring

theorem scaledArgument_tendsto_zero (v : ℝ) :
    Tendsto (fun q : ℝ => v / Real.sqrt q) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul v
  simpa only [div_eq_mul_inv, mul_zero] using h

/-- The exact quadratic local limit is obtained from the derivative of sinh. -/
theorem scaledCoshGap_tendsto {v : ℝ} (hv : 0 < v) :
    Tendsto (fun q : ℝ => q * (Real.cosh (v / Real.sqrt q) - 1))
      atTop (𝓝 (v ^ 2 / 2)) := by
  let t : ℝ → ℝ := fun q => (v / Real.sqrt q) / 2
  have ht0 : Tendsto t atTop (𝓝 0) := by
    simpa only [t, zero_div] using (scaledArgument_tendsto_zero v).div_const 2
  have ht : Tendsto t atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr ⟨ht0, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with q hq
    exact half_pos (div_pos hv (Real.sqrt_pos.mpr hq))
  have hsinh : Tendsto (fun x : ℝ => Real.sinh x / x) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [zero_add, Real.sinh_zero, sub_zero, Real.cosh_zero, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using (Real.hasDerivAt_sinh 0).tendsto_slope_zero_right
  have hratio := hsinh.comp ht
  have hlim : Tendsto (fun q : ℝ => (v ^ 2 / 2) * (Real.sinh (t q) / t q) ^ 2)
      atTop (𝓝 (v ^ 2 / 2)) := by
    simpa only [one_pow, mul_one] using (hratio.pow 2).const_mul (v ^ 2 / 2)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with q hq
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  let u : ℝ := v / Real.sqrt q
  have hu : 0 < u := div_pos hv hs
  have hfactor : q * u ^ 2 = v ^ 2 := by
    dsimp [u]
    rw [div_pow, Real.sq_sqrt hq.le]
    field_simp [hq.ne'] <;> ring
  change (v ^ 2 / 2) * (Real.sinh (u / 2) / (u / 2)) ^ 2 = q * (Real.cosh u - 1)
  rw [← hfactor, cosh_eq_one_add_two_sinh_half_sq]
  field_simp [hu.ne'] <;> ring

theorem scaledKernel_tendsto (ν : ℂ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun q : ℝ => scaledKernel ν q v) atTop
      (𝓝 (Real.exp (-(v ^ 2 / 2)) : ℂ)) := by
  have hgap := scaledCoshGap_tendsto hv
  have hexp : Tendsto (fun q : ℝ => Real.exp (-q * (Real.cosh (v / Real.sqrt q) - 1)))
      atTop (𝓝 (Real.exp (-(v ^ 2 / 2)))) := by
    simpa only [neg_mul] using Real.continuous_exp.tendsto _ |>.comp hgap.neg
  have huC := Complex.continuous_ofReal.tendsto (0 : ℝ) |>.comp (scaledArgument_tendsto_zero v)
  have hcosh := Complex.continuous_cosh.tendsto (0 : ℂ) |>.comp
    (show Tendsto (fun q : ℝ => ν * ((v / Real.sqrt q : ℝ) : ℂ)) atTop (𝓝 0) from
      by simpa only [Complex.ofReal_zero, mul_zero] using huC.const_mul ν)
  have heC := Complex.continuous_ofReal.tendsto (Real.exp (-(v ^ 2 / 2))) |>.comp hexp
  simpa only [scaledKernel, Complex.cosh_zero, mul_one] using heC.mul hcosh

theorem gaussianHalf_integral :
    (∫ v in Ioi (0 : ℝ), (Real.exp (-(v ^ 2 / 2)) : ℂ)) = (Real.sqrt (Real.pi / 2) : ℂ) := by
  rw [integral_complex_ofReal]
  have he : (fun v : ℝ => Real.exp (-(v ^ 2 / 2))) =
      (fun v : ℝ => Real.exp (-(1 / 2 : ℝ) * v ^ 2)) := by
    funext v
    congr 1
    ring
  rw [he, integral_gaussian_Ioi]
  congr 1
  have hA := Real.sq_sqrt (show 0 ≤ Real.pi / (1 / 2 : ℝ) by positivity)
  have hB := Real.sq_sqrt (show 0 ≤ Real.pi / 2 by positivity)
  have hAn := Real.sqrt_nonneg (Real.pi / (1 / 2 : ℝ))
  have hBn := Real.sqrt_nonneg (Real.pi / 2)
  nlinarith only [hA, hB, hAn, hBn]

/-- Sharp leading large-q constant for the literal K at arbitrary complex order. -/
theorem complexOrderK_large_argument (ν : ℂ) :
    Tendsto (fun q : ℝ => ((Real.sqrt q * Real.exp q : ℝ) : ℂ) * complexOrderK ν q)
      atTop (𝓝 (Real.sqrt (Real.pi / 2) : ℂ)) := by
  rw [← gaussianHalf_integral]
  have hlim : Tendsto (fun q : ℝ => ∫ v in Ioi (0 : ℝ), scaledKernel ν q v)
      atTop (𝓝 (∫ v in Ioi (0 : ℝ), (Real.exp (-(v ^ 2 / 2)) : ℂ))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun v : ℝ => Real.exp (-(v ^ 2 / 4)))
    · apply Eventually.of_forall
      intro q
      have hc : Continuous (scaledKernel ν q) := by unfold scaledKernel; fun_prop
      exact hc.aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (max 1 (2 * ν.re ^ 2))] with q hq
      have hqpos : 0 < q := zero_lt_one.trans_le ((le_max_left _ _).trans hq)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact scaledKernel_norm_le_gaussian ν hqpos ((le_max_right _ _).trans hq) hv.le
    · exact gaussianMajorant_integrable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      exact scaledKernel_tendsto ν hv
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with q hq
  exact scaledKernel_integral ν hq

end
end ImbalancedChen.Part3.ComplexOrderKLargeArgument20261025a
