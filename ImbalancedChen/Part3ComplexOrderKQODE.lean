import ImbalancedChen.Part3ComplexOrderKQCalculus
import ImbalancedChen.Part3ComplexOrderKHolomorphic

/-!
# Actual modified Bessel equation at unrestricted complex order

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

A literal u-flux is differentiated, and both it and its derivative are
proved integrable. The endpoint at infinity therefore vanishes by the
native improper-integral theorem; the endpoint at zero vanishes exactly.
This yields the genuine q-moment ODE and hence the actual derivative ODE
for complexOrderK, for every complex order and positive real q.
Neither the ODE nor a K/I connection is assumed.
-/

namespace ImbalancedChen.Part3.ComplexOrderKQODE

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ComplexOrderKBridgeSourceOnly ComplexOrderKHolomorphicSourceOnly
open ComplexOrderKQCalculus RealOrderKPositiveLaplace

def qFlux (ν : ℂ) (q u : ℝ) : ℂ :=
  (Real.exp (-q * Real.cosh u) : ℂ) *
    (ν * Complex.sinh (ν * (u : ℂ)) +
      (q : ℂ) * (Real.sinh u : ℂ) * Complex.cosh (ν * (u : ℂ)))

def qFluxDerivative (ν : ℂ) (q u : ℝ) : ℂ :=
  (ν ^ 2 + (q : ℂ) ^ 2) * qMomentIntegrand 0 ν q u -
    (q : ℂ) * qMomentIntegrand 1 ν q u -
      (q : ℂ) ^ 2 * qMomentIntegrand 2 ν q u

theorem qFlux_hasDerivAt (ν : ℂ) (q u : ℝ) :
    HasDerivAt (qFlux ν q) (qFluxDerivative ν q u) u := by
  have hν : HasDerivAt (fun z : ℂ => ν * z) ν (u : ℂ) := by
    simpa only [mul_one] using (hasDerivAt_id (u : ℂ)).const_mul ν
  have hS := hν.csinh.comp_ofReal
  have hC := hν.ccosh.comp_ofReal
  have hE := (((Real.hasDerivAt_cosh u).const_mul (-q)).exp).ofReal_comp
  have hR := (Real.hasDerivAt_sinh u).ofReal_comp
  have hd := hE.mul ((hS.const_mul ν).add ((hR.const_mul (q : ℂ)).mul hC))
  have hsq : (Real.sinh u : ℂ) ^ 2 = (Real.cosh u : ℂ) ^ 2 - 1 := by
    exact_mod_cast Real.sinh_sq u
  convert hd using 1 <;>
    dsimp [qFlux, qFluxDerivative, qMomentIntegrand] <;>
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, pow_zero, pow_one, one_mul] <;>
    ring_nf <;> simp only [hsq] <;> ring

private theorem abs_sinh_le_cosh (u : ℝ) : |Real.sinh u| ≤ Real.cosh u := by
  have hp := (Real.sinh_lt_cosh (x := u)).le
  have hn := (Real.sinh_lt_cosh (x := -u)).le
  rw [Real.sinh_neg, Real.cosh_neg] at hn
  exact abs_le.mpr ⟨by linarith only [hn], hp⟩

theorem qFlux_integrable (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    IntegrableOn (qFlux ν q) (Ioi (0 : ℝ)) := by
  let f : ℝ → ℂ := fun u => (Real.exp (-q * Real.cosh u) : ℂ) * ν *
    Complex.sinh (ν * (u : ℂ))
  let g : ℝ → ℂ := fun u => (q : ℂ) * (Real.sinh u : ℂ) *
    complexOrderIntegrand ν q u
  have hf : IntegrableOn f (Ioi (0 : ℝ)) := by
    have hc : Continuous f := by dsimp [f]; fun_prop
    apply ((tiltedCoshDensity_integrable |ν.re| hq).integrableOn.const_mul ‖ν‖).mono'
      hc.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hs : ‖Complex.sinh (ν * (u : ℂ))‖ ≤ Real.exp (|ν.re| * u) := by
      apply (norm_complex_sinh_le_real_cosh _).trans
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero] using cosh_le_exp_abs_mul ν.re hu.le
    calc
      ‖f u‖ = ‖ν‖ * (Real.exp (-q * Real.cosh u) *
          ‖Complex.sinh (ν * (u : ℂ))‖) := by
        simp only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        ring
      _ ≤ ‖ν‖ * (Real.exp (-q * Real.cosh u) * Real.exp (|ν.re| * u)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le) (norm_nonneg ν)
      _ = ‖ν‖ * tiltedCoshDensity |ν.re| q u := by
        rw [← Real.exp_add]
        rfl
  have hg : IntegrableOn g (Ioi (0 : ℝ)) := by
    have hc : Continuous g := by dsimp [g, complexOrderIntegrand]; fun_prop
    apply ((qMomentIntegrand_integrable 1 ν hq).norm.const_mul |q|).mono'
      hc.aestronglyMeasurable
    filter_upwards [] with u
    have hm := mul_le_mul_of_nonneg_right (abs_sinh_le_cosh u)
      (mul_nonneg (mul_nonneg (abs_nonneg q) (Real.exp_pos (-q * Real.cosh u)).le)
        (norm_nonneg (Complex.cosh (ν * (u : ℂ)))))
    simp only [g, complexOrderIntegrand, qMomentIntegrand, pow_one, norm_mul,
      norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos u),
      abs_of_pos (Real.exp_pos _)]
    nlinarith only [hm]
  apply (hf.add hg).congr_fun _ measurableSet_Ioi
  intro u _
  dsimp [f, g, qFlux, complexOrderIntegrand]
  ring

theorem qFluxDerivative_integrable (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    IntegrableOn (qFluxDerivative ν q) (Ioi (0 : ℝ)) := by
  exact (((qMomentIntegrand_integrable 0 ν hq).const_mul (ν ^ 2 + (q : ℂ) ^ 2)).sub
    ((qMomentIntegrand_integrable 1 ν hq).const_mul (q : ℂ))).sub
      ((qMomentIntegrand_integrable 2 ν hq).const_mul ((q : ℂ) ^ 2))

theorem qFlux_tendsto_zero (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    Tendsto (qFlux ν q) atTop (𝓝 0) :=
  tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (fun u _ => qFlux_hasDerivAt ν q u)
    (qFluxDerivative_integrable ν hq) (qFlux_integrable ν hq)

theorem qFluxDerivative_integral_zero (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    (∫ u in Ioi (0 : ℝ), qFluxDerivative ν q u) = 0 := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u _ => qFlux_hasDerivAt ν q u)
    (qFluxDerivative_integrable ν hq) (qFlux_tendsto_zero ν hq)]
  simp [qFlux]

/-- Exact complex-order sign: the coefficient is q^2+nu^2. -/
theorem complexOrderK_qMoment_ODE (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    (q : ℂ) ^ 2 * qMoment 2 ν q + (q : ℂ) * qMoment 1 ν q -
      ((q : ℂ) ^ 2 + ν ^ 2) * complexOrderK ν q = 0 := by
  have h0 := qMomentIntegrand_integrable 0 ν hq
  have h1 := qMomentIntegrand_integrable 1 ν hq
  have h2 := qMomentIntegrand_integrable 2 ν hq
  have h := qFluxDerivative_integral_zero ν hq
  unfold qFluxDerivative at h
  rw [integral_sub ((h0.const_mul _).sub (h1.const_mul _)) (h2.const_mul _),
    integral_sub (h0.const_mul _) (h1.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul] at h
  change (ν ^ 2 + (q : ℂ) ^ 2) * qMoment 0 ν q -
    (q : ℂ) * qMoment 1 ν q - (q : ℂ) ^ 2 * qMoment 2 ν q = 0 at h
  rw [qMoment_zero] at h
  linear_combination -h

/-- The actual derivative ODE, with no ODE premise and no restriction on
the complex order. q remains a positive real argument. -/
theorem complexOrderK_modifiedBessel_equation (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    (q : ℂ) ^ 2 * deriv (deriv (complexOrderK ν)) q +
      (q : ℂ) * deriv (complexOrderK ν) q -
        ((q : ℂ) ^ 2 + ν ^ 2) * complexOrderK ν q = 0 := by
  rw [(deriv_complexOrderK_hasDerivAt_q ν hq).deriv,
    (complexOrderK_hasDerivAt_q ν hq).deriv]
  exact complexOrderK_qMoment_ODE ν hq

end

end ImbalancedChen.Part3.ComplexOrderKQODE
