import ImbalancedChen.Part3ComplexOrderKBridge
import ImbalancedChen.Part3RealOrderKPositiveLaplace
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Genuine q calculus of the actual K integral at every complex order

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

All q moments of the actual complexOrderK integrand are dominated on
q>=a>0 by the integrable tilted cosh density with exponent k+|Re nu|.
Dominated differentiation gives M_k'=M_(k+1) at every positive real q.
The order is unrestricted in C. This does not assume a K/I connection
or the general modified Bessel ODE; the latter requires a separate u-IBP.
-/

namespace ImbalancedChen.Part3.ComplexOrderKQCalculus

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ComplexOrderKBridgeSourceOnly RealOrderKPositiveLaplace

def qMomentIntegrand (k : ℕ) (ν : ℂ) (q u : ℝ) : ℂ :=
  (-(Real.cosh u : ℂ)) ^ k * (Real.exp (-q * Real.cosh u) : ℂ) *
    Complex.cosh (ν * (u : ℂ))

def qMoment (k : ℕ) (ν : ℂ) (q : ℝ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), qMomentIntegrand k ν q u

theorem qMoment_zero (ν : ℂ) (q : ℝ) : qMoment 0 ν q = complexOrderK ν q := by
  simp only [qMoment, qMomentIntegrand, pow_zero, one_mul, complexOrderK,
    complexOrderIntegrand]

theorem cosh_le_exp_abs_mul (a : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    Real.cosh (a * u) ≤ Real.exp (|a| * u) := by
  have hp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self a) hu)
  have hn := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_abs a) hu)
  rw [Real.cosh_eq]
  have he : -(a * u) = -a * u := by ring
  rw [he]
  linarith only [hp, hn]

theorem qMomentIntegrand_norm_le (k : ℕ) (ν : ℂ)
    {a q u : ℝ} (hq : a ≤ q) (hu : 0 ≤ u) :
    ‖qMomentIntegrand k ν q u‖ ≤
      tiltedCoshDensity ((k : ℝ) + |ν.re|) a u := by
  have hcosh : Real.cosh u ≤ Real.exp u := by
    simpa only [one_mul, abs_one] using cosh_le_exp_abs_mul 1 hu
  have hp : Real.cosh u ^ k ≤ Real.exp ((k : ℝ) * u) := by
    simpa only [Real.exp_nat_mul] using
      pow_le_pow_left₀ (Real.cosh_pos u).le hcosh k
  have hn : ‖Complex.cosh (ν * (u : ℂ))‖ ≤ Real.exp (|ν.re| * u) := by
    apply (norm_complex_cosh_le_real_cosh _).trans
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
      cosh_le_exp_abs_mul ν.re hu
  have he : Real.exp (-q * Real.cosh u) ≤ Real.exp (-a * Real.cosh u) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right hq (Real.cosh_pos u).le]
  calc
    ‖qMomentIntegrand k ν q u‖ =
        (Real.cosh u ^ k * Real.exp (-q * Real.cosh u)) *
          ‖Complex.cosh (ν * (u : ℂ))‖ := by
      simp only [qMomentIntegrand, norm_mul, norm_pow, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.cosh_pos u), abs_of_pos (Real.exp_pos _)]
    _ ≤ (Real.exp ((k : ℝ) * u) * Real.exp (-a * Real.cosh u)) *
        Real.exp (|ν.re| * u) :=
      mul_le_mul (mul_le_mul hp he (Real.exp_pos _).le (Real.exp_pos _).le) hn
        (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = tiltedCoshDensity ((k : ℝ) + |ν.re|) a u := by
      rw [← Real.exp_add, ← Real.exp_add]
      unfold tiltedCoshDensity
      congr 1
      ring

theorem qMomentIntegrand_integrable (k : ℕ) (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    IntegrableOn (qMomentIntegrand k ν q) (Ioi (0 : ℝ)) := by
  have hc : Continuous (qMomentIntegrand k ν q) := by
    unfold qMomentIntegrand
    fun_prop
  apply (tiltedCoshDensity_integrable ((k : ℝ) + |ν.re|) hq).integrableOn.mono'
    hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact qMomentIntegrand_norm_le k ν le_rfl hu.le

theorem qMomentIntegrand_hasDerivAt (k : ℕ) (ν : ℂ) (q u : ℝ) :
    HasDerivAt (fun r : ℝ => qMomentIntegrand k ν r u)
      (qMomentIntegrand (k + 1) ν q u) q := by
  have hd := (((hasDerivAt_id q).neg.mul_const (Real.cosh u)).exp).ofReal_comp
  convert (hd.const_mul ((-(Real.cosh u : ℂ)) ^ k)).mul_const
    (Complex.cosh (ν * (u : ℂ))) using 1 <;>
    dsimp [qMomentIntegrand] <;> simp only [Complex.ofReal_mul, Complex.ofReal_neg, pow_succ] <;> ring

/-- Actual dominated differentiation, with a real q parameter and complex
values. The derivative moment bound is proved for every complex order. -/
theorem qMoment_hasDerivAt (k : ℕ) (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (qMoment k ν) (qMoment (k + 1) ν q) q := by
  have ha : 0 < q / 2 := by linarith
  let bound := tiltedCoshDensity (((k + 1 : ℕ) : ℝ) + |ν.re|) (q / 2)
  have hF : ∀ᶠ r in 𝓝 q, AEStronglyMeasurable (qMomentIntegrand k ν r)
      (volume.restrict (Ioi (0 : ℝ))) := by
    apply Eventually.of_forall
    intro r
    have hc : Continuous (qMomentIntegrand k ν r) := by unfold qMomentIntegrand; fun_prop
    exact hc.aestronglyMeasurable
  have hF' : AEStronglyMeasurable (qMomentIntegrand (k + 1) ν q)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (qMomentIntegrand_integrable (k + 1) ν hq).aestronglyMeasurable
  have hbound : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ∀ r ∈ Ioi (q / 2),
      ‖qMomentIntegrand (k + 1) ν r u‖ ≤ bound u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro r hr
    exact qMomentIntegrand_norm_le (k + 1) ν hr.le hu.le
  have hdiff : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ∀ r ∈ Ioi (q / 2),
      HasDerivAt (fun x => qMomentIntegrand k ν x u)
        (qMomentIntegrand (k + 1) ν r u) r :=
    Eventually.of_forall (fun u r _ => qMomentIntegrand_hasDerivAt k ν r u)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun r u => qMomentIntegrand k ν r u)
    (F' := fun r u => qMomentIntegrand (k + 1) ν r u) (bound := bound)
    (Ioi_mem_nhds (by linarith : q / 2 < q)) hF
    (qMomentIntegrand_integrable k ν hq) hF' hbound
    (tiltedCoshDensity_integrable _ ha).integrableOn hdiff).2

theorem qMoment_continuousOn (k : ℕ) (ν : ℂ) :
    ContinuousOn (qMoment k ν) (Ioi (0 : ℝ)) := by
  intro q hq
  exact (qMoment_hasDerivAt k ν hq).continuousAt.continuousWithinAt

theorem complexOrderK_hasDerivAt_q (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (complexOrderK ν) (qMoment 1 ν q) q := by
  have he : qMoment 0 ν = complexOrderK ν := funext (qMoment_zero ν)
  rw [← he]
  exact qMoment_hasDerivAt 0 ν hq

theorem deriv_complexOrderK_hasDerivAt_q (ν : ℂ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (deriv (complexOrderK ν)) (qMoment 2 ν q) q := by
  apply (qMoment_hasDerivAt 1 ν hq).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hq] with r hr
  exact (complexOrderK_hasDerivAt_q ν hr).deriv

end

end ImbalancedChen.Part3.ComplexOrderKQCalculus
