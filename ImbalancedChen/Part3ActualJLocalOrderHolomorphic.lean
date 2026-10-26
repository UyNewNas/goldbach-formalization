import ImbalancedChen.Part3GeneralJSymmetricPoissonIntegral
import ImbalancedChen.Part3JBesselPoissonEvenMoments
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual order holomorphy near order zero of the original reciprocal-Gamma J.
The symmetric Poisson integral is consumed at its actual normalization.
Its literal order derivative has the extra factor log(1-t^2). On Re nu>-1/4
this is dominated by 8 times the integrable Poisson weight of order -3/8.
The endpoint domination, measurability and derivative under the integral are
proved here; no J-analyticity or differentiation supplier is assumed.

This file asserts no normalization for an automorphic Kuznetsov kernel.
-/

namespace ImbalancedChen.Part3.ActualJLocalOrderHolomorphic20261026a

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open ActualGeneralJBesselSourceOnly GeneralJSymmetricPoissonIntegralSourceOnly
open JBesselPoissonEvenMoments20261025a

def orderHalfPlane : Set ℂ := {nu | -(1 / 4 : ℝ) < nu.re}

/-- The global measurable representative agrees with the actual Poisson
integrand on the open integration interval. -/
def orderPoissonIntegrand (nu : ℂ) (q t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (q : ℂ) * (t : ℂ)) *
    Complex.exp ((Real.log (1 - t ^ 2) : ℂ) * (nu - 1 / 2))

def orderPoissonDerivIntegrand (nu : ℂ) (q t : ℝ) : ℂ :=
  (Real.log (1 - t ^ 2) : ℂ) * orderPoissonIntegrand nu q t

def orderPoissonIntegral (nu : ℂ) (q : ℝ) : ℂ :=
  ∫ t in Ioo (-1 : ℝ) 1, orderPoissonIntegrand nu q t

def orderPoissonDeriv (nu : ℂ) (q : ℝ) : ℂ :=
  ∫ t in Ioo (-1 : ℝ) 1, orderPoissonDerivIntegrand nu q t

private theorem base_pos {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    0 < 1 - t ^ 2 := by
  have h := (abs_lt.mpr ht)
  nlinarith [sq_abs t, abs_nonneg t]

theorem orderPoissonIntegrand_eq (nu : ℂ) (q : ℝ)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    orderPoissonIntegrand nu q t = jSymmetricPoissonIntegrand nu q t := by
  have hx := base_pos ht
  rw [orderPoissonIntegrand, jSymmetricPoissonIntegrand,
    jSymmetricPoissonWeight]
  congr 1
  rw [show 1 - (t : ℂ) ^ (2 : ℕ) = ((1 - t ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le]

private theorem integrand_measurable (nu : ℂ) (q : ℝ) :
    AEStronglyMeasurable (orderPoissonIntegrand nu q)
      (volume.restrict (Ioo (-1 : ℝ) 1)) := by
  unfold orderPoissonIntegrand
  exact (by fun_prop : Measurable (fun t : ℝ =>
    Complex.exp (Complex.I * (q : ℂ) * (t : ℂ)) *
      Complex.exp ((Real.log (1 - t ^ 2) : ℂ) * (nu - 1 / 2)))).aestronglyMeasurable

private theorem deriv_integrand_measurable (nu : ℂ) (q : ℝ) :
    AEStronglyMeasurable (orderPoissonDerivIntegrand nu q)
      (volume.restrict (Ioo (-1 : ℝ) 1)) := by
  unfold orderPoissonDerivIntegrand orderPoissonIntegrand
  exact (by fun_prop : Measurable (fun t : ℝ =>
    (Real.log (1 - t ^ 2) : ℂ) *
      (Complex.exp (Complex.I * (q : ℂ) * (t : ℂ)) *
      Complex.exp ((Real.log (1 - t ^ 2) : ℂ) * (nu - 1 / 2))))).aestronglyMeasurable

theorem orderPoisson_integrable {nu : ℂ} (hnu : -(1 / 2 : ℝ) < nu.re) (q : ℝ) :
    IntegrableOn (orderPoissonIntegrand nu q) (Ioo (-1 : ℝ) 1) := by
  have h := (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (by norm_num : (-1 : ℝ) ≤ 1)).1 (jSymmetricPoissonIntegrand_integrable hnu q)
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact (orderPoissonIntegrand_eq nu q ht).symm

theorem orderPoissonIntegral_eq (nu : ℂ) (q : ℝ) :
    orderPoissonIntegral nu q = jSymmetricPoissonIntegral nu q := by
  rw [orderPoissonIntegral, jSymmetricPoissonIntegral,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact orderPoissonIntegrand_eq nu q ht

def orderDerivativeEnvelope (t : ℝ) : ℝ :=
  8 * ‖poissonWeight (-3 / 8 : ℂ) t‖

theorem orderDerivativeEnvelope_integrable :
    IntegrableOn orderDerivativeEnvelope (Ioo (-1 : ℝ) 1) := by
  exact (poissonWeight_integrable (nu := (-3 / 8 : ℂ)) (by norm_num)).norm.const_mul 8

/-- Explicit endpoint logarithmic domination, uniform on the actual order
half-plane and in every real argument q. -/
theorem orderPoissonDerivIntegrand_norm_le {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    (q : ℝ) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ‖orderPoissonDerivIntegrand nu q t‖ ≤ orderDerivativeEnvelope t := by
  have hx := base_pos ht
  have hx1 : 1 - t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
  let u : ℝ := -Real.log (1 - t ^ 2)
  have hlog : Real.log (1 - t ^ 2) ≤ 0 := Real.log_nonpos hx.le hx1
  have hu : 0 ≤ u := neg_nonneg.mpr hlog
  have hphase : ‖Complex.exp (Complex.I * (q : ℂ) * (t : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hw : ‖poissonWeight (-3 / 8 : ℂ) t‖ = Real.exp (7 * u / 8) := by
    rw [poissonWeight, Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le,
      Complex.norm_exp]
    congr 1
    dsimp [u]
    simp only [Complex.mul_re, Complex.sub_re, Complex.div_re,
      Complex.ofReal_re, Complex.ofReal_im]
    norm_num
    ring
  have he : ‖orderPoissonDerivIntegrand nu q t‖ =
      u * Real.exp (u * (1 / 2 - nu.re)) := by
    simp only [orderPoissonDerivIntegrand, orderPoissonIntegrand, norm_mul,
      hphase, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos hlog, Complex.norm_exp]
    congr 2
    dsimp [u]
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.div_re, Complex.ofNat_re, Complex.ofNat_im, Complex.one_re, Complex.one_im]
    norm_num
    ring
  have hexp : Real.exp (u * (1 / 2 - nu.re)) ≤ Real.exp (3 * u / 4) := by
    apply Real.exp_le_exp.mpr
    have hRe : -(1 / 4 : ℝ) < nu.re := hnu
    nlinarith [mul_le_mul_of_nonneg_left hRe.le hu]
  have hd : u ≤ 8 * Real.exp (u / 8) := by
    have h := Real.add_one_le_exp (u / 8)
    linarith
  rw [he, orderDerivativeEnvelope, hw]
  calc
    u * Real.exp (u * (1 / 2 - nu.re)) ≤ u * Real.exp (3 * u / 4) :=
      mul_le_mul_of_nonneg_left hexp hu
    _ ≤ (8 * Real.exp (u / 8)) * Real.exp (3 * u / 4) :=
      mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le
    _ = 8 * Real.exp (7 * u / 8) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2 <;> ring

theorem orderPoissonIntegrand_hasDerivAt (nu : ℂ) (q t : ℝ) :
    HasDerivAt (fun z : ℂ => orderPoissonIntegrand z q t)
      (orderPoissonDerivIntegrand nu q t) nu := by
  have h := (((hasDerivAt_id nu).sub_const (1 / 2)).const_mul
    (Real.log (1 - t ^ 2) : ℂ)).cexp.const_mul
      (Complex.exp (Complex.I * (q : ℂ) * (t : ℂ)))
  convert h using 1 <;>
    dsimp [orderPoissonIntegrand, orderPoissonDerivIntegrand] <;> ring

/-- Actual dominated complex order differentiation, including all endpoint
and measurability obligations. -/
theorem orderPoissonIntegral_hasDerivAt {nu : ℂ} (hnu : nu ∈ orderHalfPlane) (q : ℝ) :
    HasDerivAt (fun z : ℂ => orderPoissonIntegral z q) (orderPoissonDeriv nu q) nu := by
  have hopen : IsOpen orderHalfPlane :=
    isOpen_lt continuous_const Complex.continuous_re
  have hmeas : ∀ᶠ z in 𝓝 nu, AEStronglyMeasurable (orderPoissonIntegrand z q)
      (volume.restrict (Ioo (-1 : ℝ) 1)) :=
    Eventually.of_forall (fun z => integrand_measurable z q)
  have hbound : ∀ᵐ t ∂volume.restrict (Ioo (-1 : ℝ) 1), ∀ z ∈ orderHalfPlane,
      ‖orderPoissonDerivIntegrand z q t‖ ≤ orderDerivativeEnvelope t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact fun z hz => orderPoissonDerivIntegrand_norm_le hz q ht
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioo (-1 : ℝ) 1), ∀ z ∈ orderHalfPlane,
      HasDerivAt (fun w : ℂ => orderPoissonIntegrand w q t)
        (orderPoissonDerivIntegrand z q t) z :=
    Eventually.of_forall (fun t z _ => orderPoissonIntegrand_hasDerivAt z q t)
  have hnu' : -(1 / 2 : ℝ) < nu.re := by
    change -(1 / 4 : ℝ) < nu.re at hnu
    linarith
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioo (-1 : ℝ) 1))
    (F := fun z t => orderPoissonIntegrand z q t)
    (F' := fun z t => orderPoissonDerivIntegrand z q t)
    (bound := orderDerivativeEnvelope)
    (hopen.mem_nhds hnu) hmeas (orderPoisson_integrable hnu' q)
    (deriv_integrand_measurable nu q) hbound orderDerivativeEnvelope_integrable hdiff).2

/-- The actual J order derivative; the first summand differentiates the
principal power, the second the Gamma factor, the third the actual integral. -/
def actualJOrderDerivative (nu : ℂ) (q : ℝ) : ℂ :=
  let p := (((q / 2 : ℝ) : ℂ) ^ nu)
  let g := (Real.sqrt Real.pi : ℂ) * Complex.Gamma (nu + 1 / 2)
  ((p * Complex.log (((q / 2 : ℝ) : ℂ))) * g -
    p * ((Real.sqrt Real.pi : ℂ) * deriv Complex.Gamma (nu + 1 / 2))) / g ^ 2 *
      orderPoissonIntegral nu q + (p / g) * orderPoissonDeriv nu q

theorem generalJ_order_hasDerivAt {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun z : ℂ => generalJ z q) (actualJOrderDerivative nu q) nu := by
  have hpos : 0 < (nu + 1 / 2).re := by
    change -(1 / 4 : ℝ) < nu.re at hnu
    simp only [Complex.add_re]
    norm_num
    linarith
  have hp := (Complex.hasStrictDerivAt_const_cpow
    (x := (((q / 2 : ℝ) : ℂ))) (y := nu)
    (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity : (q / 2 : ℝ) ≠ 0)))).hasDerivAt
  have hg := ((Complex.differentiableAt_Gamma (nu + 1 / 2) (fun n hn => by
    have hh := congrArg Complex.re hn
    simp only [Complex.neg_re, Complex.natCast_re] at hh
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)).hasDerivAt.comp nu ((hasDerivAt_id nu).add_const (1 / 2))).const_mul
      (Real.sqrt Real.pi : ℂ)
  have hgnz : (Real.sqrt Real.pi : ℂ) * Complex.Gamma (nu + 1 / 2) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 Real.pi_pos).ne')
      (Complex.Gamma_ne_zero_of_re_pos hpos)
  have h := (hp.div hg hgnz).mul (orderPoissonIntegral_hasDerivAt hnu q)
  have hrepr : (fun z : ℂ => generalJ z q) =ᶠ[𝓝 nu]
      (fun z : ℂ => (((q / 2 : ℝ) : ℂ) ^ z) /
        ((Real.sqrt Real.pi : ℂ) * Complex.Gamma (z + 1 / 2)) * orderPoissonIntegral z q) := by
    have hopen : IsOpen orderHalfPlane := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hnu] with z hz
    have hz' : -(1 / 2 : ℝ) < z.re := by change -(1 / 4 : ℝ) < z.re at hz; linarith
    rw [orderPoissonIntegral_eq]
    exact generalJ_eq_symmetric_poisson_integral hz' hq
  exact (by simpa only [actualJOrderDerivative] using h).congr_of_eventuallyEq hrepr

theorem generalJ_order_differentiableOn {q : ℝ} (hq : 0 < q) :
    DifferentiableOn ℂ (fun nu : ℂ => generalJ nu q) orderHalfPlane :=
  fun _ hnu => (generalJ_order_hasDerivAt hnu hq).differentiableAt.differentiableWithinAt

theorem generalJ_order_analyticAt {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) : AnalyticAt ℂ (fun z : ℂ => generalJ z q) nu :=
  (generalJ_order_differentiableOn hq).analyticAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hnu)

theorem generalJ_order_deriv_zero {q : ℝ} (hq : 0 < q) :
    deriv (fun nu : ℂ => generalJ nu q) 0 = actualJOrderDerivative 0 q :=
  (generalJ_order_hasDerivAt (by norm_num [orderHalfPlane]) hq).deriv

end
end ImbalancedChen.Part3.ActualJLocalOrderHolomorphic20261026a
