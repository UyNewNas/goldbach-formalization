import ImbalancedChen.Part3ComplexOrderKQCalculus
import ImbalancedChen.Part3ComplexOrderKRadialRegularity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-25. No acceptance credit.

Actual general-order K right endpoints from its literal cosh-Laplace
moments. The constants are finite integrals of actual moment norms at
q=1; no tail bound, endpoint limit or L2 hypothesis is supplied.

For every complex order, all fixed q moments decay like exp(1-q) on
q>=1. Absorbing q into half this exponential proves decay of the actual
native log derivative. K(exp r) and its native derivative both tend to
zero and belong to L2(dr) on r>0. Actual K is strictly positive at every
real order and q>0. These are right-endpoint inputs for the Green kernel;
no Schur bound or spectral identity is asserted here.
-/

namespace ImbalancedChen.Part3.GeneralKRightEndpoint20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ComplexOrderKBridgeSourceOnly ComplexOrderKQCalculus
open ComplexOrderKRadialRegularitySourceOnly
open RealOrderKExceptionalSourceOnly RealOrderKPositiveLaplace

/-- A genuine finite constant from the actual q=1 moment integrand. -/
def momentMass (k : ℕ) (ν : ℂ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), ‖qMomentIntegrand k ν 1 u‖

theorem momentMass_nonneg (k : ℕ) (ν : ℂ) : 0 ≤ momentMass k ν :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem momentMass_integrable (k : ℕ) (ν : ℂ) :
    IntegrableOn (fun u : ℝ => ‖qMomentIntegrand k ν 1 u‖) (Ioi 0) :=
  (qMomentIntegrand_integrable k ν (by norm_num : (0 : ℝ) < 1)).norm

private theorem qMomentIntegrand_split (k : ℕ) (ν : ℂ) (q u : ℝ) :
    qMomentIntegrand k ν q u =
      (Real.exp (-(q - 1) * Real.cosh u) : ℂ) * qMomentIntegrand k ν 1 u := by
  have he : Real.exp (-q * Real.cosh u) =
      Real.exp (-(q - 1) * Real.cosh u) * Real.exp (-1 * Real.cosh u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp only [qMomentIntegrand]
  rw [he, Complex.ofReal_mul]
  ring

/-- The entire complex order is unrestricted. The q decay is obtained
from cosh(u)>=1, keeping the genuinely integrable q=1 factor. -/
theorem qMomentIntegrand_norm_exp_bound (k : ℕ) (ν : ℂ)
    {q : ℝ} (hq : 1 ≤ q) (u : ℝ) :
    ‖qMomentIntegrand k ν q u‖ ≤
      Real.exp (1 - q) * ‖qMomentIntegrand k ν 1 u‖ := by
  rw [qMomentIntegrand_split, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hcosh : 1 ≤ Real.cosh u := Real.one_le_cosh u
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hcosh)]

/-- Explicit exp(-q) decay of every actual differentiated K moment. -/
theorem qMoment_norm_exp_bound (k : ℕ) (ν : ℂ) {q : ℝ} (hq : 1 ≤ q) :
    ‖qMoment k ν q‖ ≤ Real.exp (1 - q) * momentMass k ν := by
  calc
    ‖qMoment k ν q‖ ≤ ∫ u in Ioi (0 : ℝ), ‖qMomentIntegrand k ν q u‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioi (0 : ℝ), Real.exp (1 - q) * ‖qMomentIntegrand k ν 1 u‖ := by
      apply integral_mono (qMomentIntegrand_integrable k ν (by linarith)).norm
        ((momentMass_integrable k ν).const_mul (Real.exp (1 - q)))
      exact qMomentIntegrand_norm_exp_bound k ν hq
    _ = Real.exp (1 - q) * momentMass k ν := by
      rw [integral_const_mul]
      rfl

theorem complexOrderK_norm_exp_bound (ν : ℂ) {q : ℝ} (hq : 1 ≤ q) :
    ‖complexOrderK ν q‖ ≤ Real.exp (1 - q) * momentMass 0 ν := by
  simpa only [qMoment_zero] using qMoment_norm_exp_bound 0 ν hq

private theorem q_mul_exp_bound (q : ℝ) :
    q * Real.exp (1 - q) ≤ 2 * Real.exp 1 * Real.exp (-q / 2) := by
  have hq : q ≤ 2 * Real.exp (q / 2) := by
    have := Real.add_one_le_exp (q / 2)
    linarith
  calc
    q * Real.exp (1 - q) ≤ 2 * Real.exp (q / 2) * Real.exp (1 - q) :=
      mul_le_mul_of_nonneg_right hq (Real.exp_pos _).le
    _ = 2 * Real.exp 1 * Real.exp (-q / 2) := by
      rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The actual native Euler derivative q*K'(q) has exponential decay. -/
theorem q_deriv_complexOrderK_exp_bound (ν : ℂ) {q : ℝ} (hq : 1 ≤ q) :
    ‖(q : ℂ) * deriv (complexOrderK ν) q‖ ≤
      (2 * Real.exp 1 * momentMass 1 ν) * Real.exp (-q / 2) := by
  have hqpos : 0 < q := by linarith
  rw [(complexOrderK_hasDerivAt_q ν hqpos).deriv, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos]
  calc
    q * ‖qMoment 1 ν q‖ ≤ q * (Real.exp (1 - q) * momentMass 1 ν) :=
      mul_le_mul_of_nonneg_left (qMoment_norm_exp_bound 1 ν hq) hqpos.le
    _ ≤ (2 * Real.exp 1 * momentMass 1 ν) * Real.exp (-q / 2) := by
      have h := mul_le_mul_of_nonneg_right (q_mul_exp_bound q) (momentMass_nonneg 1 ν)
      nlinarith only [h]

/-- Actual K positivity for every real order, using the already proved
full-line tilted Laplace convergence; no exceptional strip is needed. -/
theorem actualRealOrderK_pos (α : ℝ) {q : ℝ} (hq : 0 < q) : 0 < realOrderK α q := by
  have hint : IntegrableOn (realOrderIntegrand α q) (Ioi (0 : ℝ)) := by
    have h := (((tiltedCoshDensity_integrable (-α) hq).integrableOn).add
      (tiltedCoshDensity_integrable α hq).integrableOn).div_const 2
    apply h.congr_fun _ measurableSet_Ioi
    intro u _
    rw [tiltedCoshDensity_pair]
    ring
  have hc : Continuous (realOrderIntegrand α q) := by
    unfold realOrderIntegrand
    fun_prop
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] realOrderIntegrand α q :=
    ae_of_all _ (fun u => mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le)
  apply (setIntegral_pos_iff_support_of_nonneg_ae hn hint).2
  have hopen : IsOpen (Function.support (realOrderIntegrand α q) ∩ Ioi (0 : ℝ)) :=
    hc.isOpen_support.inter isOpen_Ioi
  have hmem : (1 : ℝ) ∈ Function.support (realOrderIntegrand α q) ∩ Ioi 0 := by
    constructor
    · change realOrderIntegrand α q 1 ≠ 0
      exact (mul_pos (Real.exp_pos _) (Real.cosh_pos _)).ne'
    · norm_num
  exact IsOpen.measure_pos volume hopen ⟨1, hmem⟩

theorem radialK_real_re_pos (α r : ℝ) : 0 < (radialK (α : ℂ) r).re := by
  simpa only [radialK, complexOrderK_real, Complex.ofReal_re] using
    actualRealOrderK_pos α (Real.exp_pos r)

theorem radialK_real_im_zero (α r : ℝ) : (radialK (α : ℂ) r).im = 0 := by
  simp only [radialK, complexOrderK_real, Complex.ofReal_im]

/-- A concrete exponential dr envelope for the actual K(exp r) value. -/
theorem radialK_norm_exp_bound (ν : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ‖radialK ν r‖ ≤ momentMass 0 ν * Real.exp (-(r / 2)) := by
  have hq : 1 ≤ Real.exp r := by simpa using Real.exp_le_exp.mpr hr
  have hb := complexOrderK_norm_exp_bound ν hq
  have he : 1 - Real.exp r ≤ -(r / 2) := by
    have := Real.add_one_le_exp r
    linarith
  exact hb.trans (by
    have h := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) (momentMass_nonneg 0 ν)
    simpa only [radialK, mul_comm] using h)

/-- A genuine envelope for the native log derivative, not a boundary
condition assumed for a Green kernel. -/
theorem radialK_deriv_norm_exp_bound (ν : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ‖deriv (radialK ν) r‖ ≤
      (2 * Real.exp 1 * momentMass 1 ν) * Real.exp (-(r / 2)) := by
  have hq : 1 ≤ Real.exp r := by simpa using Real.exp_le_exp.mpr hr
  have hd : deriv (radialK ν) r =
      (Real.exp r : ℂ) * deriv (complexOrderK ν) (Real.exp r) := by
    rw [(radialK_hasDerivAt ν r).deriv,
      (complexOrderK_hasDerivAt_q ν (Real.exp_pos r)).deriv]
    rfl
  rw [hd]
  apply (q_deriv_complexOrderK_exp_bound ν hq).trans
  have hC : 0 ≤ 2 * Real.exp 1 * momentMass 1 ν :=
    mul_nonneg (by positivity) (momentMass_nonneg 1 ν)
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  have := Real.add_one_le_exp r
  linarith

private theorem exp_half_tendsto_zero :
    Tendsto (fun r : ℝ => Real.exp (-(r / 2))) atTop (𝓝 0) := by
  have he : (fun r : ℝ => (-(1 / 2) : ℝ) * r) = fun r : ℝ => -(r / 2) := by
    funext r
    ring
  have hlinear : Tendsto (fun r : ℝ => (-(1 / 2) : ℝ) * r) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by norm_num : (-(1 / 2) : ℝ) < 0)
  rw [he] at hlinear
  exact Real.tendsto_exp_atBot.comp hlinear

theorem radialK_tendsto_zero (ν : ℂ) : Tendsto (radialK ν) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    exact radialK_norm_exp_bound ν hr)
  simpa only [mul_zero] using (tendsto_const_nhds.mul exp_half_tendsto_zero
    : Tendsto (fun r : ℝ => momentMass 0 ν * Real.exp (-(r / 2))) atTop (𝓝 _))

theorem radialK_deriv_tendsto_zero (ν : ℂ) :
    Tendsto (deriv (radialK ν)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    exact radialK_deriv_norm_exp_bound ν hr)
  simpa only [mul_zero] using (tendsto_const_nhds.mul exp_half_tendsto_zero
    : Tendsto (fun r : ℝ => (2 * Real.exp 1 * momentMass 1 ν) *
      Real.exp (-(r / 2))) atTop (𝓝 _))

private theorem memLp_two_of_exp_bound (f : ℝ → ℂ) (hf : Continuous f) (C : ℝ)
    (hbound : ∀ r : ℝ, 0 ≤ r → ‖f r‖ ≤ C * Real.exp (-(r / 2))) :
    MemLp f 2 (volume.restrict (Ioi (0 : ℝ))) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).2
  have he : IntegrableOn (fun r : ℝ => C ^ 2 * Real.exp (-r)) (Ioi 0) := by
    simpa only [neg_one_mul] using
      (integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0).const_mul (C ^ 2)
  apply he.mono' (hf.norm.pow 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hsq := pow_le_pow_left₀ (norm_nonneg (f r)) (hbound r hr.le) 2
  have hexp : (Real.exp (-(r / 2))) ^ 2 = Real.exp (-r) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [mul_pow, hexp] at hsq
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f r‖)] using hsq

theorem radialK_memLp_two_Ioi (ν : ℂ) :
    MemLp (radialK ν) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  memLp_two_of_exp_bound _ (radialK_C2 ν).continuous _
    (fun r hr => radialK_norm_exp_bound ν hr)

theorem radialK_deriv_memLp_two_Ioi (ν : ℂ) :
    MemLp (deriv (radialK ν)) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hd : deriv (radialK ν) = fun r : ℝ => Real.exp r • radialMoment 1 ν r := by
    funext r
    exact (radialK_hasDerivAt ν r).deriv
  have hc : Continuous (deriv (radialK ν)) := by
    rw [hd]
    exact Real.continuous_exp.smul (radialMoment_continuous 1 ν)
  exact memLp_two_of_exp_bound _ hc _ (fun r hr => radialK_deriv_norm_exp_bound ν hr)

end
end ImbalancedChen.Part3.GeneralKRightEndpoint20261025a
