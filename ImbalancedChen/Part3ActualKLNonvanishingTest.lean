import ImbalancedChen.Part3ActualKLCompactTestIntegrationByParts
import ImbalancedChen.Part3ComplexOrderKUniformStripDecay
import ImbalancedChen.Part3GeneralKRightEndpoint
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-25. No acceptance credit.

A fixed actual compact smooth nonnegative radial bump has a K_{i tau}
transform which is entire in complex tau and strictly nonzero at tau=0.
Actual compact radial support and the proved uniform K order-derivative
envelope justify differentiation under the integral. Measurability of
the derivative section is proved by genuine difference quotients.

The pinned isolated-zero theorem then makes the real zero set countable.
Thus the actual transform is nonzero Lebesgue almost everywhere and also
almost everywhere for the literal raw KL weight 2*tau*sinh(pi*tau)/pi^2.
No isometry, projection invariance, density or onto conclusion is assumed
or asserted. These are separate range-identification obligations.
-/

namespace ImbalancedChen.Part3.ActualKLNonvanishingTest20261025a

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
open RadialSchrodingerL2Form20261025a
open ActualKLCompactTestIntegrationByParts20261025a
open ComplexOrderKBridgeSourceOnly ComplexOrderKEntire20261025a
open ComplexOrderKUniformStripDecay20261025a
open ComplexOrderKRadialRegularitySourceOnly GeneralKRightEndpoint20261025a

def realBump : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def testFunction (r : ℝ) : ℂ := (realBump r : ℂ)

def nonvanishingTest : RadialTest where
  function := testFunction
  smooth := Complex.ofRealCLM.contDiff.comp realBump.contDiff
  compact := by
    exact realBump.hasCompactSupport.comp_left rfl

theorem realBump_nonneg (r : ℝ) : 0 ≤ realBump r := realBump.nonneg

theorem realBump_zero : realBump 0 = 1 := by
  apply realBump.one_of_mem_closedBall
  exact mem_closedBall_self (by norm_num [realBump])

theorem testFunction_zero : testFunction 0 = 1 := by simp only [testFunction, realBump_zero, Complex.ofReal_one]

private theorem support_lower {r : ℝ} (hr : testFunction r ≠ 0) : -2 ≤ r := by
  have hb : realBump r ≠ 0 := fun h => hr (by simp only [testFunction, h, Complex.ofReal_zero])
  have hmem : r ∈ Function.support realBump := hb
  rw [realBump.support_eq] at hmem
  have hnorm : |r| < 2 := by simpa only [realBump, mem_ball, Real.dist_eq, sub_zero] using hmem
  exact (abs_lt.mp hnorm).1.le

def complexTestTransform (τ : ℂ) : ℂ :=
  ∫ r : ℝ, testFunction r * radialK (τ * Complex.I) r

private def transformIntegrand (τ : ℂ) (r : ℝ) : ℂ :=
  testFunction r * radialK (τ * Complex.I) r

theorem complexTestTransform_eq_actual (τ : ℝ) :
    complexTestTransform (τ : ℂ) = actualKtransform nonvanishingTest.function τ := rfl

private theorem integrand_continuous (τ : ℂ) : Continuous (transformIntegrand τ) :=
  nonvanishingTest.smooth.continuous.mul (radialK_C2 (τ * Complex.I)).continuous

private theorem integrand_integrable (τ : ℂ) : Integrable (transformIntegrand τ) :=
  (integrand_continuous τ).integrable_of_hasCompactSupport nonvanishingTest.compact.mul_right

private theorem integrand_differentiable (r : ℝ) :
    Differentiable ℂ (fun τ : ℂ => transformIntegrand τ r) := by
  have hk := complexOrderK_differentiable_all (Real.exp_pos r)
  have hp : Differentiable ℂ (fun τ : ℂ => τ * Complex.I) := differentiable_id.mul_const _
  exact (hk.comp hp).const_mul (testFunction r)

private theorem integrand_deriv (τ : ℂ) (r : ℝ) :
    deriv (fun ζ : ℂ => transformIntegrand ζ r) τ =
      testFunction r *
        (deriv (fun ν : ℂ => complexOrderK ν (Real.exp r)) (τ * Complex.I) * Complex.I) := by
  have hk := (complexOrderK_differentiable_all (Real.exp_pos r) (τ * Complex.I)).hasDerivAt
  have hp := (hasDerivAt_id τ).mul_const Complex.I
  exact ((hk.comp τ hp).const_mul (testFunction r)).deriv

private theorem derivative_section_measurable (τ0 : ℂ) :
    AEStronglyMeasurable (fun r : ℝ => deriv (fun τ : ℂ => transformIntegrand τ r) τ0) volume := by
  let δ : ℕ → ℂ := fun n => ((1 / ((n : ℝ) + 2) : ℝ) : ℂ)
  have hδpos (n : ℕ) : 0 < 1 / ((n : ℝ) + 2) := by positivity
  have hreal : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_natCast_atTop_atTop.add_const 2).const_div_atTop 1
  have hδ : Tendsto δ atTop (𝓝 (0 : ℂ)) := by
    simpa only [δ, Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hδNE : Tendsto δ atTop (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hδ, Eventually.of_forall (fun n => ?_)⟩
    exact Complex.ofReal_ne_zero.mpr (hδpos n).ne'
  let Q : ℕ → ℝ → ℂ := fun n r => (δ n)⁻¹ *
    (transformIntegrand (τ0 + δ n) r - transformIntegrand τ0 r)
  have hQ (n : ℕ) : AEStronglyMeasurable (Q n) volume :=
    aestronglyMeasurable_const.mul
      ((integrand_continuous (τ0 + δ n)).aestronglyMeasurable.sub
        (integrand_continuous τ0).aestronglyMeasurable)
  have hlim : ∀ᵐ r : ℝ, Tendsto (fun n => Q n r) atTop
      (𝓝 (deriv (fun τ : ℂ => transformIntegrand τ r) τ0)) := by
    exact Eventually.of_forall (fun r => by
      simpa only [Q, smul_eq_mul, Function.comp_def] using
        ((integrand_differentiable r) τ0).hasDerivAt.tendsto_slope_zero.comp hδNE)
  exact aestronglyMeasurable_of_tendsto_ae atTop hQ hlim

private theorem integrand_deriv_uniform_bound (τ0 τ : ℂ) (hτ : τ ∈ ball τ0 1) (r : ℝ) :
    ‖deriv (fun ζ : ℂ => transformIntegrand ζ r) τ‖ ≤
      stripDecayConstant 1 (Real.exp (-2)) (‖τ0‖ + 1) * ‖testFunction r‖ := by
  by_cases hr : testFunction r = 0
  · rw [integrand_deriv, hr]
    simp
  · have hq : Real.exp (-2) ≤ Real.exp r := Real.exp_le_exp.mpr (support_lower hr)
    have hτnorm : ‖τ‖ ≤ ‖τ0‖ + 1 := by
      have hdist : ‖τ - τ0‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hτ
      calc
        ‖τ‖ = ‖(τ - τ0) + τ0‖ := by congr 1; ring
        _ ≤ ‖τ - τ0‖ + ‖τ0‖ := norm_add_le _ _
        _ ≤ ‖τ0‖ + 1 := by linarith
    have hstrip : |(τ * Complex.I).re| ≤ ‖τ0‖ + 1 := by
      apply (Complex.abs_re_le_norm (τ * Complex.I)).trans
      simpa only [norm_mul, Complex.norm_I, mul_one] using hτnorm
    have hk := complexOrderK_orderDeriv_uniform_exp_bound (Real.exp_pos (-2)) hq hstrip
    have hexp : Real.exp (-(Real.exp r / 2)) ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr
        (neg_nonpos.mpr (div_nonneg (Real.exp_pos r).le (by norm_num : (0 : ℝ) ≤ 2)))
    have hkC : ‖deriv (fun ν : ℂ => complexOrderK ν (Real.exp r)) (τ * Complex.I)‖ ≤
        stripDecayConstant 1 (Real.exp (-2)) (‖τ0‖ + 1) := by
      exact hk.trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp
          (stripDecayConstant_pos 1 (Real.exp (-2)) (‖τ0‖ + 1)).le)
    rw [integrand_deriv, norm_mul, norm_mul, Complex.norm_I, mul_one]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hkC (norm_nonneg (testFunction r))

/-- Actual complex differentiability of the compact-bump K transform.
The uniform order bound, derivative measurability and integrable compact
majorant are all proved on the literal integrand. -/
theorem complexTestTransform_differentiable : Differentiable ℂ complexTestTransform := by
  intro τ0
  let C : ℝ := stripDecayConstant 1 (Real.exp (-2)) (‖τ0‖ + 1)
  have hboundInt : Integrable (fun r : ℝ => C * ‖testFunction r‖) :=
    (nonvanishingTest.smooth.continuous.norm.integrable_of_hasCompactSupport
      nonvanishingTest.compact.norm).const_mul C
  have hFmeas : ∀ᶠ τ in 𝓝 τ0, AEStronglyMeasurable (transformIntegrand τ) volume :=
    Eventually.of_forall (fun τ => (integrand_continuous τ).aestronglyMeasurable)
  have hbound : ∀ᵐ r : ℝ, ∀ τ ∈ ball τ0 1,
      ‖deriv (fun ζ : ℂ => transformIntegrand ζ r) τ‖ ≤ C * ‖testFunction r‖ :=
    Eventually.of_forall (fun r τ hτ => integrand_deriv_uniform_bound τ0 τ hτ r)
  have hdiff : ∀ᵐ r : ℝ, ∀ τ ∈ ball τ0 1,
      HasDerivAt (fun ζ : ℂ => transformIntegrand ζ r)
        (deriv (fun ζ : ℂ => transformIntegrand ζ r) τ) τ :=
    Eventually.of_forall (fun r τ _ => ((integrand_differentiable r) τ).hasDerivAt)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := transformIntegrand)
    (F' := fun τ r => deriv (fun ζ : ℂ => transformIntegrand ζ r) τ)
    (bound := fun r => C * ‖testFunction r‖) (ball_mem_nhds τ0 (by norm_num : (0 : ℝ) < 1))
    hFmeas (integrand_integrable τ0) (derivative_section_measurable τ0)
    hbound hboundInt hdiff).2.differentiableAt

theorem complexTestTransform_entire : AnalyticOnNhd ℂ complexTestTransform univ :=
  fun τ _ => complexTestTransform_differentiable.analyticAt τ

/-- At zero the actual transform is a strictly positive K0 integral. -/
theorem complexTestTransform_zero_re_pos : 0 < (complexTestTransform 0).re := by
  let g : ℝ → ℝ := fun r => realBump r * (radialK (0 : ℂ) r).re
  have hc : Continuous g :=
    realBump.continuous.mul (Complex.continuous_re.comp (radialK_C2 0).continuous)
  have hi : Integrable g := hc.integrable_of_hasCompactSupport realBump.hasCompactSupport.mul_right
  have hn : ∀ r : ℝ, 0 ≤ g r := fun r =>
    mul_nonneg (realBump_nonneg r) (radialK_real_re_pos 0 r).le
  have hg0 : 0 < g 0 := by simpa only [g, realBump_zero, one_mul] using radialK_real_re_pos 0 0
  have hpos : 0 < ∫ r : ℝ, g r := by
    apply (integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hn) hi).2
    exact IsOpen.measure_pos volume hc.isOpen_support ⟨0, hg0.ne'⟩
  rw [complexTestTransform, ← integral_re (integrand_integrable 0)]
  simpa only [transformIntegrand, zero_mul, testFunction, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, g] using hpos

theorem complexTestTransform_zero_ne : complexTestTransform 0 ≠ 0 := by
  intro hz
  have h := complexTestTransform_zero_re_pos
  rw [hz, Complex.zero_re] at h
  exact (lt_irrefl 0) h

theorem complexTestTransform_zeros_countable : {τ : ℂ | complexTestTransform τ = 0}.Countable := by
  have hcod := complexTestTransform_entire.preimage_zero_mem_codiscrete complexTestTransform_zero_ne
  change ({τ : ℂ | complexTestTransform τ = 0}ᶜ) ∈ codiscrete ℂ at hcod
  have hclosed : IsClosed {τ : ℂ | complexTestTransform τ = 0} ∧
      IsDiscrete {τ : ℂ | complexTestTransform τ = 0} := by
    exact compl_mem_codiscrete_iff.mp hcod
  exact hclosed.1.isLindelof.countable_of_isDiscrete hclosed.2

theorem actualKtransform_test_zeros_countable :
    {τ : ℝ | actualKtransform nonvanishingTest.function τ = 0}.Countable := by
  have h := complexTestTransform_zeros_countable.preimage Complex.ofReal_injective
  simpa only [preimage_setOf_eq, complexTestTransform_eq_actual] using h

theorem actualKtransform_test_nonzero_ae :
    ∀ᵐ τ : ℝ, actualKtransform nonvanishingTest.function τ ≠ 0 := by
  rw [ae_iff]
  simpa only [not_not] using actualKtransform_test_zeros_countable.measure_zero volume

/-- The same actual test is nonvanishing almost everywhere for the literal
positive raw KL measure; this asserts no transform isometry or onto map. -/
theorem actualKtransform_test_nonzero_rawKL_ae :
    ∀ᵐ τ : ℝ ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun τ : ℝ => ENNReal.ofReal ((2 / Real.pi ^ 2) * τ * Real.sinh (Real.pi * τ)))),
      actualKtransform nonvanishingTest.function τ ≠ 0 := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_of_ae actualKtransform_test_nonzero_ae)

end
end ImbalancedChen.Part3.ActualKLNonvanishingTest20261025a
