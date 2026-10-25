import ImbalancedChen.Part3Gamma0ActualUnboundedScalarMeasure
import ImbalancedChen.Part3Gamma0ActualHeatGenerator
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Scalar heat coefficients of the ACTUAL Gamma0 heat semigroup equal the
Laplace transforms of the SAME actual unbounded scalar measures, for all
nonnegative times, including zero. The equality follows from the actual
CFC heat multiplier and the proved actual zero-fiber theorem.

For EVERY physical quotient vector, with no operator-domain assumption,
the coefficient is differentiable at each positive time. A genuine local
bound lambda exp(-s lambda) <= 2/t for s>t/2 gives an integrable constant
under the actual finite nonnegative measure. The derivative under the
integral is therefore proved, not supplied as a heat-measure identity or
a differentiation premise. Positivity, the norm-squared bound, and time
monotonicity are also derived. No generic smoothing theorem is reproved.
-/

namespace ImbalancedChen.Part3.Gamma0ActualHeatScalarCoefficient20261025a

noncomputable section
open Set MeasureTheory Filter Topology
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualResolventScalarMeasure20261025a
open Gamma0ActualFriedrichsSpectralMoments20261025a
open Gamma0ActualUnboundedScalarMeasure20261025a
open Gamma0ActualHeatGenerator20261025a

def actualHeatCoefficient (N : ℕ) [NeZero N] (f : QuotientL2 N) (t : ℝ) : ℝ :=
  (inner ℂ f (actualGammaHeat N t f)).re

theorem actualHeat_kernel_integrable (N : ℕ) [NeZero N] {t : ℝ} (ht : 0≤t)
    (f : QuotientL2 N) :
    Integrable (fun lambda : ℝ => Real.exp (-t*lambda)) (actualLaplaceMeasure N f) := by
  apply (integrable_const (1 : ℝ)).mono'
    (show AEStronglyMeasurable (fun lambda : ℝ => Real.exp (-t*lambda))
      (actualLaplaceMeasure N f) from
        (show Continuous (fun lambda : ℝ => Real.exp (-t*lambda)) by fun_prop).aestronglyMeasurable)
  filter_upwards [actualLaplaceMeasure_nonnegative_ae N f] with lambda hl
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hl)

/-- True scalar heat identity for the actual heat and actual measure;
the possibly spectral r=0 fiber is removed by a proved theorem. -/
theorem actualHeat_scalar_integral (N : ℕ) [NeZero N] {t : ℝ} (ht : 0≤t)
    (f : QuotientL2 N) :
    (∫ lambda : ℝ, Real.exp (-t*lambda) ∂actualLaplaceMeasure N f) =
      actualHeatCoefficient N f t := by
  have hm : Measurable (fun lambda : ℝ => Real.exp (-t*lambda)) := by fun_prop
  change (∫ lambda : ℝ, Real.exp (-t*lambda) ∂(actualScalarMeasure N f).map
    (GenericResolventUnboundedScalarMeasure20261025a.spectralLambda (actualGammaResolvent N))) = _
  rw [integral_map_of_stronglyMeasurable
    (GenericResolventUnboundedScalarMeasure20261025a.measurable_spectralLambda
      (actualGammaResolvent N)) hm.stronglyMeasurable]
  have heq : (fun r : ActualResolventSpectrum N => Real.exp (-t*
      GenericResolventUnboundedScalarMeasure20261025a.spectralLambda (actualGammaResolvent N) r))
      =ᵐ[actualScalarMeasure N f]
      (fun r => GenericPositiveResolventHeat20261025a.heatScalar (actualGammaHeatData N) t r) := by
    filter_upwards [actualScalarMeasure_ae_coordinate_pos N f] with r hr
    by_cases ht0 : t=0
    · subst t
      simp only [neg_zero, zero_mul, Real.exp_zero,
        GenericPositiveResolventHeat20261025a.heatScalar_zero, ContinuousMap.one_apply]
    · exact (GenericPositiveResolventHeat20261025a.heatScalar_apply_of_pos
        (actualGammaHeatData N) (lt_of_le_of_ne ht (Ne.symm ht0)) hr).symm
  rw [integral_congr_ae heq]
  exact GenericPositiveResolventHeat20261025a.scalarMeasure_integral
    (actualGammaHeatData N) f
    (GenericPositiveResolventHeat20261025a.heatScalar (actualGammaHeatData N) t)

theorem actualHeat_complex_scalar_integral (N : ℕ) [NeZero N] {t : ℝ} (ht : 0≤t)
    (f : QuotientL2 N) :
    (∫ lambda : ℝ, (Real.exp (-t*lambda) : ℂ) ∂actualLaplaceMeasure N f) =
      inner ℂ f (actualGammaHeat N t f) := by
  rw [integral_complex_ofReal]
  apply Complex.ext
  · simpa only [Complex.ofReal_re, actualHeatCoefficient] using actualHeat_scalar_integral N ht f
  · simp only [Complex.ofReal_im,
      (actualGammaHeat_selfAdjoint N t).isSymmetric.im_inner_self_apply f]

theorem actualHeatCoefficient_bounds (N : ℕ) [NeZero N] {t : ℝ} (ht : 0≤t)
    (f : QuotientL2 N) : 0≤actualHeatCoefficient N f t ∧ actualHeatCoefficient N f t≤‖f‖^2 := by
  constructor
  · rw [← actualHeat_scalar_integral N ht f]
    exact integral_nonneg (fun _ => (Real.exp_pos _).le)
  · rw [← actualHeat_scalar_integral N ht f]
    calc
      _ ≤ ∫ _lambda : ℝ, (1 : ℝ) ∂actualLaplaceMeasure N f := by
        apply integral_mono_ae (actualHeat_kernel_integrable N ht f) (integrable_const _)
        filter_upwards [actualLaplaceMeasure_nonnegative_ae N f] with lambda hl
        exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hl)
      _ = (actualLaplaceMeasure N f).real univ := by simp [Measure.real]
      _ = _ := actualLaplaceMeasure_mass N f

theorem actualHeatCoefficient_antitoneOn (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    AntitoneOn (actualHeatCoefficient N f) (Ici (0 : ℝ)) := by
  intro s hs t ht hst
  rw [← actualHeat_scalar_integral N ht f, ← actualHeat_scalar_integral N hs f]
  apply integral_mono_ae (actualHeat_kernel_integrable N ht f) (actualHeat_kernel_integrable N hs f)
  filter_upwards [actualLaplaceMeasure_nonnegative_ae N f] with lambda hl
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hst hl]

/-- A concrete exponential domination, with no spectral-domain input. -/
private theorem lambda_mul_exp_le {a lambda : ℝ} (ha : 0<a) (hl : 0≤lambda) :
    lambda*Real.exp (-a*lambda) ≤ 1/a := by
  have h := Real.mul_exp_neg_le_exp_neg_one (a*lambda)
  have h1 : Real.exp (-1)≤1 := Real.exp_le_one_iff.mpr (by norm_num)
  have heq : -(a*lambda) = -a*lambda := by ring
  rw [heq] at h
  apply (le_div_iff₀ ha).mpr
  nlinarith

theorem actualHeat_lambda_kernel_integrable (N : ℕ) [NeZero N] {t : ℝ} (ht : 0<t)
    (f : QuotientL2 N) :
    Integrable (fun lambda : ℝ => lambda*Real.exp (-t*lambda)) (actualLaplaceMeasure N f) := by
  apply (integrable_const (1/t : ℝ)).mono'
    (show AEStronglyMeasurable (fun lambda : ℝ => lambda*Real.exp (-t*lambda))
      (actualLaplaceMeasure N f) from
        (show Continuous (fun lambda : ℝ => lambda*Real.exp (-t*lambda)) by fun_prop).aestronglyMeasurable)
  filter_upwards [actualLaplaceMeasure_nonnegative_ae N f] with lambda hl
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hl (Real.exp_pos _).le)]
  exact lambda_mul_exp_le ht hl

private theorem local_heat_derivative_bound {t s lambda : ℝ}
    (ht : 0<t) (hs : t/2<s) (hl : 0≤lambda) :
    ‖-lambda*Real.exp (-s*lambda)‖ ≤ 2/t := by
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hl, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ lambda*Real.exp (-(t/2)*lambda) := by
      apply mul_le_mul_of_nonneg_left _ hl
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hs.le hl]
    _ ≤ 1/(t/2) := lambda_mul_exp_le (half_pos ht) hl
    _ = 2/t := by field_simp [ht.ne']; ring

/-- Differentiation under the actual finite measure is justified on a
whole neighborhood by a derived integrable derivative bound. -/
theorem actualHeat_laplace_hasDerivAt (N : ℕ) [NeZero N] {t : ℝ} (ht : 0<t)
    (f : QuotientL2 N) :
    HasDerivAt (fun s : ℝ => ∫ lambda : ℝ, Real.exp (-s*lambda) ∂actualLaplaceMeasure N f)
      (-(∫ lambda : ℝ, lambda*Real.exp (-t*lambda) ∂actualLaplaceMeasure N f)) t := by
  have hs : Ioi (t/2) ∈ 𝓝 t := isOpen_Ioi.mem_nhds (by dsimp; linarith)
  have hmeas : ∀ᶠ s : ℝ in 𝓝 t, AEStronglyMeasurable
      (fun lambda : ℝ => Real.exp (-s*lambda)) (actualLaplaceMeasure N f) :=
    Eventually.of_forall fun s =>
      (show Continuous (fun lambda : ℝ => Real.exp (-s*lambda)) by fun_prop).aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable
      (fun lambda : ℝ => -lambda*Real.exp (-t*lambda)) (actualLaplaceMeasure N f) :=
    (show Continuous (fun lambda : ℝ => -lambda*Real.exp (-t*lambda)) by fun_prop).aestronglyMeasurable
  have hbound : ∀ᵐ lambda ∂actualLaplaceMeasure N f, ∀ s ∈ Ioi (t/2),
      ‖-lambda*Real.exp (-s*lambda)‖ ≤ (2/t : ℝ) := by
    filter_upwards [actualLaplaceMeasure_nonnegative_ae N f] with lambda hl
    intro s hs
    exact local_heat_derivative_bound ht hs hl
  have hdiff : ∀ᵐ lambda ∂actualLaplaceMeasure N f, ∀ s ∈ Ioi (t/2),
      HasDerivAt (fun x : ℝ => Real.exp (-x*lambda)) (-lambda*Real.exp (-s*lambda)) s :=
    Eventually.of_forall fun lambda s _ => by
      convert (((hasDerivAt_id s).neg).mul_const lambda).exp using 1 <;> ring
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s lambda : ℝ => Real.exp (-s*lambda))
    (F' := fun s lambda : ℝ => -lambda*Real.exp (-s*lambda))
    (bound := fun _lambda : ℝ => (2/t : ℝ)) hs hmeas
    (actualHeat_kernel_integrable N ht.le f) hdmeas hbound (integrable_const _) hdiff).2
  simpa only [neg_mul, integral_neg] using hd

/-- Bernstein's first derivative formula for EVERY actual physical
vector. In particular no membership in the unbounded operator domain is required. -/
theorem actualHeatCoefficient_hasDerivAt (N : ℕ) [NeZero N] {t : ℝ} (ht : 0<t)
    (f : QuotientL2 N) :
    HasDerivAt (actualHeatCoefficient N f)
      (-(∫ lambda : ℝ, lambda*Real.exp (-t*lambda) ∂actualLaplaceMeasure N f)) t := by
  apply (actualHeat_laplace_hasDerivAt N ht f).congr_of_eventuallyEq
  apply Filter.eventually_of_mem (isOpen_Ioi.mem_nhds ht)
  intro s hs
  exact (actualHeat_scalar_integral N hs.le f).symm

theorem actualHeatCoefficient_deriv_nonpos (N : ℕ) [NeZero N] {t : ℝ} (ht : 0<t)
    (f : QuotientL2 N) : deriv (actualHeatCoefficient N f) t ≤ 0 := by
  rw [(actualHeatCoefficient_hasDerivAt N ht f).deriv]
  apply neg_nonpos.mpr
  apply integral_nonneg_of_ae
  filter_upwards [actualLaplaceMeasure_nonnegative_ae N f] with lambda hl
  exact mul_nonneg hl (Real.exp_pos _).le

end
end ImbalancedChen.Part3.Gamma0ActualHeatScalarCoefficient20261025a
