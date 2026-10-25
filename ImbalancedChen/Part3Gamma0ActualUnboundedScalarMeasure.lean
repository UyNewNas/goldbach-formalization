import ImbalancedChen.Part3Gamma0ActualFriedrichsSpectralMoments
import ImbalancedChen.Part3Gamma0ActualShiftedFriedrichsResolvent
import ImbalancedChen.Part3GenericResolventUnboundedScalarMeasure

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The ACTUAL Gamma0 unbounded scalar measure is the generic inverse-
resolvent pushforward instantiated at the genuine physical J J* on H_Gamma.
It is finite, concentrated on [0,infinity), and has norm-squared mass.

Its first and second moments for every ACTUAL native Friedrichs-domain
vector are proved integrable and equal the actual quadratic pair and
actual output norm. This uses the genuine domain weighted-measure theorem,
not a proposed unbounded spectral graph. Every positive shifted physical
resolvent has its real and complex Stieltjes representation for this SAME
measure, with the scalar kernel bounded by 1/a almost everywhere.

The two total inverse-coordinate conventions agree only off r=0; their
needed a.e. equality is proved using the actual zero-fiber theorem. The
possible lambda=0 sector is retained. No spectral gap, Kuznetsov density,
normalization constant, or essential self-adjointness is asserted.
-/

namespace ImbalancedChen.Part3.Gamma0ActualUnboundedScalarMeasure20261025a

noncomputable section
open Set MeasureTheory Filter
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0ActualResolventScalarMeasure20261025a
open Gamma0ActualFriedrichsSpectralMoments20261025a
open Gamma0ActualShiftedFriedrichsResolvent20261025a

/-- A scalar measure on the real unbounded spectral coordinate, for
the SAME actual physical quotient resolvent and vector. -/
def actualLaplaceMeasure (N : ℕ) [NeZero N] (f : QuotientL2 N) : Measure ℝ :=
  GenericResolventUnboundedScalarMeasure20261025a.unboundedScalarMeasure
    (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f

instance actualLaplaceMeasure_finite (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    IsFiniteMeasure (actualLaplaceMeasure N f) := by
  unfold actualLaplaceMeasure
  infer_instance

theorem actualLaplaceMeasure_Iio_zero (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    actualLaplaceMeasure N f (Iio 0) = 0 :=
  GenericResolventUnboundedScalarMeasure20261025a.unboundedScalarMeasure_Iio_zero
    (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
    (actualGammaResolvent_nonneg N) (actualGammaResolvent_opNorm_le_one N)
    (actualGammaResolvent_injective N) f

theorem actualLaplaceMeasure_nonnegative_ae (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    ∀ᵐ lambda ∂actualLaplaceMeasure N f, 0 ≤ lambda := by
  rw [ae_iff]
  simpa only [not_le] using actualLaplaceMeasure_Iio_zero N f

theorem actualLaplaceMeasure_mass (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    (actualLaplaceMeasure N f).real univ = ‖f‖^2 :=
  GenericResolventUnboundedScalarMeasure20261025a.unboundedScalarMeasure_mass
    (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f

theorem actualLaplaceMeasure_univ (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    actualLaplaceMeasure N f univ = ENNReal.ofReal (‖f‖^2) :=
  GenericResolventUnboundedScalarMeasure20261025a.unboundedScalarMeasure_univ
    (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f

private theorem lambda_conventions_ae (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    GenericResolventUnboundedScalarMeasure20261025a.spectralLambda (actualGammaResolvent N)
      =ᵐ[actualScalarMeasure N f] actualSpectralLambda N := by
  filter_upwards [actualScalarMeasure_ae_coordinate_pos N f] with r hr
  unfold GenericResolventUnboundedScalarMeasure20261025a.spectralLambda actualSpectralLambda
  field_simp [hr.ne']
  <;> ring

/-- First moment integrability for a true ACTUAL unbounded-domain input. -/
theorem actualLaplaceMeasure_domain_first_integrable (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    Integrable (fun lambda : ℝ => lambda) (actualLaplaceMeasure N (u : QuotientL2 N)) := by
  change Integrable _ ((actualScalarMeasure N (u : QuotientL2 N)).map
    (GenericResolventUnboundedScalarMeasure20261025a.spectralLambda (actualGammaResolvent N)))
  apply (integrable_map_measure measurable_id.aestronglyMeasurable
    (GenericResolventUnboundedScalarMeasure20261025a.measurable_spectralLambda
      (actualGammaResolvent N)).aemeasurable).2
  exact (domain_lambda_integrable N u).congr (lambda_conventions_ae N (u : QuotientL2 N)).symm

theorem actualLaplaceMeasure_domain_second_integrable (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    Integrable (fun lambda : ℝ => lambda^2) (actualLaplaceMeasure N (u : QuotientL2 N)) := by
  have hm : Measurable (fun lambda : ℝ => lambda^2) := by fun_prop
  change Integrable _ ((actualScalarMeasure N (u : QuotientL2 N)).map
    (GenericResolventUnboundedScalarMeasure20261025a.spectralLambda (actualGammaResolvent N)))
  apply (integrable_map_measure hm.aestronglyMeasurable
    (GenericResolventUnboundedScalarMeasure20261025a.measurable_spectralLambda
      (actualGammaResolvent N)).aemeasurable).2
  apply (domain_lambda_sq_integrable N u).congr
  filter_upwards [lambda_conventions_ae N (u : QuotientL2 N)] with r hr
  simp only [Function.comp_apply, hr]

/-- The physical operator-domain first moment, for the unbounded
pushforward measure itself, rather than its old bounded coordinate. -/
theorem actualLaplaceMeasure_domain_first_moment (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    (∫ lambda : ℝ, lambda ∂actualLaplaceMeasure N (u : QuotientL2 N)) =
      (inner ℂ (u : QuotientL2 N) (actualGammaFriedrichs N u)).re := by
  change (∫ lambda : ℝ, lambda ∂(actualScalarMeasure N (u : QuotientL2 N)).map
    (GenericResolventUnboundedScalarMeasure20261025a.spectralLambda (actualGammaResolvent N))) = _
  rw [integral_map_of_stronglyMeasurable
    (GenericResolventUnboundedScalarMeasure20261025a.measurable_spectralLambda
      (actualGammaResolvent N)) measurable_id.stronglyMeasurable]
  exact (integral_congr_ae (lambda_conventions_ae N (u : QuotientL2 N))).trans
    (domain_lambda_integral_pair N u)

theorem actualLaplaceMeasure_domain_second_moment (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    (∫ lambda : ℝ, lambda^2 ∂actualLaplaceMeasure N (u : QuotientL2 N)) =
      ‖actualGammaFriedrichs N u‖^2 := by
  have hm : Measurable (fun lambda : ℝ => lambda^2) := by fun_prop
  change (∫ lambda : ℝ, lambda^2 ∂(actualScalarMeasure N (u : QuotientL2 N)).map
    (GenericResolventUnboundedScalarMeasure20261025a.spectralLambda (actualGammaResolvent N))) = _
  rw [integral_map_of_stronglyMeasurable
    (GenericResolventUnboundedScalarMeasure20261025a.measurable_spectralLambda
      (actualGammaResolvent N)) hm.stronglyMeasurable]
  calc
    _ = ∫ r, (actualSpectralLambda N r)^2 ∂actualScalarMeasure N (u : QuotientL2 N) := by
      apply integral_congr_ae
      filter_upwards [lambda_conventions_ae N (u : QuotientL2 N)] with r hr
      simp only [hr]
    _ = _ := domain_lambda_sq_integral N u

theorem actualLaplaceMeasure_stieltjes_integrable (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) (f : QuotientL2 N) :
    Integrable (fun lambda : ℝ => (a+lambda)⁻¹) (actualLaplaceMeasure N f) :=
  GenericResolventUnboundedScalarMeasure20261025a.integrable_shifted_resolventCoordinate
    (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
    (actualGammaResolvent_nonneg N) (actualGammaResolvent_opNorm_le_one N)
    (actualGammaResolvent_injective N) ha f

/-- The Stieltjes coefficient belongs to the ACTUAL two-sided inverse
of aI+A_F on its true domain, as proved in the actual shifted-operator source. -/
theorem actualLaplaceMeasure_stieltjes_integral (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) (f : QuotientL2 N) :
    (∫ lambda : ℝ, (a+lambda)⁻¹ ∂actualLaplaceMeasure N f) =
      (inner ℂ f (actualGammaShiftedResolvent N a f)).re :=
  GenericResolventUnboundedScalarMeasure20261025a.scalar_shifted_resolvent_integral
    (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
    (actualGammaResolvent_nonneg N) (actualGammaResolvent_opNorm_le_one N)
    (actualGammaResolvent_injective N) ha f

theorem actualLaplaceMeasure_complex_stieltjes_integral (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) (f : QuotientL2 N) :
    (∫ lambda : ℝ, (((a+lambda)⁻¹ : ℝ) : ℂ) ∂actualLaplaceMeasure N f) =
      inner ℂ f (actualGammaShiftedResolvent N a f) := by
  rw [integral_complex_ofReal]
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using actualLaplaceMeasure_stieltjes_integral N ha f
  · simp only [Complex.ofReal_im,
      (actualGammaShiftedResolvent_selfAdjoint N a).isSymmetric.im_inner_self_apply f]

/-- A genuine uniform kernel bound on the actual nonnegative measure,
including lambda=0. No lower positive spectral gap is assumed. -/
theorem actualLaplaceMeasure_stieltjes_kernel_bound (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) (f : QuotientL2 N) :
    ∀ᵐ lambda ∂actualLaplaceMeasure N f,
      0 ≤ (a+lambda)⁻¹ ∧ ‖(a+lambda)⁻¹‖ ≤ 1/a := by
  filter_upwards [actualLaplaceMeasure_nonnegative_ae N f] with lambda hl
  have hden : 0<a+lambda := add_pos_of_pos_of_nonneg ha hl
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hden.le)]
  simpa only [one_div] using one_div_le_one_div_of_le ha (le_add_of_nonneg_right hl)

theorem actualLaplaceMeasure_stieltjes_integral_bound (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0<a) (f : QuotientL2 N) :
    0 ≤ (∫ lambda : ℝ, (a+lambda)⁻¹ ∂actualLaplaceMeasure N f) ∧
      (∫ lambda : ℝ, (a+lambda)⁻¹ ∂actualLaplaceMeasure N f) ≤ (1/a)*‖f‖^2 := by
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [actualLaplaceMeasure_stieltjes_kernel_bound N ha f] with lambda hl
    exact hl.1
  · rw [actualLaplaceMeasure_stieltjes_integral N ha f]
    calc
      _ ≤ ‖f‖*‖actualGammaShiftedResolvent N a f‖ :=
        (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
      _ ≤ ‖f‖*((1/a)*‖f‖) :=
        mul_le_mul_of_nonneg_left (actualGammaShiftedResolvent_apply_norm_le N ha f) (norm_nonneg f)
      _ = _ := by ring

end
end ImbalancedChen.Part3.Gamma0ActualUnboundedScalarMeasure20261025a
