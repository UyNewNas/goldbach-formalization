import ImbalancedChen.Part3ActualRadialSpectralFormDomain
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
TRUE maximal sqrt(lambda)-weighted L2 criterion for the SAME actual
radial closed energy form, and its complete shifted/unshifted norm
identities. Every cyclic seed and every scalar L2 vector are allowed.
The inverse sqrt(t) criterion is proved in the preceding module, not
assumed. This module proves its equivalence with sqrt(1/t-1), including
integrability and the exact derivative-plus-exponential energy.
No KL transform, compact forcing density or assumed form equality enters.
-/

namespace ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a

noncomputable section
open MeasureTheory
open GenericResolventCyclicL2Representation20261025a

def radialLambdaSqrtProduct (F : RadialL2) (ξ : RadialScalarL2 F)
    (t : RadialBoundedSpectrum) : ℂ :=
  (Real.sqrt (radialSpectralLambda t) : ℂ) * ξ t

theorem radialInverseSqrtProduct_aestronglyMeasurable (F : RadialL2)
    (ξ : RadialScalarL2 F) :
    AEStronglyMeasurable (radialInverseSqrtProduct F ξ) (radialBoundedScalarMeasure F) := by
  exact ((Complex.continuous_ofReal.comp
    (Real.continuous_sqrt.comp continuous_subtype_val)).measurable.inv.aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable ξ)

theorem radialLambdaSqrtProduct_aestronglyMeasurable (F : RadialL2)
    (ξ : RadialScalarL2 F) :
    AEStronglyMeasurable (radialLambdaSqrtProduct F ξ) (radialBoundedScalarMeasure F) := by
  exact (Complex.measurable_ofReal.comp
    (Real.continuous_sqrt.measurable.comp radialSpectralLambda_measurable)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable ξ)

theorem radialSpectral_form_weight_identity (F : RadialL2) (ξ : RadialScalarL2 F) :
    ∀ᵐ t ∂radialBoundedScalarMeasure F,
      ‖radialInverseSqrtProduct F ξ t‖ ^ 2 =
        ‖ξ t‖ ^ 2 + ‖radialLambdaSqrtProduct F ξ t‖ ^ 2 := by
  filter_upwards [radialBoundedScalarMeasure_ae_strict_unitInterval F,
    radialSpectralLambda_pos_ae F] with t ht hλ
  simp only [radialInverseSqrtProduct, radialLambdaSqrtProduct, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, ← inv_pow, Real.sq_sqrt ht.1.le, Real.sq_sqrt hλ.le,
    radialSpectralLambda]
  ring

/-- The mass term already belongs to scalar L2, so the shifted and
unshifted square-root graph norms have precisely the same domain. -/
theorem radialInverseSqrt_memLp_iff_lambdaSqrt (F : RadialL2)
    (ξ : RadialScalarL2 F) :
    MemLp (radialInverseSqrtProduct F ξ) 2 (radialBoundedScalarMeasure F) ↔
      MemLp (radialLambdaSqrtProduct F ξ) 2 (radialBoundedScalarMeasure F) := by
  constructor
  · intro h
    apply h.of_le (radialLambdaSqrtProduct_aestronglyMeasurable F ξ)
    filter_upwards [radialSpectral_form_weight_identity F ξ] with t ht
    nlinarith [sq_nonneg ‖ξ t‖, norm_nonneg (radialInverseSqrtProduct F ξ t),
      norm_nonneg (radialLambdaSqrtProduct F ξ t)]
  · intro h
    apply ((Lp.memLp ξ).norm.add h.norm).of_le
      (radialInverseSqrtProduct_aestronglyMeasurable F ξ)
    filter_upwards [radialSpectral_form_weight_identity F ξ] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    nlinarith [mul_nonneg (norm_nonneg (ξ t))
      (norm_nonneg (radialLambdaSqrtProduct F ξ t)),
      norm_nonneg (radialInverseSqrtProduct F ξ t),
      norm_nonneg (ξ t), norm_nonneg (radialLambdaSqrtProduct F ξ t)]

/-- EXACT actual closed-form range iff the actual spectral sqrt(lambda)
product belongs to L2. There is no unproved domain supplier. -/
theorem actualRadialClosedForm_domain_iff_lambdaSqrtMemLp (F : RadialL2)
    (ξ : RadialScalarL2 F) :
    (∃ e : radialClosedEnergyDomain 1, radialPhysicalEmbedding 1 e =
      cyclicExtension radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F ξ) ↔
      MemLp (radialLambdaSqrtProduct F ξ) 2 (radialBoundedScalarMeasure F) :=
  (radialClosedForm_domain_iff_inverseSqrtMemLp F ξ).trans
    (radialInverseSqrt_memLp_iff_lambdaSqrt F ξ)

private theorem scalar_memLp_norm_sq_integrable (F : RadialL2)
    (g : RadialBoundedSpectrum → ℂ) (hg : MemLp g 2 (radialBoundedScalarMeasure F)) :
    Integrable (fun t => ‖g t‖ ^ 2) (radialBoundedScalarMeasure F) := by
  have hi := (L2.integrable_inner (𝕜 := ℂ) (hg.toLp g) (hg.toLp g)).re
  apply hi.congr
  filter_upwards [hg.coeFn_toLp] with t ht
  rw [ht, inner_self_eq_norm_sq_to_K]
  simp

private theorem scalar_memLp_norm_sq_integral (F : RadialL2)
    (g : RadialBoundedSpectrum → ℂ) (hg : MemLp g 2 (radialBoundedScalarMeasure F)) :
    ‖hg.toLp g‖ ^ 2 = ∫ t, ‖g t‖ ^ 2 ∂radialBoundedScalarMeasure F := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) (hg.toLp g) (hg.toLp g))]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with t ht
  rw [ht, inner_self_eq_norm_sq_to_K]
  simp

theorem radialSpectral_shifted_norm_sq (F : RadialL2) (ξ : RadialScalarL2 F)
    (hξ : MemLp (radialLambdaSqrtProduct F ξ) 2 (radialBoundedScalarMeasure F)) :
    ‖((radialInverseSqrt_memLp_iff_lambdaSqrt F ξ).mpr hξ).toLp
      (radialInverseSqrtProduct F ξ)‖ ^ 2 = ‖ξ‖ ^ 2 +
      ‖hξ.toLp (radialLambdaSqrtProduct F ξ)‖ ^ 2 := by
  let hi := (radialInverseSqrt_memLp_iff_lambdaSqrt F ξ).mpr hξ
  have hbase : ‖ξ‖ ^ 2 = ∫ t, ‖ξ t‖ ^ 2 ∂radialBoundedScalarMeasure F := by
    have h := scalar_memLp_norm_sq_integral F (fun t => ξ t) (Lp.memLp ξ)
    have he : (Lp.memLp ξ).toLp (fun t => ξ t) = ξ := by
      apply Lp.ext
      exact (Lp.memLp ξ).coeFn_toLp
    rwa [he] at h
  rw [scalar_memLp_norm_sq_integral, hbase, scalar_memLp_norm_sq_integral,
    ← integral_add (scalar_memLp_norm_sq_integrable F _ (Lp.memLp ξ))
      (scalar_memLp_norm_sq_integrable F _ hξ)]
  exact integral_congr_ae (radialSpectral_form_weight_identity F ξ)

/-- Complete original three-coordinate shifted norm identity for every
actual energy element whose physical vector lies in this cyclic block. -/
theorem actualRadialClosedForm_full_norm_sq (F : RadialL2) (ξ : RadialScalarL2 F)
    (e : radialClosedEnergyDomain 1)
    (he : radialPhysicalEmbedding 1 e =
      cyclicExtension radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F ξ) :
    ∃ hξ : MemLp (radialLambdaSqrtProduct F ξ) 2 (radialBoundedScalarMeasure F),
      ‖e‖ ^ 2 = ‖ξ‖ ^ 2 + ‖hξ.toLp (radialLambdaSqrtProduct F ξ)‖ ^ 2 := by
  obtain ⟨hi, hnorm⟩ := radialClosedForm_full_norm F ξ e he
  have hξ := (radialInverseSqrt_memLp_iff_lambdaSqrt F ξ).mp hi
  refine ⟨hξ, ?_⟩
  rw [hnorm]
  exact radialSpectral_shifted_norm_sq F ξ hξ

/-- The genuine unshifted radial form, with its actual derivative and
exp(r)-multiplication coordinates, is EXACTLY sqrt(lambda) energy. -/
theorem actualRadialClosedForm_unshifted_norm_sq (F : RadialL2) (ξ : RadialScalarL2 F)
    (e : radialClosedEnergyDomain 1)
    (he : radialPhysicalEmbedding 1 e =
      cyclicExtension radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F ξ) :
    ∃ hξ : MemLp (radialLambdaSqrtProduct F ξ) 2 (radialBoundedScalarMeasure F),
      ‖radialClosedDerivative 1 e‖ ^ 2 + ‖radialClosedExponential 1 e‖ ^ 2 =
        ‖hξ.toLp (radialLambdaSqrtProduct F ξ)‖ ^ 2 := by
  obtain ⟨hξ, hspec⟩ := actualRadialClosedForm_full_norm_sq F ξ e he
  refine ⟨hξ, ?_⟩
  have hform := congrArg Complex.re (radialClosedEnergy_inner 1 (by norm_num) e e)
  simp only [Complex.add_re, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow,
    Complex.ofReal_re] at hform
  norm_num at hform
  rw [he, cyclicExtension_norm] at hform
  linarith

theorem actualRadialClosedForm_lambda_integral (F : RadialL2) (ξ : RadialScalarL2 F)
    (e : radialClosedEnergyDomain 1)
    (he : radialPhysicalEmbedding 1 e =
      cyclicExtension radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F ξ) :
    ‖radialClosedDerivative 1 e‖ ^ 2 + ‖radialClosedExponential 1 e‖ ^ 2 =
      ∫ t : RadialBoundedSpectrum, radialSpectralLambda t * ‖ξ t‖ ^ 2
        ∂radialBoundedScalarMeasure F := by
  obtain ⟨hξ, henergy⟩ := actualRadialClosedForm_unshifted_norm_sq F ξ e he
  rw [henergy, scalar_memLp_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [radialSpectralLambda_pos_ae F] with t ht
  simp only [radialLambdaSqrtProduct, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt ht.le]

end
end ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a
