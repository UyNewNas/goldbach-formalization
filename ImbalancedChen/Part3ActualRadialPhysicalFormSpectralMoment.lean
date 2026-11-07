import ImbalancedChen.Part3ActualRadialLambdaSquareRootForm
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Every physical radial vector F is treated as its OWN cyclic seed, with
the actual constant-one scalar vector synthesizing exactly to F.
The original closed radial form range is therefore exactly the set of
F for which sqrt(lambda) is L2 for the genuine native unbounded scalar
measure nu_F. Its first lambda moment is the literal derivative-plus-
exponential energy; its (1+lambda) moment is the full actual form norm.
This is a same-native closed-form theorem, independent of KL formulas.
-/

namespace ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a

noncomputable section
open MeasureTheory
open GenericResolventCyclicL2Representation20261025a

def radialScalarUnit (F : RadialL2) : RadialScalarL2 F :=
  spectralToLp radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F 1

theorem radialScalarUnit_coe_ae (F : RadialL2) :
    radialScalarUnit F =ᵐ[radialBoundedScalarMeasure F] (fun _ => (1 : ℂ)) :=
  (1 : C(RadialBoundedSpectrum, ℂ)).coeFn_toLp

theorem radialScalarUnit_synthesis (F : RadialL2) :
    cyclicExtension radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint F
      (radialScalarUnit F) = F := by
  rw [radialScalarUnit, cyclicExtension_apply]
  change complexResolventCFC radialUnitShiftResolvent
    radialUnitShiftResolvent_selfAdjoint 1 F = F
  rw [map_one]
  rfl

theorem radialPhysical_closedForm_domain_iff_sqrtLambdaMemLp (F : RadialL2) :
    (∃ e : radialClosedEnergyDomain 1, radialPhysicalEmbedding 1 e = F) ↔
      MemLp (fun λ : ℝ => (Real.sqrt λ : ℂ)) 2 (radialUnboundedScalarMeasure F) := by
  have hcyc := actualRadialClosedForm_domain_iff_lambdaSqrtMemLp F (radialScalarUnit F)
  rw [radialScalarUnit_synthesis] at hcyc
  rw [hcyc, radialUnboundedScalarMeasure,
    memLp_map_measure_iff
      ((Complex.continuous_ofReal.comp Real.continuous_sqrt).aestronglyMeasurable)
      radialSpectralLambda_measurable.aemeasurable]
  apply memLp_congr_ae
  filter_upwards [radialScalarUnit_coe_ae F] with t ht
  simp only [radialLambdaSqrtProduct, ht, mul_one, Function.comp_apply]

theorem radialPhysical_closedForm_lambda_integrable (e : radialClosedEnergyDomain 1) :
    Integrable (fun λ : ℝ => λ)
      (radialUnboundedScalarMeasure (radialPhysicalEmbedding 1 e)) := by
  let F := radialPhysicalEmbedding 1 e
  have hξ := (radialPhysical_closedForm_domain_iff_sqrtLambdaMemLp F).mp ⟨e, rfl⟩
  let g : ℝ → ℂ := fun λ => (Real.sqrt λ : ℂ)
  have hi := (L2.integrable_inner (𝕜 := ℂ) (hξ.toLp g) (hξ.toLp g)).re
  apply hi.congr
  have hpos : ∀ᵐ λ ∂radialUnboundedScalarMeasure F, 0 < λ := by
    rw [ae_iff]
    simpa only [not_lt] using radialUnboundedScalarMeasure_Iic_zero F
  filter_upwards [hξ.coeFn_toLp, hpos] with λ hλ hp
  rw [hλ, inner_self_eq_norm_sq_to_K]
  simp only [g, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hp.le]

/-- The actual physical native spectral measure's first moment is the
original two-coordinate unshifted radial energy, for EVERY form vector. -/
theorem radialPhysical_closedForm_lambda_moment (e : radialClosedEnergyDomain 1) :
    ‖radialClosedDerivative 1 e‖ ^ 2 + ‖radialClosedExponential 1 e‖ ^ 2 =
      ∫ λ : ℝ, λ ∂radialUnboundedScalarMeasure (radialPhysicalEmbedding 1 e) := by
  let F := radialPhysicalEmbedding 1 e
  have h := actualRadialClosedForm_lambda_integral F (radialScalarUnit F) e
    (radialScalarUnit_synthesis F).symm
  rw [radialUnboundedScalarMeasure,
    integral_map_of_stronglyMeasurable radialSpectralLambda_measurable
      (continuous_id.stronglyMeasurable : StronglyMeasurable (fun λ : ℝ => λ))]
  refine h.trans (integral_congr_ae ?_)
  filter_upwards [radialScalarUnit_coe_ae F] with t ht
  simp only [ht, norm_one, one_pow, mul_one]

/-- Shifted actual form norm, including the physical mass term. -/
theorem radialPhysical_closedForm_full_norm_moment (e : radialClosedEnergyDomain 1) :
    ‖e‖ ^ 2 = ‖radialPhysicalEmbedding 1 e‖ ^ 2 +
      ∫ λ : ℝ, λ ∂radialUnboundedScalarMeasure (radialPhysicalEmbedding 1 e) := by
  have h := congrArg Complex.re (radialClosedEnergy_inner 1 (by norm_num) e e)
  simp only [Complex.add_re, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow,
    Complex.ofReal_re] at h
  norm_num at h
  rw [← radialPhysical_closedForm_lambda_moment]
  linarith

/-- Exact actual norm formula in both directions. The membership
criterion is a consequence, and not an input equality of domains. -/
theorem radialPhysical_closedForm_exists_iff_spectral (F : RadialL2) :
    (∃ e : radialClosedEnergyDomain 1, radialPhysicalEmbedding 1 e = F ∧
      ‖e‖ ^ 2 = ‖F‖ ^ 2 + ∫ λ : ℝ, λ ∂radialUnboundedScalarMeasure F) ↔
      MemLp (fun λ : ℝ => (Real.sqrt λ : ℂ)) 2 (radialUnboundedScalarMeasure F) := by
  constructor
  · rintro ⟨e, he, _⟩
    exact (radialPhysical_closedForm_domain_iff_sqrtLambdaMemLp F).mp ⟨e, he⟩
  · intro hF
    obtain ⟨e, he⟩ := (radialPhysical_closedForm_domain_iff_sqrtLambdaMemLp F).mpr hF
    refine ⟨e, he, ?_⟩
    simpa only [he] using radialPhysical_closedForm_full_norm_moment e

end
end ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a
