import ImbalancedChen.Part3ActualKLAllVectorScalarMeasure
import ImbalancedChen.Part3ActualRadialPhysicalFormSpectralMoment
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The actual physical closed form domain is exactly the tau-weighted raw
KL L2 domain. The converse is obtained from the independently proved
native scalar spectral form theorem, after the all-vector measure
identification. The unshifted energy and the full form norm are actual
tau^2 moments for every form vector. No equality of domains or energies
is supplied as a premise.
-/

namespace ImbalancedChen.Part3.ActualKLNativeFormDomain20261026a

noncomputable section
open Set MeasureTheory Filter
open RadialSchrodingerL2Form20261025a
open ActualKLCoreTransform20261025a ActualKLCoordinateMeasures20261025a
open ActualKLOntoUnitary20261025a ActualKLAllVectorScalarMeasure20261026a

theorem native_scalar_positive_ae (F : RadialL2) :
    ∀ᵐ λ : ℝ ∂radialUnboundedScalarMeasure F, 0 < λ := by
  rw [ae_iff]
  simpa only [not_lt] using radialUnboundedScalarMeasure_Iic_zero F

/-- The native square-root theorem is equivalently the first scalar
moment criterion; positivity is proved for the same native measure. -/
theorem native_form_domain_iff_firstMoment (F : RadialL2) :
    (∃ e : radialClosedEnergyDomain 1, radialPhysicalEmbedding 1 e = F) ↔
      Integrable (fun λ : ℝ => λ) (radialUnboundedScalarMeasure F) := by
  rw [radialPhysical_closedForm_domain_iff_sqrtLambdaMemLp,
    memLp_two_iff_integrable_sq_norm
      ((Complex.continuous_ofReal.comp Real.continuous_sqrt).aestronglyMeasurable)]
  apply integrable_congr
  filter_upwards [native_scalar_positive_ae F] with λ hλ
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hλ.le]

theorem native_firstMoment_integrable_iff (F : RadialL2) :
    Integrable (fun λ : ℝ => λ) (radialUnboundedScalarMeasure F) ↔
      Integrable (fun τ : ℝ => τ ^ 2 * ‖actualKLUnitary F τ‖ ^ 2) tauMeasure := by
  rw [native_scalarMeasure_eq_actualKL, klScalarMeasure,
    integrable_map_measure continuous_id.aestronglyMeasurable
      (show AEMeasurable (fun τ : ℝ => τ ^ 2)
        (amplitudeMeasure (actualKLUnitary F)) from (by fun_prop)),
    amplitudeMeasure,
    integrable_withDensity_iff_integrable_smul₀'
      (((Lp.aestronglyMeasurable (actualKLUnitary F)).norm.pow 2).aemeasurable.ennreal_ofReal)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [Function.comp_apply, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, mul_comm]

/-- Both directions on the original native physical form range. -/
theorem actualKL_form_domain_iff (F : RadialL2) :
    (∃ e : radialClosedEnergyDomain 1, radialPhysicalEmbedding 1 e = F) ↔
      Integrable (fun τ : ℝ => τ ^ 2 * ‖actualKLUnitary F τ‖ ^ 2) tauMeasure := by
  rw [native_form_domain_iff_firstMoment, native_firstMoment_integrable_iff]

def tauProduct (g : RawTauL2) (τ : ℝ) : ℂ := (τ : ℂ) * g τ

theorem tauProduct_aestronglyMeasurable (g : RawTauL2) :
    AEStronglyMeasurable (tauProduct g) tauMeasure :=
  Complex.continuous_ofReal.aestronglyMeasurable.mul (Lp.aestronglyMeasurable g)

theorem tauProduct_norm_sq (g : RawTauL2) (τ : ℝ) :
    ‖tauProduct g τ‖ ^ 2 = τ ^ 2 * ‖g τ‖ ^ 2 := by
  simp only [tauProduct, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem tauProduct_memLp_iff (g : RawTauL2) :
    MemLp (tauProduct g) 2 tauMeasure ↔
      Integrable (fun τ : ℝ => τ ^ 2 * ‖g τ‖ ^ 2) tauMeasure := by
  rw [memLp_two_iff_integrable_sq_norm (tauProduct_aestronglyMeasurable g)]
  simp_rw [tauProduct_norm_sq]

theorem actualKL_form_domain_iff_tauMemLp (F : RadialL2) :
    (∃ e : radialClosedEnergyDomain 1, radialPhysicalEmbedding 1 e = F) ↔
      MemLp (tauProduct (actualKLUnitary F)) 2 tauMeasure := by
  rw [tauProduct_memLp_iff, actualKL_form_domain_iff]

/-- The literal first moment formula requires no domain premise; it is
an equality of Bochner integrals, and finiteness is characterized above. -/
theorem native_firstMoment_eq_tauIntegral (F : RadialL2) :
    (∫ λ : ℝ, λ ∂radialUnboundedScalarMeasure F) =
      ∫ τ : ℝ, τ ^ 2 * ‖actualKLUnitary F τ‖ ^ 2 ∂tauMeasure := by
  rw [native_scalarMeasure_eq_actualKL, klScalarMeasure,
    integral_map_of_stronglyMeasurable (by fun_prop)
      (continuous_id.stronglyMeasurable : StronglyMeasurable (fun λ : ℝ => λ)),
    amplitudeMeasure, integral_withDensity_eq_integral_toReal_smul₀
      (((Lp.aestronglyMeasurable (actualKLUnitary F)).norm.pow 2).aemeasurable.ennreal_ofReal)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun τ => mul_comm _ _)

theorem actualKL_form_energy_integrable (e : radialClosedEnergyDomain 1) :
    Integrable (fun τ : ℝ => τ ^ 2 *
      ‖actualKLUnitary (radialPhysicalEmbedding 1 e) τ‖ ^ 2) tauMeasure :=
  (actualKL_form_domain_iff _).mp ⟨e, rfl⟩

theorem actualKL_form_energy (e : radialClosedEnergyDomain 1) :
    ‖radialClosedDerivative 1 e‖ ^ 2 + ‖radialClosedExponential 1 e‖ ^ 2 =
      ∫ τ : ℝ, τ ^ 2 * ‖actualKLUnitary (radialPhysicalEmbedding 1 e) τ‖ ^ 2 ∂tauMeasure := by
  rw [radialPhysical_closedForm_lambda_moment, native_firstMoment_eq_tauIntegral]

theorem actualKL_form_norm (e : radialClosedEnergyDomain 1) :
    ‖e‖ ^ 2 = ‖radialPhysicalEmbedding 1 e‖ ^ 2 +
      ∫ τ : ℝ, τ ^ 2 * ‖actualKLUnitary (radialPhysicalEmbedding 1 e) τ‖ ^ 2 ∂tauMeasure := by
  rw [radialPhysical_closedForm_full_norm_moment, native_firstMoment_eq_tauIntegral]

theorem actualKL_form_domain_image :
    actualKLUnitary '' Set.range (radialPhysicalEmbedding 1) =
      {g : RawTauL2 | Integrable (fun τ : ℝ => τ ^ 2 * ‖g τ‖ ^ 2) tauMeasure} := by
  ext g
  constructor
  · rintro ⟨F, ⟨e, he⟩, rfl⟩
    exact (actualKL_form_domain_iff F).mp ⟨e, he⟩
  · intro hg
    refine ⟨actualKLUnitary.symm g, ?_, actualKLUnitary.apply_symm_apply g⟩
    exact (actualKL_form_domain_iff (actualKLUnitary.symm g)).mpr
      (by simpa only [actualKLUnitary.apply_symm_apply] using hg)

theorem formTau_memLp (e : radialClosedEnergyDomain 1) :
    MemLp (tauProduct (actualKLUnitary (radialPhysicalEmbedding 1 e))) 2 tauMeasure :=
  (tauProduct_memLp_iff _).mpr (actualKL_form_energy_integrable e)

def formTauL2 (e : radialClosedEnergyDomain 1) : RawTauL2 :=
  (formTau_memLp e).toLp (tauProduct (actualKLUnitary (radialPhysicalEmbedding 1 e)))

theorem formTauL2_coe_ae (e : radialClosedEnergyDomain 1) :
    formTauL2 e =ᵐ[tauMeasure] tauProduct (actualKLUnitary (radialPhysicalEmbedding 1 e)) :=
  (formTau_memLp e).coeFn_toLp

theorem formTauL2_norm_sq (e : radialClosedEnergyDomain 1) :
    ‖formTauL2 e‖ ^ 2 =
      ‖radialClosedDerivative 1 e‖ ^ 2 + ‖radialClosedExponential 1 e‖ ^ 2 := by
  rw [actualKL_form_energy, raw_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [formTauL2_coe_ae e] with τ hτ
  rw [hτ, tauProduct_norm_sq]

end
end ImbalancedChen.Part3.ActualKLNativeFormDomain20261026a
