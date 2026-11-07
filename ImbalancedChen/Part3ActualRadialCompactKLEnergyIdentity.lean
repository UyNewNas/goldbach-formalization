import ImbalancedChen.Part3ActualRadialPhysicalFormSpectralMoment
import ImbalancedChen.Part3ActualKLScalarMeasureIdentification
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The original actual radial compact-core form energy equals the literal
tau^2-weighted KL integral. The native measure equality is consumed from
its independently proved Stone/Green identification; it is NOT an input
premise of any theorem here. The exact positive-axis square Jacobian
transports the lambda moment. Weighted integrability is independently
proved using the actual compact Hamiltonian test, before norm equality.
The exact frozen measure-identification leaf is recorded in the registry.
-/

namespace ImbalancedChen.Part3.ActualRadialCompactKLEnergyIdentity20261025a

noncomputable section
open Set MeasureTheory
open RadialSchrodingerL2Form20261025a
open ActualRadialCompactScalarStone20261025a
open ActualKLCompactDensityMeasure20261025a
open ActualKLScalarMeasureIdentification20261025a
open ActualKLCoordinateMeasures20261025a
open ActualKLCompactTestIntegrationByParts20261025a
open ActualKLCompactTestWeightedL220261025a

def compactRadialFormElement (F : RadialTest) : radialClosedEnergyDomain 1 :=
  ⟨radialEnergyCoreVector 1 F, (radialEnergyCoreSpan 1).le_topologicalClosure
    (Submodule.subset_span ⟨F, rfl⟩)⟩

theorem compactRadialFormElement_physical (F : RadialTest) :
    radialPhysicalEmbedding 1 (compactRadialFormElement F) = radialCoreL2 F :=
  energyPhysical_core 1 (by norm_num) F

theorem actualKL_hamiltonian_energy (F : RadialTest) (τ : ℝ) :
    actualKLEnergy (hamiltonianTest F) τ = τ ^ 4 * actualKLEnergy F τ := by
  rw [actualKLEnergy, actualKtransform_hamiltonian]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    pow_mul, sq_abs]
  unfold actualKLEnergy
  ring

/-- Actual first spectral moment integrability; the two existing compact
weighted L2 bounds provide a genuine majorant, with no norm premise. -/
theorem compact_actualKL_first_moment_integrable (F : RadialTest) :
    IntegrableOn (fun τ : ℝ => τ ^ 2 * actualKLEnergy F τ) (Ioi 0) := by
  have hmajor := (actualKtransform_KL_weighted_square_integrable F).add
    (actualKtransform_KL_weighted_square_integrable (hamiltonianTest F))
  apply hmajor.mono'
  · exact ((continuous_id.pow 2).aestronglyMeasurable.mul
      ((show Measurable actualKLWeight by unfold actualKLWeight normalization; fun_prop).
        aestronglyMeasurable.mul
        ((actualKtransform_stronglyMeasurable F).norm.pow 2))).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
    have hE : 0 ≤ actualKLEnergy F τ :=
      mul_nonneg (actualKLWeight_nonneg hτ.le) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hE),
      actualKL_hamiltonian_energy]
    have hpoly : τ ^ 2 ≤ 1 + τ ^ 4 := by
      nlinarith [sq_nonneg (τ ^ 2 - (1 / 2 : ℝ))]
    nlinarith [mul_nonneg (sub_nonneg.mpr hpoly) hE]

theorem compact_actualKL_literal_first_moment_integrable (F : RadialTest) :
    IntegrableOn (fun τ : ℝ => τ ^ 2 * actualKLWeight τ *
      ‖actualKtransform F.function τ‖ ^ 2) (Ioi 0) := by
  simpa only [actualKLEnergy, mul_assoc] using compact_actualKL_first_moment_integrable F

/-- Literal lambda density moment transported through the original
tau^2 Jacobian. All transforms are of the SAME compact radial input. -/
theorem compactKLDensityMeasure_lambda_moment (F : RadialTest) :
    (∫ λ : ℝ, λ ∂compactKLDensityMeasure F) =
      ∫ τ in Ioi (0 : ℝ), τ ^ 2 * actualKLWeight τ *
        ‖actualKtransform F.function τ‖ ^ 2 := by
  have hED : Measurable energyDensity := by unfold energyDensity; fun_prop
  have hTD : Measurable tauDensity := by unfold tauDensity; fun_prop
  have hT := actualKtransform_stronglyMeasurable F
  let g : ℝ → ℝ := fun λ => λ * ‖actualKtransform F.function (Real.sqrt λ)‖ ^ 2
  have hg : StronglyMeasurable g :=
    measurable_id.stronglyMeasurable.mul
      ((hT.measurable.comp Real.continuous_sqrt.measurable).norm.pow 2).stronglyMeasurable
  calc
    _ = ∫ λ in Ioi (0 : ℝ), compactLambdaDensity F λ * λ := by
      rw [compactKLDensityMeasure,
        integral_withDensity_eq_integral_toReal_smul
          (compactLambdaDensity_measurable F).ennreal_ofReal
          (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      simp only [ENNReal.toReal_ofReal (compactLambdaDensity_nonneg F _), smul_eq_mul]
    _ = ∫ λ, g λ ∂energyMeasure := by
      rw [energyMeasure, positiveDensityMeasure,
        integral_withDensity_eq_integral_toReal_smul hED.ennreal_ofReal
          (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      simp only [ENNReal.toReal_ofReal (energyDensity_nonneg _), smul_eq_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun λ => by
        rw [compactLambdaDensity_eq_energyDensity]
        dsimp only [g]
        ring)
    _ = ∫ τ, g (τ ^ 2) ∂tauMeasure := integral_energyMeasure g hg
    _ = ∫ τ, τ ^ 2 * ‖actualKtransform F.function τ‖ ^ 2 ∂tauMeasure := by
      apply integral_congr_ae
      have hp : ∀ᵐ τ ∂tauMeasure, 0 < τ :=
        (ae_restrict_mem measurableSet_Ioi).mono_ac (withDensity_absolutelyContinuous _ _)
      filter_upwards [hp] with τ hτ
      simp only [g, Real.sqrt_sq_eq_abs, abs_of_pos hτ]
    _ = _ := by
      rw [tauMeasure, positiveDensityMeasure,
        integral_withDensity_eq_integral_toReal_smul hTD.ennreal_ofReal
          (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
      rw [ENNReal.toReal_ofReal (by
        simpa only [tauDensity_eq_actualKLWeight] using actualKLWeight_nonneg hτ.le)]
      simp only [smul_eq_mul, tauDensity_eq_actualKLWeight]
      ring

/-- Actual physical unshifted form energy, with BOTH original coordinates,
is the literal tau^2-weighted KL transform integral. -/
theorem compact_actual_radial_KL_energy (F : RadialTest) :
    ‖radialDerivativeL2 F‖ ^ 2 + ‖radialExponentialL2 F‖ ^ 2 =
      ∫ τ in Ioi (0 : ℝ), τ ^ 2 * actualKLWeight τ *
        ‖actualKtransform F.function τ‖ ^ 2 := by
  have h := radialPhysical_closedForm_lambda_moment (compactRadialFormElement F)
  rw [compactRadialFormElement_physical] at h
  change ‖radialDerivativeL2 F‖ ^ 2 + ‖radialExponentialL2 F‖ ^ 2 =
    ∫ λ : ℝ, λ ∂compactRadialScalarMeasure F at h
  rw [compactRadialScalarMeasure_eq_actual_KL_density] at h
  exact h.trans (compactKLDensityMeasure_lambda_moment F)

/-- The exact same identity directly on the actual completed form core. -/
theorem compact_actual_closed_form_KL_energy (F : RadialTest) :
    ‖radialClosedDerivative 1 (compactRadialFormElement F)‖ ^ 2 +
      ‖radialClosedExponential 1 (compactRadialFormElement F)‖ ^ 2 =
      ∫ τ in Ioi (0 : ℝ), τ ^ 2 * actualKLWeight τ *
        ‖actualKtransform F.function τ‖ ^ 2 :=
  compact_actual_radial_KL_energy F

end
end ImbalancedChen.Part3.ActualRadialCompactKLEnergyIdentity20261025a
