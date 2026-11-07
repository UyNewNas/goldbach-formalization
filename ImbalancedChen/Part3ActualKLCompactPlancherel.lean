import ImbalancedChen.Part3ActualKLScalarMeasureIdentification
import ImbalancedChen.Part3ActualKLCoreTransform

/-!
# Actual compact-test Kontorovich--Lebedev Plancherel identity

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The native scalar measure has already been identified by two proved Stone
limits, including the elimination of positive endpoint atoms. Its entire
mass is the original physical L2 norm squared. The actual tau^2 Jacobian
then gives the literal KL weight (2/pi^2)*tau*sinh(pi*tau).
The raw transform is the existing actual integral core map, not a newly
normalized surrogate. No norm, spectral density or boundary-exchange
hypothesis is introduced.
-/

namespace ImbalancedChen.Part3.ActualKLCompactPlancherel20261025a

noncomputable section
open Set MeasureTheory
open RadialSchrodingerL2Form20261025a
open ActualKLCompactTestIntegrationByParts20261025a ActualKLCompactTestWeightedL220261025a
open ActualKLCoordinateMeasures20261025a ActualKLCoreTransform20261025a
open ActualRadialCompactScalarStone20261025a ActualKLCompactDensityMeasure20261025a
open ActualKLScalarMeasureIdentification20261025a

/-- Literal normalized KL energy equals the full actual physical norm.
This is a conclusion from the native spectral mass, not an input to an
extension or to a formal transform package. -/
theorem actualKL_compact_integral_norm (T : RadialTest) :
    (∫ tau in Ioi (0 : ℝ),
      actualKLWeight tau * ‖actualKtransform T.function tau‖ ^ 2) =
        ‖radialCoreL2 T‖ ^ 2 := by
  have hmass := congrArg (fun mu : Measure ℝ => mu univ)
    (compactRadialScalarMeasure_eq_actual_KL_density T)
  rw [compactKLDensityMeasure_univ] at hmass
  change radialUnboundedScalarMeasure (radialCoreL2 T) univ =
    ENNReal.ofReal (∫ tau in Ioi (0 : ℝ), actualKLEnergy T tau) at hmass
  rw [radialUnboundedScalarMeasure_univ] at hmass
  have hnonneg : 0 ≤ ∫ tau in Ioi (0 : ℝ), actualKLEnergy T tau :=
    integral_nonneg_of_ae (actualKLEnergy_ae_nonneg T)
  have hreal := congrArg ENNReal.toReal hmass
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal hnonneg, actualKLEnergy] using hreal.symm

private theorem rawKLTestTransform_norm_sq_integral (T : RadialTest) :
    ‖rawKLTestTransform T‖ ^ 2 =
      ∫ tau, ‖actualKtransform T.function tau‖ ^ 2 ∂tauMeasure := by
  have hL2 : inner ℂ (rawKLTestTransform T) (rawKLTestTransform T) =
      ∫ tau, inner ℂ (rawKLTestTransform T tau) (rawKLTestTransform T tau) ∂tauMeasure :=
    L2.inner_def _ _
  simp_rw [inner_self_eq_norm_sq_to_K] at hL2
  rw [integral_ofReal] at hL2
  have hreal := Complex.ofReal_injective hL2
  rw [hreal]
  apply integral_congr_ae
  filter_upwards [rawKLTestTransform_ae T] with tau htau
  rw [htau]

private theorem tau_norm_integral_eq_actual_energy (T : RadialTest) :
    (∫ tau, ‖actualKtransform T.function tau‖ ^ 2 ∂tauMeasure) =
      ∫ tau in Ioi (0 : ℝ), actualKLEnergy T tau := by
  change (∫ tau, ‖actualKtransform T.function tau‖ ^ 2
    ∂((volume : Measure ℝ).restrict (Ioi 0)).withDensity
      (fun tau => ENNReal.ofReal (tauDensity tau))) = _
  have hw : Measurable (fun tau => ENNReal.ofReal (tauDensity tau)) := by
    unfold tauDensity
    fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hw
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with tau htau
  have hwpos : 0 ≤ tauDensity tau := actualKLWeight_nonneg htau.le
  rw [ENNReal.toReal_ofReal hwpos]
  rfl

/-- The exact pre-existing raw Lp transform has the original physical norm. -/
theorem rawKLTestTransform_norm (T : RadialTest) :
    ‖rawKLTestTransform T‖ = ‖radialCoreL2 T‖ := by
  have hsq : ‖rawKLTestTransform T‖ ^ 2 = ‖radialCoreL2 T‖ ^ 2 := by
    rw [rawKLTestTransform_norm_sq_integral, tau_norm_integral_eq_actual_energy]
    exact actualKL_compact_integral_norm T
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The actual integral map on physical compact-core vectors preserves norm,
with representative independence already supplied by the core construction. -/
theorem actualCoreKLTransform_norm (F : compactPhysicalCore) :
    ‖actualCoreKLTransform F‖ = ‖(F : RadialL2)‖ := by
  change ‖rawKLTestTransform (coreRepresentative F)‖ = _
  rw [rawKLTestTransform_norm, coreRepresentative_spec]

end
end ImbalancedChen.Part3.ActualKLCompactPlancherel20261025a
