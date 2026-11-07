import ImbalancedChen.Part3ActualKLCoordinateMeasures
import ImbalancedChen.Part3ActualGreenStoneBoundaryIntegral

/-!
# The actual finite KL density candidate in the lambda coordinate

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

This is an actual with-density measure, with literal K-transform square.
Its finite total mass comes from the already proved weighted-KL L2 bound
and the genuine square-root measure transport, not from Plancherel.
It is not identified with the native spectral measure in this module.
-/

namespace ImbalancedChen.Part3.ActualKLCompactDensityMeasure20261025a

noncomputable section
open Set MeasureTheory
open scoped ENNReal
open RadialSchrodingerL2Form20261025a ActualKLCoordinateMeasures20261025a
open ActualKLCompactTestIntegrationByParts20261025a ActualKLCompactTestWeightedL220261025a
open ActualGreenStoneBoundaryIntegral20261025a

def compactLambdaDensity (F : RadialTest) (lambda : ℝ) : ℝ :=
  actualCompactLambdaDensity F.function lambda

def compactKLDensityMeasure (F : RadialTest) : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Ioi 0)).withDensity
    (fun lambda => ENNReal.ofReal (compactLambdaDensity F lambda))

theorem compactLambdaDensity_eq_energyDensity (F : RadialTest) (lambda : ℝ) :
    compactLambdaDensity F lambda = energyDensity lambda *
      ‖actualKtransform F.function (Real.sqrt lambda)‖ ^ 2 := rfl

theorem energyDensity_nonneg (lambda : ℝ) : 0 ≤ energyDensity lambda := by
  unfold energyDensity
  exact div_nonneg
    (Real.sinh_nonneg_iff.mpr (mul_nonneg Real.pi_pos.le (Real.sqrt_nonneg lambda)))
    (sq_nonneg _)

theorem compactLambdaDensity_nonneg (F : RadialTest) (lambda : ℝ) :
    0 ≤ compactLambdaDensity F lambda :=
  mul_nonneg (energyDensity_nonneg lambda) (sq_nonneg _)

theorem compactLambdaDensity_measurable (F : RadialTest) : Measurable (compactLambdaDensity F) := by
  have hT := (actualKtransform_stronglyMeasurable F).measurable
  exact (show Measurable energyDensity by unfold energyDensity; fun_prop).mul
    ((hT.comp Real.continuous_sqrt.measurable).norm.pow 2)

/-- The candidate lambda mass is the actual weighted transform energy,
through the genuine tau^2 Jacobian. No norm equality is used here. -/
theorem compactLambdaDensity_lintegral_eq_tau_energy (F : RadialTest) :
    (∫⁻ lambda in Ioi (0 : ℝ), ENNReal.ofReal (compactLambdaDensity F lambda)) =
      ∫⁻ tau in Ioi (0 : ℝ), ENNReal.ofReal (actualKLEnergy F tau) := by
  let g : ℝ → ℝ≥0∞ := fun tau => ENNReal.ofReal (‖actualKtransform F.function tau‖ ^ 2)
  have hg : Measurable g :=
    ((actualKtransform_stronglyMeasurable F).measurable.norm.pow 2).ennreal_ofReal
  have henergyMeas : Measurable (fun lambda => ENNReal.ofReal (energyDensity lambda)) := by
    unfold energyDensity
    fun_prop
  have htauMeas : Measurable (fun tau => ENNReal.ofReal (tauDensity tau)) := by
    unfold tauDensity
    fun_prop
  calc
    _ = ∫⁻ lambda in Ioi (0 : ℝ),
        ENNReal.ofReal (energyDensity lambda) * g (Real.sqrt lambda) := by
      apply lintegral_congr_ae
      apply Filter.Eventually.of_forall
      intro lambda
      exact ENNReal.ofReal_mul (energyDensity_nonneg lambda)
    _ = ∫⁻ lambda, g (Real.sqrt lambda) ∂energyMeasure := by
      symm
      exact lintegral_withDensity_eq_lintegral_mul _ henergyMeas
        (hg.comp Real.continuous_sqrt.measurable)
    _ = ∫⁻ tau, g tau ∂tauMeasure := (lintegral_tauMeasure g hg).symm
    _ = ∫⁻ tau in Ioi (0 : ℝ), ENNReal.ofReal (tauDensity tau) * g tau :=
      lintegral_withDensity_eq_lintegral_mul _ htauMeas hg
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with tau htau
      change ENNReal.ofReal (actualKLWeight tau) *
        ENNReal.ofReal (‖actualKtransform F.function tau‖ ^ 2) =
          ENNReal.ofReal (actualKLWeight tau * ‖actualKtransform F.function tau‖ ^ 2)
      exact (ENNReal.ofReal_mul (actualKLWeight_nonneg htau.le)).symm

theorem actualKLEnergy_ae_nonneg (F : RadialTest) :
    0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioi 0)] actualKLEnergy F := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with tau htau
  exact mul_nonneg (actualKLWeight_nonneg htau.le) (sq_nonneg _)

theorem compactKLDensityMeasure_univ (F : RadialTest) :
    compactKLDensityMeasure F univ =
      ENNReal.ofReal (∫ tau in Ioi (0 : ℝ), actualKLEnergy F tau) := by
  rw [compactKLDensityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    compactLambdaDensity_lintegral_eq_tau_energy]
  exact (ofReal_integral_eq_lintegral_ofReal
    (actualKtransform_KL_weighted_square_integrable F) (actualKLEnergy_ae_nonneg F)).symm

instance compactKLDensityMeasure_finite (F : RadialTest) : IsFiniteMeasure (compactKLDensityMeasure F) where
  measure_univ_lt_top := by rw [compactKLDensityMeasure_univ]; exact ENNReal.ofReal_lt_top

theorem compactKLDensityMeasure_singleton (F : RadialTest) (x : ℝ) :
    compactKLDensityMeasure F ({x} : Set ℝ) = 0 := measure_singleton x

theorem compactKLDensityMeasure_nonpositive (F : RadialTest) :
    compactKLDensityMeasure F (Iic 0) = 0 := by
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply measurableSet_Iic]
  have hset : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and]
    exact fun h => not_lt_of_ge h
  rw [hset, measure_empty]

theorem compactLambdaDensity_integrable (F : RadialTest) :
    IntegrableOn (compactLambdaDensity F) (Ioi (0 : ℝ)) := by
  refine ⟨(compactLambdaDensity_measurable F).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (compactLambdaDensity_nonneg F))).mpr
  rw [compactLambdaDensity_lintegral_eq_tau_energy,
    ← ofReal_integral_eq_lintegral_ofReal
      (actualKtransform_KL_weighted_square_integrable F) (actualKLEnergy_ae_nonneg F)]
  exact ENNReal.ofReal_lt_top

/-- Exact open-interval mass in the Stone lambda coordinate. -/
theorem compactKLDensityMeasure_real_Ioo (F : RadialTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (compactKLDensityMeasure F).real (Ioo a b) =
      ∫ lambda in a..b, compactLambdaDensity F lambda := by
  have hsub : Ioo a b ⊆ Ioi (0 : ℝ) := fun x hx => ha.trans hx.1
  have hi : IntegrableOn (compactLambdaDensity F) (Ioo a b) :=
    (compactLambdaDensity_integrable F).mono_set hsub
  have hmass : compactKLDensityMeasure F (Ioo a b) =
      ENNReal.ofReal (∫ lambda in Ioo a b, compactLambdaDensity F lambda) := by
    rw [compactKLDensityMeasure, withDensity_apply _ measurableSet_Ioo,
      Measure.restrict_restrict measurableSet_Ioo, inter_eq_left.mpr hsub]
    exact (ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (compactLambdaDensity_nonneg F))).symm
  rw [measureReal_def, hmass, ENNReal.toReal_ofReal
    (integral_nonneg (fun lambda => compactLambdaDensity_nonneg F lambda))]
  rw [intervalIntegral.integral_of_le hab, ← integral_Ioo_eq_integral_Ioc]

end
end ImbalancedChen.Part3.ActualKLCompactDensityMeasure20261025a
