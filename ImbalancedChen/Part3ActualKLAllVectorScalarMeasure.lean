import ImbalancedChen.Part3ActualKLOntoUnitary
import ImbalancedChen.Part3ActualKLScalarMeasureIdentification
import ImbalancedChen.Part3ActualRadialScalarEndpointAtoms
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

All-vector scalar-measure identification for the actual radial KL unitary.
The native compact tests are derived from the SAME bounded resolvent CFC:
compact support supplies the zero extension at its zero spectral endpoint.
The raw compact tests are bounded multiplier quadratic forms. Continuity
on physical L2 and the actual dense compact core then identify the finite
regular measures. Neither continuity of the measures nor a target spectral
identity, norm identity, range premise, or new unitary is assumed.

The raw measure is (2/pi^2)*tau*sinh(pi*tau) d tau on tau>0.
There is no automorphic quotient or dt/cosh(pi*t) assertion.
-/

namespace ImbalancedChen.Part3.ActualKLAllVectorScalarMeasure20261026a

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open RadialSchrodingerL2Form20261025a
open ActualKLCoreTransform20261025a ActualKLCoordinateMeasures20261025a
open ActualKLOntoUnitary20261025a
open ActualKLCompactTestIntegrationByParts20261025a ActualKLCompactTestWeightedL220261025a
open ActualKLCompactDensityMeasure20261025a ActualKLScalarMeasureIdentification20261025a
open ActualRadialCompactScalarStone20261025a
open GenericResolventScalarMeasure20261025a GenericResolventScalarZeroAtom20261025a

/-- The compact spectral test extends by zero at the bounded endpoint.
Its value there need not agree with phi(-1); that fiber is native null. -/
def nativeCompactLiftFunction (φ : C_c(ℝ, ℝ)) (t : RadialBoundedSpectrum) : ℝ :=
  if (t : ℝ) = 0 then 0 else φ (radialSpectralLambda t)

theorem nativeCompactLiftFunction_continuous (φ : C_c(ℝ, ℝ)) :
    Continuous (nativeCompactLiftFunction φ) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : (t : ℝ) = 0
  · obtain ⟨B, hB⟩ := φ.hasCompactSupport.isCompact.bddAbove
    let C : ℝ := max B 0 + 2
    have hC : 0 < C + 1 := by dsimp [C]; positivity
    have hδ : 0 < (C + 1)⁻¹ := inv_pos.mpr hC
    have hev : ∀ᶠ s : RadialBoundedSpectrum in 𝓝 t,
        (s : ℝ) < (C + 1)⁻¹ :=
      (isOpen_lt continuous_subtype_val continuous_const).mem_nhds (by simpa [ht] using hδ)
    apply (continuousAt_const : ContinuousAt (fun _ : RadialBoundedSpectrum => (0 : ℝ)) t).
      congr_of_eventuallyEq
    filter_upwards [hev] with s hs
    by_cases hs0 : (s : ℝ) = 0
    · simp only [nativeCompactLiftFunction, if_pos hs0]
    · have hnonneg := (spectrum_coordinate_mem_unitInterval radialUnitShiftResolvent
        radialUnitShiftResolvent_nonneg radialUnitShiftResolvent_opNorm_le_one s).1
      have hpos : 0 < (s : ℝ) := lt_of_le_of_ne hnonneg (Ne.symm hs0)
      have hmul : (s : ℝ) * (C + 1) < 1 := by
        have h := mul_lt_mul_of_pos_right hs hC
        simpa only [inv_mul_cancel₀ hC.ne'] using h
      have hinv : C + 1 < (s : ℝ)⁻¹ := by
        rw [← one_div]
        exact (lt_div_iff₀ hpos).2 (by simpa only [mul_comm] using hmul)
      have hλ : B < radialSpectralLambda s := by
        dsimp only [radialSpectralLambda]
        have hBC : B ≤ C := by dsimp [C]; linarith [le_max_left B 0]
        linarith
      have hout : radialSpectralLambda s ∉ tsupport φ := by
        intro hm
        exact not_lt_of_ge (hB hm) hλ
      simp only [nativeCompactLiftFunction, if_neg hs0, image_eq_zero_of_notMem_tsupport hout]
  · have hev : ∀ᶠ s : RadialBoundedSpectrum in 𝓝 t, (s : ℝ) ≠ 0 :=
      (isOpen_ne continuous_subtype_val continuous_const).mem_nhds ht
    have hc : ContinuousAt (fun s : RadialBoundedSpectrum => φ (radialSpectralLambda s)) t :=
      φ.continuous.continuousAt.comp
        ((continuousAt_subtype_val.inv₀ ht).sub continuousAt_const)
    apply hc.congr_of_eventuallyEq
    filter_upwards [hev] with s hs
    simp only [nativeCompactLiftFunction, if_neg hs]

def nativeCompactLift (φ : C_c(ℝ, ℝ)) : C(RadialBoundedSpectrum, ℝ) :=
  ⟨nativeCompactLiftFunction φ, nativeCompactLiftFunction_continuous φ⟩

def nativeCompactOperator (φ : C_c(ℝ, ℝ)) : RadialL2 →L[ℂ] RadialL2 :=
  resolventCFC radialUnitShiftResolvent radialUnitShiftResolvent_selfAdjoint (nativeCompactLift φ)

theorem native_compact_test_quadratic (φ : C_c(ℝ, ℝ)) (F : RadialL2) :
    (∫ λ : ℝ, φ λ ∂radialUnboundedScalarMeasure F) =
      (inner ℂ F (nativeCompactOperator φ F)).re := by
  rw [radialUnboundedScalarMeasure,
    integral_map_of_stronglyMeasurable radialSpectralLambda_measurable
      φ.continuous.stronglyMeasurable]
  have hae : (fun t : RadialBoundedSpectrum => φ (radialSpectralLambda t)) =ᵐ[
      radialBoundedScalarMeasure F] nativeCompactLift φ := by
    filter_upwards [scalarMeasure_ae_coordinate_ne_zero radialUnitShiftResolvent
      radialUnitShiftResolvent_selfAdjoint radialUnitShiftResolvent_injective F] with t ht
    simp only [nativeCompactLift, nativeCompactLiftFunction, ContinuousMap.coe_mk, if_neg ht]
  rw [integral_congr_ae hae]
  exact scalarMeasure_integral radialUnitShiftResolvent
    radialUnitShiftResolvent_selfAdjoint F (nativeCompactLift φ)

theorem native_compact_test_continuous (φ : C_c(ℝ, ℝ)) :
    Continuous (fun F : RadialL2 => ∫ λ : ℝ, φ λ ∂radialUnboundedScalarMeasure F) := by
  simp_rw [native_compact_test_quadratic]
  exact Complex.continuous_re.comp
    (continuous_id.inner (nativeCompactOperator φ).continuous)

def amplitudeMeasure (g : RawTauL2) : Measure ℝ :=
  tauMeasure.withDensity (fun τ => ENNReal.ofReal (‖g τ‖ ^ 2))

theorem amplitudeMeasure_representative (g : RawTauL2) (g₀ : ℝ → ℂ)
    (hg₀ : g₀ =ᵐ[tauMeasure] g) :
    tauMeasure.withDensity (fun τ => ENNReal.ofReal (‖g₀ τ‖ ^ 2)) = amplitudeMeasure g := by
  apply withDensity_congr_ae
  filter_upwards [hg₀] with τ hτ
  rw [hτ]

theorem raw_norm_sq_integral (g : RawTauL2) :
    ‖g‖ ^ 2 = ∫ τ : ℝ, ‖g τ‖ ^ 2 ∂tauMeasure := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) g g)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun τ => by
    simp only [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.ofReal_re])

theorem amplitudeMeasure_univ (g : RawTauL2) :
    amplitudeMeasure g univ = ENNReal.ofReal (‖g‖ ^ 2) := by
  have hi : Integrable (fun τ => ‖g τ‖ ^ 2) tauMeasure :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  rw [amplitudeMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall (fun τ => sq_nonneg ‖g τ‖)), ← raw_norm_sq_integral]

instance amplitudeMeasure_finite (g : RawTauL2) : IsFiniteMeasure (amplitudeMeasure g) where
  measure_univ_lt_top := by rw [amplitudeMeasure_univ]; exact ENNReal.ofReal_lt_top

def klScalarMeasure (F : RadialL2) : Measure ℝ :=
  (amplitudeMeasure (actualKLUnitary F)).map (fun τ : ℝ => τ ^ 2)

instance klScalarMeasure_finite (F : RadialL2) : IsFiniteMeasure (klScalarMeasure F) := by
  unfold klScalarMeasure
  infer_instance

instance klScalarMeasure_regular (F : RadialL2) : (klScalarMeasure F).Regular := by
  infer_instance

def rawCompactMultiply (φ : C_c(ℝ, ℝ)) (g : RawTauL2) (τ : ℝ) : ℂ :=
  (φ (τ ^ 2) : ℂ) * g τ

theorem rawCompactMultiply_memLp (φ : C_c(ℝ, ℝ)) (g : RawTauL2) :
    MemLp (rawCompactMultiply φ g) 2 tauMeasure := by
  apply (Lp.memLp g).of_le_mul
    ((Complex.continuous_ofReal.comp (φ.continuous.comp (continuous_id.pow 2))).
      aestronglyMeasurable.mul (Lp.aestronglyMeasurable g))
  exact Eventually.of_forall fun τ => by
    rw [rawCompactMultiply, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [Complex.norm_real, Real.norm_eq_abs] using
        φ.toBoundedContinuousFunction.norm_coe_le_norm (τ ^ 2)) (norm_nonneg _)

def rawCompactL2 (φ : C_c(ℝ, ℝ)) (g : RawTauL2) : RawTauL2 :=
  (rawCompactMultiply_memLp φ g).toLp (rawCompactMultiply φ g)

theorem rawCompactL2_coe_ae (φ : C_c(ℝ, ℝ)) (g : RawTauL2) :
    rawCompactL2 φ g =ᵐ[tauMeasure] rawCompactMultiply φ g :=
  (rawCompactMultiply_memLp φ g).coeFn_toLp

def rawCompactLinear (φ : C_c(ℝ, ℝ)) : RawTauL2 →ₗ[ℂ] RawTauL2 where
  toFun := rawCompactL2 φ
  map_add' g h := by
    apply Lp.ext
    filter_upwards [rawCompactL2_coe_ae φ (g + h), Lp.coeFn_add g h,
      Lp.coeFn_add (rawCompactL2 φ g) (rawCompactL2 φ h),
      rawCompactL2_coe_ae φ g, rawCompactL2_coe_ae φ h] with τ hl hi hr hg hh
    rw [hl, hr, hg, hh]
    simp only [rawCompactMultiply, hi, mul_add]
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [rawCompactL2_coe_ae φ (c • g), Lp.coeFn_smul c g,
      Lp.coeFn_smul c (rawCompactL2 φ g), rawCompactL2_coe_ae φ g] with τ hl hi hr hg
    rw [hl, hr, hg]
    simp only [rawCompactMultiply, hi, smul_eq_mul]
    ring

theorem rawCompactL2_norm_le (φ : C_c(ℝ, ℝ)) (g : RawTauL2) :
    ‖rawCompactL2 φ g‖ ≤ ‖φ.toBoundedContinuousFunction‖ * ‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [rawCompactL2_coe_ae φ g] with τ hτ
  rw [hτ, rawCompactMultiply, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using
      φ.toBoundedContinuousFunction.norm_coe_le_norm (τ ^ 2)) (norm_nonneg _)

def rawCompactOperator (φ : C_c(ℝ, ℝ)) : RawTauL2 →L[ℂ] RawTauL2 :=
  (rawCompactLinear φ).mkContinuous ‖φ.toBoundedContinuousFunction‖ (rawCompactL2_norm_le φ)

theorem kl_compact_test_integral (φ : C_c(ℝ, ℝ)) (F : RadialL2) :
    (∫ λ : ℝ, φ λ ∂klScalarMeasure F) =
      ∫ τ : ℝ, φ (τ ^ 2) * ‖actualKLUnitary F τ‖ ^ 2 ∂tauMeasure := by
  rw [klScalarMeasure,
    integral_map_of_stronglyMeasurable (by fun_prop) φ.continuous.stronglyMeasurable,
    amplitudeMeasure, integral_withDensity_eq_integral_toReal_smul₀
      (((Lp.aestronglyMeasurable (actualKLUnitary F)).norm.pow 2).aemeasurable.ennreal_ofReal)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun τ => mul_comm _ _)

theorem kl_compact_test_quadratic (φ : C_c(ℝ, ℝ)) (F : RadialL2) :
    (∫ λ : ℝ, φ λ ∂klScalarMeasure F) =
      (inner ℂ (actualKLUnitary F) (rawCompactOperator φ (actualKLUnitary F))).re := by
  rw [kl_compact_test_integral, L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) (actualKLUnitary F)
      (rawCompactOperator φ (actualKLUnitary F)))]
  apply integral_congr_ae
  filter_upwards [rawCompactL2_coe_ae φ (actualKLUnitary F)] with τ hτ
  change φ (τ ^ 2) * ‖actualKLUnitary F τ‖ ^ 2 =
    (inner ℂ (actualKLUnitary F τ) (rawCompactL2 φ (actualKLUnitary F) τ)).re
  rw [hτ]
  change φ (τ ^ 2) * ‖actualKLUnitary F τ‖ ^ 2 =
    (star (actualKLUnitary F τ) * ((φ (τ ^ 2) : ℂ) * actualKLUnitary F τ)).re
  rw [show star (actualKLUnitary F τ) * ((φ (τ ^ 2) : ℂ) * actualKLUnitary F τ) =
      (φ (τ ^ 2) : ℂ) * (star (actualKLUnitary F τ) * actualKLUnitary F τ) by ring,
    ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp

theorem kl_compact_test_continuous (φ : C_c(ℝ, ℝ)) :
    Continuous (fun F : RadialL2 => ∫ λ : ℝ, φ λ ∂klScalarMeasure F) := by
  simp_rw [kl_compact_test_quadratic]
  exact Complex.continuous_re.comp (actualKLUnitary.continuous.inner
    ((rawCompactOperator φ).continuous.comp actualKLUnitary.continuous))

theorem compact_density_test_transport (φ : C_c(ℝ, ℝ)) (T : RadialTest) :
    (∫ λ : ℝ, φ λ ∂compactKLDensityMeasure T) =
      ∫ τ : ℝ, φ (τ ^ 2) * ‖actualKtransform T.function τ‖ ^ 2 ∂tauMeasure := by
  have hED : Measurable energyDensity := by unfold energyDensity; fun_prop
  have hT := actualKtransform_stronglyMeasurable T
  let g : ℝ → ℝ := fun λ => φ λ * ‖actualKtransform T.function (Real.sqrt λ)‖ ^ 2
  have hg : StronglyMeasurable g := φ.continuous.stronglyMeasurable.mul
    ((hT.measurable.comp Real.continuous_sqrt.measurable).norm.pow 2).stronglyMeasurable
  calc
    _ = ∫ λ in Ioi (0 : ℝ), compactLambdaDensity T λ * φ λ := by
      rw [compactKLDensityMeasure, integral_withDensity_eq_integral_toReal_smul
        (compactLambdaDensity_measurable T).ennreal_ofReal
        (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      simp only [ENNReal.toReal_ofReal (compactLambdaDensity_nonneg T _), smul_eq_mul]
    _ = ∫ λ, g λ ∂energyMeasure := by
      rw [energyMeasure, positiveDensityMeasure, integral_withDensity_eq_integral_toReal_smul
        hED.ennreal_ofReal (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      simp only [ENNReal.toReal_ofReal (energyDensity_nonneg _), smul_eq_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun λ => by
        rw [compactLambdaDensity_eq_energyDensity]
        dsimp only [g]
        ring
    _ = ∫ τ, g (τ ^ 2) ∂tauMeasure := integral_energyMeasure g hg
    _ = _ := by
      apply integral_congr_ae
      have hp : ∀ᵐ τ ∂tauMeasure, 0 < τ :=
        (ae_restrict_mem measurableSet_Ioi).mono_ac (withDensity_absolutelyContinuous _ _)
      filter_upwards [hp] with τ hτ
      simp only [g, Real.sqrt_sq_eq_abs, abs_of_pos hτ]

/-- All physical L2 vectors, with their own native scalar measure.
The sole extension step is continuity on the proved actual dense core. -/
theorem native_scalarMeasure_eq_actualKL (F : RadialL2) :
    radialUnboundedScalarMeasure F = klScalarMeasure F := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  have heq : (fun G : RadialL2 => ∫ λ : ℝ, φ λ ∂radialUnboundedScalarMeasure G) =
      (fun G : RadialL2 => ∫ λ : ℝ, φ λ ∂klScalarMeasure G) := by
    apply (native_compact_test_continuous φ).ext_on radialCoreL2_range_dense
      (kl_compact_test_continuous φ)
    rintro _ ⟨T, rfl⟩
    change (∫ λ : ℝ, φ λ ∂compactRadialScalarMeasure T) = _
    rw [compactRadialScalarMeasure_eq_actual_KL_density,
      compact_density_test_transport, kl_compact_test_integral]
    apply integral_congr_ae
    filter_upwards [actualKLUnitary_on_test_ae T] with τ hτ
    rw [hτ]
  exact congrFun heq F

theorem native_scalarMeasure_eq_map_square_amplitude (F : RadialL2) :
    radialUnboundedScalarMeasure F =
      (tauMeasure.withDensity (fun τ => ENNReal.ofReal (‖actualKLUnitary F τ‖ ^ 2))).map
        (fun τ : ℝ => τ ^ 2) :=
  native_scalarMeasure_eq_actualKL F

end
end ImbalancedChen.Part3.ActualKLAllVectorScalarMeasure20261026a
