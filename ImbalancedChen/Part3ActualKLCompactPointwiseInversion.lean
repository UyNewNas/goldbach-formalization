import ImbalancedChen.Part3ActualKLCompactPlancherel
import ImbalancedChen.Part3ActualKLInversionFubini
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Actual pointwise KL inversion of compact smooth radial tests

The actual compact norm theorem and the actual core linear map determine
the polarized transform pairing. Genuine Fubini identifies this with the
pairing of the absolutely convergent inverse integral. Native smooth-test
separation gives equality almost everywhere, and the independently proved
continuity of that integral upgrades it to equality at every radial point.

No norm equality, Plancherel, inversion, Fubini, or continuity is supplied
as a hypothesis. The imported actual compact Plancherel source is frozen;
its norm conclusion is used directly for the already defined core map.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualKLCompactPointwiseInversion20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open RadialSchrodingerL2Form20261025a ComplexOrderKBridgeSourceOnly
open ActualKLCoreTransform20261025a ActualKLCompactPlancherel20261025a
open ActualKLCoordinateMeasures20261025a ActualKLCompactTestWeightedL220261025a
open ActualKLCompactTestIntegrationByParts20261025a ActualKLInversionBounds20261025a
open ActualKLInversionContinuity20261025a ActualKLInversionFubini20261025a

/-- Polarization of the proved norm equality for the actual linear core
map. The isometry here is local to the proof, not a separately assumed map. -/
theorem rawKLTestTransform_inner (T U : RadialTest) :
    inner ℂ (rawKLTestTransform U) (rawKLTestTransform T) =
      inner ℂ (radialCoreL2 U) (radialCoreL2 T) := by
  let L : compactPhysicalCore →ₗᵢ[ℂ] RawTauL2 :=
    { actualCoreKLTransform with
      norm_map' := fun F => actualCoreKLTransform_norm F }
  have h := L.inner_map_map (physicalCoreVector U) (physicalCoreVector T)
  change inner ℂ (actualCoreKLTransform (physicalCoreVector U))
      (actualCoreKLTransform (physicalCoreVector T)) =
    inner ℂ (radialCoreL2 U) (radialCoreL2 T) at h
  simpa only [actualCoreKLTransform_on_test] using h

theorem physical_core_inner_integral (T U : RadialTest) :
    inner ℂ (radialCoreL2 U) (radialCoreL2 T) =
      ∫ r : ℝ, T.function r * star (U.function r) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [U.function_memLp.coeFn_toLp, T.function_memLp.coeFn_toLp]
    with r hU hT
  change inner ℂ (U.function_memLp.toLp U.function r)
      (T.function_memLp.toLp T.function r) = T.function r * star (U.function r)
  simp only [hU, hT, RCLike.inner_apply]

theorem raw_core_inner_integral (T U : RadialTest) :
    inner ℂ (rawKLTestTransform U) (rawKLTestTransform T) =
      ∫ tau in Ioi (0 : ℝ), (actualKLWeight tau : ℂ) *
        actualKtransform T.function tau * star (actualKtransform U.function tau) := by
  calc
    _ = ∫ tau : ℝ, actualKtransform T.function tau *
        star (actualKtransform U.function tau) ∂tauMeasure := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [rawKLTestTransform_ae U, rawKLTestTransform_ae T]
        with tau hU hT
      simp only [hU, hT, RCLike.inner_apply]
    _ = _ := by
      unfold tauMeasure positiveDensityMeasure
      rw [integral_withDensity_eq_integral_toReal_smul
        (show Measurable (fun tau : ℝ => ENNReal.ofReal (tauDensity tau)) by
          unfold tauDensity
          fun_prop)
        (Eventually.of_forall (fun tau => ENNReal.ofReal_lt_top))]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with tau htau
      rw [tauDensity_eq_actualKLWeight,
        ENNReal.toReal_ofReal (actualKLWeight_nonneg htau.le)]
      simp only [Complex.real_smul]
      ring

/-- Actual compact polarized Parseval identity, extracted from the
concrete compact norm theorem rather than passed as a supplier premise. -/
theorem actualKtransform_compact_parseval (T U : RadialTest) :
    (∫ tau in Ioi (0 : ℝ), (actualKLWeight tau : ℂ) *
      actualKtransform T.function tau * star (actualKtransform U.function tau)) =
      ∫ r : ℝ, T.function r * star (U.function r) := by
  rw [← raw_core_inner_integral, rawKLTestTransform_inner, physical_core_inner_integral]

theorem actualKLInverse_smooth_test_pairing (T U : RadialTest) :
    (∫ r : ℝ, actualKLInverse T r * star (U.function r)) =
      ∫ r : ℝ, T.function r * star (U.function r) := by
  rw [actualKLInverse_compact_test_pairing T U.smooth.continuous U.compact,
    actualKtransform_compact_parseval]

/-- Native smooth-test separation produces actual equality almost
everywhere only after both true integral pairings have been identified. -/
theorem actualKLInverse_ae (T : RadialTest) :
    actualKLInverse T =ᵐ[(volume : Measure ℝ)] T.function := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (actualKLInverse_continuous T).locallyIntegrable T.smooth.continuous.locallyIntegrable
  intro g hg hgc
  let U : RadialTest :=
    { function := fun r : ℝ => (g r : ℂ)
      smooth := by fun_prop
      compact := hgc.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp) }
  have h := actualKLInverse_smooth_test_pairing T U
  simpa [U, Complex.real_smul, mul_comm] using h

/-- The inverse integral is genuinely continuous, so equality is
pointwise, not merely equality of L2 representatives. -/
theorem actualKLInverse_eq (T : RadialTest) : actualKLInverse T = T.function :=
  MeasureTheory.eq_of_ae_eq (actualKLInverse_ae T)
    (actualKLInverse_continuous T) T.smooth.continuous

/-- Pointwise inversion for the literal K_(i*tau) integral with raw
normalization 2/pi^2. It holds at every real radial coordinate r. -/
theorem actualKL_compact_pointwise_inversion (T : RadialTest) (r : ℝ) :
    (∫ tau in Ioi (0 : ℝ),
      (((2 / Real.pi ^ 2) * tau * Real.sinh (Real.pi * tau) : ℝ) : ℂ) *
        actualKtransform T.function tau *
        complexOrderK ((tau : ℂ) * Complex.I) (Real.exp r)) = T.function r :=
  congrFun (actualKLInverse_eq T) r

end
end ImbalancedChen.Part3.ActualKLCompactPointwiseInversion20261025a
