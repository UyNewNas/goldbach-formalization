import ImbalancedChen.Part3GenericGlobalContinuousCFC
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The native RMK scalar measure of an arbitrary vector equals the sum of its
literal squared-coordinate weighted cyclic measures. The index is unrestricted:
finite mass is obtained from the Hilbert-sum norm, and native Bochner integration
over a sum of measures does not require countability once integrability holds.
No spectral measure, CFC representation, or Borel identity is assumed.
-/

namespace ImbalancedChen.Part3.GenericGlobalScalarMeasureConsistency20261025a
noncomputable section
open MeasureTheory
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventCyclicL2Representation20261025a
open ImbalancedChen.Part3.GenericResolventGlobalSpectralAssembly20261025a
open ImbalancedChen.Part3.GenericGlobalContinuousCFC20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

theorem scalarL2_norm_square (f : H) (ξ : ScalarL2 R hSA f) :
    ‖ξ‖ ^ 2 = ∫ t, ‖ξ t‖ ^ 2 ∂scalarMeasure R hSA f := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def]
  simp_rw [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  simpa only [integral_complex_ofReal, Complex.ofReal_re]

theorem scalarL2_integrable_norm_square (f : H) (ξ : ScalarL2 R hSA f) :
    Integrable (fun t => ‖ξ t‖ ^ 2) (scalarMeasure R hSA f) :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable ξ)).mp (Lp.memLp ξ)

def squaredCoordinateMeasure (f : H) (ξ : ScalarL2 R hSA f) :
    Measure (ResolventSpectrum R) :=
  (scalarMeasure R hSA f).withDensity (fun t => ENNReal.ofReal (‖ξ t‖ ^ 2))

theorem squaredCoordinateMeasure_univ (f : H) (ξ : ScalarL2 R hSA f) :
    squaredCoordinateMeasure R hSA f ξ Set.univ = ENNReal.ofReal (‖ξ‖ ^ 2) := by
  unfold squaredCoordinateMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (scalarL2_integrable_norm_square R hSA f ξ)
    (Filter.Eventually.of_forall (fun t => sq_nonneg ‖ξ t‖)),
    ← scalarL2_norm_square]

instance squaredCoordinateMeasure_finite (f : H) (ξ : ScalarL2 R hSA f) :
    IsFiniteMeasure (squaredCoordinateMeasure R hSA f ξ) where
  measure_univ_lt_top := by
    rw [squaredCoordinateMeasure_univ]
    exact ENNReal.ofReal_lt_top

instance squaredCoordinateMeasure_regular (f : H) (ξ : ScalarL2 R hSA f) :
    (squaredCoordinateMeasure R hSA f ξ).Regular := by infer_instance

theorem squaredCoordinateMeasure_integral (f : H) (ξ : ScalarL2 R hSA f)
    (φ : C(ResolventSpectrum R, ℂ)) :
    (∫ t, φ t ∂squaredCoordinateMeasure R hSA f ξ) =
      ∫ t, φ t * ((‖ξ t‖ ^ 2 : ℝ) : ℂ) ∂scalarMeasure R hSA f := by
  unfold squaredCoordinateMeasure
  have hm : AEMeasurable (fun t => ENNReal.ofReal (‖ξ t‖ ^ 2))
      (scalarMeasure R hSA f) :=
    ((Lp.aestronglyMeasurable ξ).norm.pow 2).aemeasurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul₀ hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), Complex.real_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => mul_comm _ _)

def coordinateSumMeasure (ξ : SpectralSum R hSA) : Measure (ResolventSpectrum R) :=
  Measure.sum (fun i : SpectralIndex R hSA => squaredCoordinateMeasure R hSA (i : H) (ξ i))

theorem spectralSum_norm_square_summable (ξ : SpectralSum R hSA) :
    Summable (fun i : SpectralIndex R hSA => ‖ξ i‖ ^ 2) := by
  have h := (lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) ξ).summable
  simpa using h

instance coordinateSumMeasure_finite (ξ : SpectralSum R hSA) :
    IsFiniteMeasure (coordinateSumMeasure R hSA ξ) where
  measure_univ_lt_top := by
    unfold coordinateSumMeasure
    rw [Measure.sum_apply _ MeasurableSet.univ]
    simp_rw [squaredCoordinateMeasure_univ]
    exact (spectralSum_norm_square_summable R hSA ξ).tsum_ofReal_lt_top

instance coordinateSumMeasure_regular (ξ : SpectralSum R hSA) :
    (coordinateSumMeasure R hSA ξ).Regular := by infer_instance

theorem coordinateSumMeasure_continuous_integral (ξ : SpectralSum R hSA)
    (φ : C(ResolventSpectrum R, ℂ)) :
    (∫ t, φ t ∂coordinateSumMeasure R hSA ξ) =
      ∑' i : SpectralIndex R hSA,
        ∫ t, φ t * ((‖ξ i t‖ ^ 2 : ℝ) : ℂ) ∂scalarMeasure R hSA (i : H) := by
  have hi : Integrable φ (coordinateSumMeasure R hSA ξ) :=
    φ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace φ)
  rw [coordinateSumMeasure, integral_sum_measure hi]
  exact tsum_congr fun i => squaredCoordinateMeasure_integral R hSA (i : H) (ξ i) φ

/-- Measure uniqueness follows only after the actual all-continuous CFC
conjugacy has supplied every continuous test. -/
theorem scalarMeasure_eq_coordinateSumMeasure (u : H) :
    scalarMeasure R hSA u =
      coordinateSumMeasure R hSA ((spectralUnitary R hSA).symm u) := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  have hleft := scalarMeasure_continuous_test_sum R hSA u
    (complexOfReal R φ.toContinuousMap)
  have hright := coordinateSumMeasure_continuous_integral R hSA
    ((spectralUnitary R hSA).symm u) (complexOfReal R φ.toContinuousMap)
  have hcomplex := hleft.trans hright.symm
  change (∫ t, (φ t : ℂ) ∂scalarMeasure R hSA u) =
    ∫ t, (φ t : ℂ) ∂coordinateSumMeasure R hSA ((spectralUnitary R hSA).symm u) at hcomplex
  simpa only [integral_complex_ofReal, Complex.ofReal_inj] using hcomplex

/-- Literal Borel mass identity, including arbitrary cardinality of the
Zorn family. No projection identification is an input. -/
theorem scalarMeasure_borel_fiber_formula (u : H) (B : Set (ResolventSpectrum R))
    (hB : MeasurableSet B) :
    scalarMeasure R hSA u B =
      ∑' i : SpectralIndex R hSA,
        ∫⁻ t in B, ENNReal.ofReal (‖((spectralUnitary R hSA).symm u i) t‖ ^ 2)
          ∂scalarMeasure R hSA (i : H) := by
  rw [scalarMeasure_eq_coordinateSumMeasure, coordinateSumMeasure, Measure.sum_apply _ hB]
  apply tsum_congr
  intro i
  exact withDensity_apply _ hB

end
end ImbalancedChen.Part3.GenericGlobalScalarMeasureConsistency20261025a