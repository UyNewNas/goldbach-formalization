import ImbalancedChen.Part3GenericResolventScalarMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Actual coordinate-square weighting of generic scalar spectral measures

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

For arbitrary complete complex Hilbert H, bounded self-adjoint R and f,
the genuinely constructed RMK measure of Rf equals t^2 times the RMK
measure of f. CFC multiplication and actual self-adjoint symmetry prove
the continuous-test identity; uniqueness of finite regular measures gives
the measure equality. No weighting, spectral vector realization, absence
of atoms, positivity or contraction conclusion is an input.
-/

namespace ImbalancedChen.Part3.GenericResolventWeightedScalarMeasure20261025a
noncomputable section
open MeasureTheory
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

def coordinateSquareDensity (t : ResolventSpectrum R) : ℝ≥0∞ :=
  ENNReal.ofReal ((t : ℝ) ^ 2)

theorem coordinateSquareDensity_measurable : Measurable (coordinateSquareDensity R) := by
  unfold coordinateSquareDensity
  fun_prop

def coordinateWeightedMeasure (f : H) : Measure (ResolventSpectrum R) :=
  (scalarMeasure R hSA f).withDensity (coordinateSquareDensity R)

instance coordinateWeightedMeasure_finite (f : H) :
    IsFiniteMeasure (coordinateWeightedMeasure R hSA f) := by
  have hi : Integrable (fun t : ResolventSpectrum R => (t : ℝ) ^ 2)
      (scalarMeasure R hSA f) :=
    (compactLift R (spectrumCoordinate R ^ 2)).integrable
  have hfin : (∫⁻ t : ResolventSpectrum R,
      ENNReal.ofReal ((t : ℝ) ^ 2) ∂scalarMeasure R hSA f) < ∞ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun t => sq_nonneg (t : ℝ)))).mp
      hi.hasFiniteIntegral
  exact Measure.isFiniteMeasure_withDensity hfin.ne

instance coordinateWeightedMeasure_regular (f : H) :
    (coordinateWeightedMeasure R hSA f).Regular := by infer_instance

/-- The literal coordinate-square CFC multiplier is R times the test
operator times R, including both applications to the vector. -/
theorem resolventCFC_coordinate_square_mul (φ : C(ResolventSpectrum R, ℝ)) :
    resolventCFC R hSA (spectrumCoordinate R ^ 2 * φ) =
      (R * resolventCFC R hSA φ) * R := by
  have hfun : spectrumCoordinate R ^ 2 * φ =
      spectrumCoordinate R * φ * spectrumCoordinate R := by
    ext t
    simp only [ContinuousMap.mul_apply, ContinuousMap.pow_apply]
    ring
  rw [hfun,map_mul,map_mul,resolventCFC_coordinate]

/-- Continuous-test weighting is derived from true CFC multiplication
and the self-adjoint inner identity, before measure uniqueness is used. -/
theorem scalarMeasure_apply_integral (f : H) (φ : C(ResolventSpectrum R, ℝ)) :
    (∫ t : ResolventSpectrum R, φ t ∂scalarMeasure R hSA (R f)) =
      ∫ t : ResolventSpectrum R, (t : ℝ) ^ 2 * φ t ∂scalarMeasure R hSA f := by
  have hweighted := scalarMeasure_integral R hSA f (spectrumCoordinate R ^ 2 * φ)
  change (∫ t : ResolventSpectrum R, (t : ℝ) ^ 2 * φ t ∂scalarMeasure R hSA f) =
    (inner ℂ f ((resolventCFC R hSA (spectrumCoordinate R ^ 2 * φ)) f)).re at hweighted
  rw [scalarMeasure_integral, hweighted, resolventCFC_coordinate_square_mul]
  change (inner ℂ (R f) ((resolventCFC R hSA φ) (R f))).re =
    (inner ℂ f (R ((resolventCFC R hSA φ) (R f)))).re
  exact congrArg Complex.re (hSA.isSymmetric f ((resolventCFC R hSA φ) (R f)))

theorem coordinateWeightedMeasure_integral (f : H) (φ : C(ResolventSpectrum R, ℝ)) :
    (∫ t : ResolventSpectrum R, φ t ∂coordinateWeightedMeasure R hSA f) =
      ∫ t : ResolventSpectrum R, (t : ℝ) ^ 2 * φ t ∂scalarMeasure R hSA f := by
  unfold coordinateWeightedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (coordinateSquareDensity_measurable R)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [coordinateSquareDensity, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

/-- The exact native measure identity μ_(Rf)=t² μ_f, for every bounded
self-adjoint R on every complete complex Hilbert space. -/
theorem scalarMeasure_apply (f : H) :
    scalarMeasure R hSA (R f) =
      (scalarMeasure R hSA f).withDensity (fun t : ResolventSpectrum R =>
        ENNReal.ofReal ((t : ℝ) ^ 2)) := by
  change scalarMeasure R hSA (R f) = coordinateWeightedMeasure R hSA f
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  rw [scalarMeasure_apply_integral R hSA f φ.toContinuousMap,
    coordinateWeightedMeasure_integral R hSA f φ.toContinuousMap]

/-- The exact Borel-set version of the weighting identity. -/
theorem scalarMeasure_apply_on (f : H) (B : Set (ResolventSpectrum R))
    (hB : MeasurableSet B) :
    scalarMeasure R hSA (R f) B =
      ∫⁻ t in B, ENNReal.ofReal ((t : ℝ) ^ 2) ∂scalarMeasure R hSA f := by
  rw [scalarMeasure_apply, Measure.withDensity_apply _ hB]

/-- In particular the zero-coordinate fiber has zero measure for every
vector in the actual RANGE of R, without an injectivity assumption. -/
theorem scalarMeasure_apply_zeroFiber (f : H) :
    scalarMeasure R hSA (R f) {t : ResolventSpectrum R | (t : ℝ) = 0} = 0 := by
  have hB : MeasurableSet {t : ResolventSpectrum R | (t : ℝ) = 0} := by fun_prop
  rw [scalarMeasure_apply_on R hSA f _ hB]
  have hzero : (fun t : ResolventSpectrum R => ENNReal.ofReal ((t : ℝ) ^ 2)) =ᵐ[
      (scalarMeasure R hSA f).restrict {t : ResolventSpectrum R | (t : ℝ) = 0}] (fun _ => 0) := by
    filter_upwards [ae_restrict_mem hB] with t ht
    simp only [Set.mem_setOf_eq] at ht
    simp only [ht, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero]
  rw [lintegral_congr_ae hzero,lintegral_zero]

end
end ImbalancedChen.Part3.GenericResolventWeightedScalarMeasure20261025a
