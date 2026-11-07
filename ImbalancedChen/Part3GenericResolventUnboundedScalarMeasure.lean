import ImbalancedChen.Part3GenericResolventScalarMeasure
import ImbalancedChen.Part3GenericResolventScalarZeroAtom
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
The actual RMK measure for any injective positive self-adjoint contraction
is transported by lambda = 1/t - 1. The zero-fiber theorem is consumed
from the independent generic weighted-measure argument. This file proves
nonnegative support, exact mass, recovery of the original measure, all
inverse-resolvent moments, and every positive shifted-resolvent integral.
There are no concrete Hilbert-space imports and no assumed measure or
no-atom conclusions. SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.Part3.GenericResolventUnboundedScalarMeasure20261025a

noncomputable section

open MeasureTheory Set Filter Topology
open ImbalancedChen.Part3.PositiveContractionResolventCalculus20261025a
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)
    (hpos : 0 ≤ R) (hnorm : ‖R‖ ≤ 1) (hinj : Function.Injective R)

theorem scalarMeasure_coordinate_pos_ae (f : H) :
    ∀ᵐ t : ResolventSpectrum R ∂scalarMeasure R hSA f, 0 < (t : ℝ) := by
  have hnot : ∀ᵐ t : ResolventSpectrum R ∂scalarMeasure R hSA f, (t : ℝ) ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using
      GenericResolventScalarZeroAtom20261025a.scalarMeasure_zeroFiber R hSA hinj f
  filter_upwards [hnot] with t ht
  exact lt_of_le_of_ne (spectrum_coordinate_mem_unitInterval R hpos hnorm t).1 (Ne.symm ht)

def spectralLambda (t : ResolventSpectrum R) : ℝ := (t : ℝ)⁻¹ - 1

theorem measurable_spectralLambda : Measurable (spectralLambda R) := by
  unfold spectralLambda
  fun_prop

theorem spectralLambda_nonneg {t : ResolventSpectrum R} (ht : 0 < (t : ℝ)) :
    0 ≤ spectralLambda R t := by
  have h : (1 : ℝ) ≤ 1 / (t : ℝ) :=
    (le_div_iff₀ ht).2 (by simpa using (spectrum_coordinate_mem_unitInterval R hpos hnorm t).2)
  simpa only [spectralLambda, one_div, sub_nonneg] using h

def unboundedScalarMeasure (f : H) : Measure ℝ :=
  (scalarMeasure R hSA f).map (spectralLambda R)

instance unboundedScalarMeasure_finite (f : H) :
    IsFiniteMeasure (unboundedScalarMeasure R hSA f) := by
  unfold unboundedScalarMeasure
  infer_instance

theorem unboundedScalarMeasure_Iio_zero (f : H) :
    unboundedScalarMeasure R hSA f (Iio 0) = 0 := by
  rw [unboundedScalarMeasure, Measure.map_apply (measurable_spectralLambda R) measurableSet_Iio]
  apply measure_mono_null (t := {t : ResolventSpectrum R | (t : ℝ) = 0}) ?_
    (GenericResolventScalarZeroAtom20261025a.scalarMeasure_zeroFiber R hSA hinj f)
  intro t ht
  change spectralLambda R t < 0 at ht
  by_contra hnot
  have hpos' : 0 < (t : ℝ) :=
    lt_of_le_of_ne (spectrum_coordinate_mem_unitInterval R hpos hnorm t).1 (Ne.symm hnot)
  exact not_lt_of_ge (spectralLambda_nonneg R hpos hnorm hpos') ht

theorem unboundedScalarMeasure_nonnegative_ae (f : H) :
    ∀ᵐ lambda : ℝ ∂unboundedScalarMeasure R hSA f, 0 ≤ lambda := by
  rw [ae_iff]
  simpa only [not_le] using unboundedScalarMeasure_Iio_zero R hSA hpos hnorm hinj f

theorem unboundedScalarMeasure_univ (f : H) :
    unboundedScalarMeasure R hSA f univ = ENNReal.ofReal (‖f‖ ^ 2) := by
  rw [unboundedScalarMeasure, Measure.map_apply (measurable_spectralLambda R) MeasurableSet.univ,
    preimage_univ]
  exact scalarMeasure_univ R hSA f

theorem unboundedScalarMeasure_mass (f : H) :
    (unboundedScalarMeasure R hSA f).real univ = ‖f‖ ^ 2 := by
  change (unboundedScalarMeasure R hSA f univ).toReal = _
  rw [unboundedScalarMeasure_univ, ENNReal.toReal_ofReal (sq_nonneg _)]

def resolventCoordinate (lambda : ℝ) : ℝ := 1 / (1 + lambda)

theorem measurable_resolventCoordinate : Measurable resolventCoordinate := by
  unfold resolventCoordinate
  fun_prop

theorem resolventCoordinate_spectralLambda (t : ResolventSpectrum R) :
    resolventCoordinate (spectralLambda R t) = (t : ℝ) := by
  unfold resolventCoordinate spectralLambda
  rw [show 1 + ((t : ℝ)⁻¹ - 1) = (t : ℝ)⁻¹ by ring, one_div, inv_inv]

theorem unboundedScalarMeasure_map_resolventCoordinate (f : H) :
    (unboundedScalarMeasure R hSA f).map resolventCoordinate =
      (scalarMeasure R hSA f).map (fun t : ResolventSpectrum R => (t : ℝ)) := by
  rw [unboundedScalarMeasure,
    Measure.map_map measurable_resolventCoordinate (measurable_spectralLambda R)]
  congr 1
  funext t
  exact resolventCoordinate_spectralLambda R t

theorem unboundedScalarMeasure_resolvent_moment (f : H) (n : ℕ) :
    (∫ lambda : ℝ, (resolventCoordinate lambda) ^ n ∂unboundedScalarMeasure R hSA f) =
      (inner ℂ f ((R ^ n) f)).re := by
  have hm : Measurable (fun lambda : ℝ => (resolventCoordinate lambda) ^ n) := by fun_prop
  rw [unboundedScalarMeasure,
    integral_map_of_stronglyMeasurable (measurable_spectralLambda R) hm.stronglyMeasurable]
  simp_rw [resolventCoordinate_spectralLambda]
  exact scalarMeasure_moment R hSA f n

theorem integrable_resolventCoordinate_pow (f : H) (n : ℕ) :
    Integrable (fun lambda : ℝ => (resolventCoordinate lambda) ^ n)
      (unboundedScalarMeasure R hSA f) := by
  have hm : Measurable (fun lambda : ℝ => (resolventCoordinate lambda) ^ n) := by fun_prop
  change Integrable _ ((scalarMeasure R hSA f).map (spectralLambda R))
  apply (integrable_map_measure hm.aestronglyMeasurable
    (measurable_spectralLambda R).aemeasurable).2
  have hcontinuous : Continuous (fun t : ResolventSpectrum R => (t : ℝ) ^ n) := by fun_prop
  have hi : Integrable (fun t : ResolventSpectrum R => (t : ℝ) ^ n) (scalarMeasure R hSA f) :=
    hcontinuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simpa only [Function.comp_apply, resolventCoordinate_spectralLambda] using hi

def scalarShiftedResolvent {a : ℝ} (ha : 0 < a) : C(ResolventSpectrum R, ℝ) :=
  ⟨fun t => resolventRatio a (t : ℝ),
    (continuousOn_resolventRatio R hpos hnorm ha).domRestrict⟩

theorem resolventCFC_scalarShiftedResolvent {a : ℝ} (ha : 0 < a) :
    resolventCFC R hSA (scalarShiftedResolvent R hpos hnorm ha) = shiftedResolvent R a := by
  exact (cfc_apply (resolventRatio a) R hSA
    (continuousOn_resolventRatio R hpos hnorm ha)).symm

theorem shifted_scalar_identity {a : ℝ} (ha : 0 < a) {t : ResolventSpectrum R}
    (ht : 0 < (t : ℝ)) :
    (a + spectralLambda R t)⁻¹ = scalarShiftedResolvent R hpos hnorm ha t := by
  have hd := denominator_pos ha (spectrum_coordinate_mem_unitInterval R hpos hnorm t)
  have hl : 0 < a + spectralLambda R t :=
    add_pos_of_pos_of_nonneg ha (spectralLambda_nonneg R hpos hnorm ht)
  change (a + spectralLambda R t)⁻¹ = resolventRatio a (t : ℝ)
  unfold spectralLambda at hl ⊢
  unfold resolventRatio denominator at hd ⊢
  field_simp [ht.ne', hd.ne', hl.ne']
  <;> ring

theorem integrable_shifted_resolventCoordinate {a : ℝ} (ha : 0 < a) (f : H) :
    Integrable (fun lambda : ℝ => (a + lambda)⁻¹) (unboundedScalarMeasure R hSA f) := by
  have hm : Measurable (fun lambda : ℝ => (a + lambda)⁻¹) := by fun_prop
  change Integrable _ ((scalarMeasure R hSA f).map (spectralLambda R))
  apply (integrable_map_measure hm.aestronglyMeasurable
    (measurable_spectralLambda R).aemeasurable).2
  have hc : Integrable (fun t => scalarShiftedResolvent R hpos hnorm ha t)
      (scalarMeasure R hSA f) :=
    (scalarShiftedResolvent R hpos hnorm ha).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  apply hc.congr
  filter_upwards [scalarMeasure_coordinate_pos_ae R hSA hpos hnorm hinj f] with t ht
  exact (shifted_scalar_identity R hpos hnorm ha ht).symm

theorem scalar_shifted_resolvent_integral {a : ℝ} (ha : 0 < a) (f : H) :
    (∫ lambda : ℝ, (a + lambda)⁻¹ ∂unboundedScalarMeasure R hSA f) =
      (inner ℂ f ((shiftedResolvent R a) f)).re := by
  have hm : Measurable (fun lambda : ℝ => (a + lambda)⁻¹) := by fun_prop
  rw [unboundedScalarMeasure,
    integral_map_of_stronglyMeasurable (measurable_spectralLambda R) hm.stronglyMeasurable]
  have heq : (fun t : ResolventSpectrum R => (a + spectralLambda R t)⁻¹) =ᵐ[scalarMeasure R hSA f]
      (fun t => scalarShiftedResolvent R hpos hnorm ha t) := by
    filter_upwards [scalarMeasure_coordinate_pos_ae R hSA hpos hnorm hinj f] with t ht
    exact shifted_scalar_identity R hpos hnorm ha ht
  rw [integral_congr_ae heq]
  rw [← resolventCFC_scalarShiftedResolvent R hSA hpos hnorm ha]
  exact scalarMeasure_integral R hSA f (scalarShiftedResolvent R hpos hnorm ha)

end

end ImbalancedChen.Part3.GenericResolventUnboundedScalarMeasure20261025a
