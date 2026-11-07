import ImbalancedChen.Part3ActualResolventSurvivalStrongLimit
import ImbalancedChen.Part3ActualResolventScalarMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
No zero atom for the genuine actual resolvent scalar measure, derived from
the proved strong survival limit and the actual RMK survival moments.
The inverse-resolvent map lambda=1/t-1 then produces a genuine finite
scalar measure supported on [0,infinity), with exact resolvent moments.
No no-atom, scalar-measure or spectral-pushforward supplier is assumed.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualResolventZeroAtomPushforward20261025a

noncomputable section

open MeasureTheory Set Filter Topology
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualCompletedEnergyResolvent20261025a
open ImbalancedChen.Part3.ActualResolventSurvivalStrongLimit20261025a
open ImbalancedChen.Part3.ActualResolventScalarMeasure20261025a

def zeroFiber : Set ResolventSpectrum := {t | (t : ℝ) = 0}

theorem measurableSet_zeroFiber : MeasurableSet zeroFiber :=
  (isClosed_eq continuous_subtype_val continuous_const).measurableSet

/-- Genuine survival moments tend to zero by the already proved actual
strong operator limit, before making any conclusion about atoms. -/
theorem tendsto_scalarMeasure_survival_integral (f : HyperbolicL2) :
    Tendsto (fun n : ℕ => ∫ t : ResolventSpectrum, (1 - (t : ℝ)) ^ n ∂scalarMeasure f)
      atTop (𝓝 0) := by
  have hinner : Tendsto (fun n : ℕ => inner ℂ f ((actualSurvival ^ n) f))
      atTop (𝓝 (0 : ℂ)) := by
    simpa only [inner_zero_right] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => f) atTop (𝓝 f)).inner
        (tendsto_actualSurvival_pow f)
  have hre : Tendsto (fun n : ℕ => (inner ℂ f ((actualSurvival ^ n) f)).re)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Complex.zero_re] using (Complex.continuous_re.tendsto (0 : ℂ)).comp hinner
  apply hre.congr'
  exact Eventually.of_forall fun n => (scalarMeasure_survival_moment f n).symm

/-- The atom at the possibly spectral endpoint zero is bounded by every
survival moment. Strong decay therefore forces its actual measure to zero. -/
theorem scalarMeasure_zeroFiber (f : HyperbolicL2) : scalarMeasure f zeroFiber = 0 := by
  have hbound (n : ℕ) : (scalarMeasure f).real zeroFiber ≤
      ∫ t : ResolventSpectrum, (1 - (t : ℝ)) ^ n ∂scalarMeasure f := by
    have hi : Integrable (zeroFiber.indicator (1 : ResolventSpectrum → ℝ)) (scalarMeasure f) :=
      (integrable_const (1 : ℝ)).indicator measurableSet_zeroFiber
    have hp : Integrable (fun t : ResolventSpectrum => (1 - (t : ℝ)) ^ n) (scalarMeasure f) :=
      (show Continuous (fun t : ResolventSpectrum => (1 - (t : ℝ)) ^ n) by fun_prop)
        .integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hle : ∀ t : ResolventSpectrum,
        zeroFiber.indicator (1 : ResolventSpectrum → ℝ) t ≤ (1 - (t : ℝ)) ^ n := by
      intro t
      by_cases ht : t ∈ zeroFiber
      · rw [indicator_of_mem ht]
        change (t : ℝ) = 0 at ht
        simp only [Pi.one_apply, ht, sub_zero, one_pow, le_refl]
      · rw [indicator_of_notMem ht]
        exact pow_nonneg (sub_nonneg.mpr (spectrum_coordinate_mem_unitInterval t).2) n
    have h := integral_mono_ae hi hp (Eventually.of_forall hle)
    simpa only [integral_indicator_one measurableSet_zeroFiber] using h
  have hzero : (scalarMeasure f).real zeroFiber = 0 := by
    apply le_antisymm
    · exact le_of_tendsto_of_tendsto
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (scalarMeasure f).real zeroFiber)
          atTop (𝓝 ((scalarMeasure f).real zeroFiber)))
        (tendsto_scalarMeasure_survival_integral f) (Eventually.of_forall hbound)
    · exact measureReal_nonneg
  exact (measureReal_eq_zero_iff (measure_ne_top (scalarMeasure f) zeroFiber)).mp hzero

theorem scalarMeasure_coordinate_pos_ae (f : HyperbolicL2) :
    ∀ᵐ t : ResolventSpectrum ∂scalarMeasure f, 0 < (t : ℝ) := by
  have hnot : ∀ᵐ t : ResolventSpectrum ∂scalarMeasure f, t ∉ zeroFiber := by
    rw [ae_iff]
    simpa only [not_not] using scalarMeasure_zeroFiber f
  filter_upwards [hnot] with t ht
  change (t : ℝ) ≠ 0 at ht
  exact lt_of_le_of_ne (spectrum_coordinate_mem_unitInterval t).1 (Ne.symm ht)

/-- The inverse-resolvent spectral coordinate is defined everywhere;
its exceptional negative value at t=0 has actual scalar measure zero. -/
def spectralLambda (t : ResolventSpectrum) : ℝ := (t : ℝ)⁻¹ - 1

theorem measurable_spectralLambda : Measurable spectralLambda := by
  unfold spectralLambda
  fun_prop

theorem spectralLambda_nonneg {t : ResolventSpectrum} (ht : 0 < (t : ℝ)) :
    0 ≤ spectralLambda t := by
  have h : (1 : ℝ) ≤ 1 / (t : ℝ) :=
    (le_div_iff₀ ht).2 (by simpa using (spectrum_coordinate_mem_unitInterval t).2)
  simpa only [spectralLambda, one_div, sub_nonneg] using h

def unboundedScalarMeasure (f : HyperbolicL2) : Measure ℝ :=
  (scalarMeasure f).map spectralLambda

instance unboundedScalarMeasure_finite (f : HyperbolicL2) :
    IsFiniteMeasure (unboundedScalarMeasure f) := by
  unfold unboundedScalarMeasure
  infer_instance

/-- The pushforward is actually supported in the nonnegative unbounded
coordinate; the removed t=0 atom is the only possible obstruction. -/
theorem unboundedScalarMeasure_Iio_zero (f : HyperbolicL2) :
    unboundedScalarMeasure f (Iio 0) = 0 := by
  rw [unboundedScalarMeasure, Measure.map_apply measurable_spectralLambda measurableSet_Iio]
  apply measure_mono_null (t := zeroFiber) ?_ (scalarMeasure_zeroFiber f)
  intro t ht
  change spectralLambda t < 0 at ht
  by_contra hnot
  change (t : ℝ) ≠ 0 at hnot
  have hpos : 0 < (t : ℝ) :=
    lt_of_le_of_ne (spectrum_coordinate_mem_unitInterval t).1 (Ne.symm hnot)
  exact not_lt_of_ge (spectralLambda_nonneg hpos) ht

theorem unboundedScalarMeasure_nonnegative_ae (f : HyperbolicL2) :
    ∀ᵐ lambda : ℝ ∂unboundedScalarMeasure f, 0 ≤ lambda := by
  rw [ae_iff]
  simpa only [not_le] using unboundedScalarMeasure_Iio_zero f

theorem unboundedScalarMeasure_univ (f : HyperbolicL2) :
    unboundedScalarMeasure f univ = ENNReal.ofReal (‖f‖ ^ 2) := by
  rw [unboundedScalarMeasure, Measure.map_apply measurable_spectralLambda MeasurableSet.univ,
    preimage_univ]
  exact scalarMeasure_univ f

theorem unboundedScalarMeasure_mass (f : HyperbolicL2) :
    (unboundedScalarMeasure f).real univ = ‖f‖ ^ 2 := by
  change (unboundedScalarMeasure f univ).toReal = _
  rw [unboundedScalarMeasure_univ, ENNReal.toReal_ofReal (sq_nonneg _)]

def resolventCoordinate (lambda : ℝ) : ℝ := 1 / (1 + lambda)

theorem measurable_resolventCoordinate : Measurable resolventCoordinate := by
  unfold resolventCoordinate
  fun_prop

theorem resolventCoordinate_spectralLambda (t : ResolventSpectrum) :
    resolventCoordinate (spectralLambda t) = (t : ℝ) := by
  unfold resolventCoordinate spectralLambda
  rw [show 1 + ((t : ℝ)⁻¹ - 1) = (t : ℝ)⁻¹ by ring, one_div, inv_inv]

/-- Inverse-resolvent transport recovers exactly the actual scalar
measure in its original real coordinate, not a surrogate distribution. -/
theorem unboundedScalarMeasure_map_resolventCoordinate (f : HyperbolicL2) :
    (unboundedScalarMeasure f).map resolventCoordinate =
      (scalarMeasure f).map (fun t : ResolventSpectrum => (t : ℝ)) := by
  rw [unboundedScalarMeasure, Measure.map_map measurable_resolventCoordinate measurable_spectralLambda]
  congr 1
  funext t
  exact resolventCoordinate_spectralLambda t

/-- Every bounded inverse-resolvent moment is the actual operator-power
matrix coefficient of R, for the genuine unbounded-coordinate measure. -/
theorem unboundedScalarMeasure_resolvent_moment (f : HyperbolicL2) (n : ℕ) :
    (∫ lambda : ℝ, (resolventCoordinate lambda) ^ n ∂unboundedScalarMeasure f) =
      (inner ℂ f ((actualWeakResolvent ^ n) f)).re := by
  have hm : Measurable (fun lambda : ℝ => (resolventCoordinate lambda) ^ n) := by fun_prop
  rw [unboundedScalarMeasure,
    integral_map_of_stronglyMeasurable measurable_spectralLambda hm.stronglyMeasurable]
  simp_rw [resolventCoordinate_spectralLambda]
  exact scalarMeasure_moment f n

end

end ImbalancedChen.Part3.ActualResolventZeroAtomPushforward20261025a
