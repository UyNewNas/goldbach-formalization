import ImbalancedChen.Part3ClosedIntervalSpectralRamps
import ImbalancedChen.Part3GenericResolventCyclicL2Representation

/-!
Actual strong limits of continuous spectral ramps for arbitrary bounded
self-adjoint operators on complete complex Hilbert spaces. RMK scalar
measures and the proved CFC norm-square identity imply vector Cauchy; no
limit vector or projection is a hypothesis. The resulting limit is a
constructed bounded complex-linear self-adjoint contraction.
SOURCE ONLY / UNCOMPILED / ZERO PROOF CREDIT.
-/

namespace ImbalancedChen.Part3.GenericIntervalProjectionLimit20261025a
noncomputable section
open MeasureTheory Filter
open scoped Topology
open GenericResolventScalarMeasure20261025a GenericResolventCyclicL2Representation20261025a
open ClosedIntervalSpectralRamps20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

def spectralRamp (a : ℝ) (n : ℕ) : C(ResolventSpectrum R, ℝ) :=
  rampMap (spectrumCoordinate R) a n

def rampOperator (a : ℝ) (n : ℕ) : H →L[ℂ] H :=
  resolventCFC R hSA (spectralRamp R a n)

theorem realCFC_norm_sq (f : H) (φ : C(ResolventSpectrum R, ℝ)) :
    ‖(resolventCFC R hSA φ) f‖ ^ 2 =
      ∫ t : ResolventSpectrum R, (φ t) ^ 2 ∂scalarMeasure R hSA f := by
  have he := continuousCyclicMap_norm_sq_integral R hSA f (complexOfReal R φ)
  simpa [continuousCyclicMap_apply, complexResolventCFC_ofReal,
    complexOfReal, Complex.norm_real, Real.norm_eq_abs, sq_abs] using he

theorem rampOperator_norm_le (a : ℝ) (n : ℕ) (f : H) :
    ‖rampOperator R hSA a n f‖ ≤ ‖f‖ := by
  have hI : Integrable (fun t : ResolventSpectrum R => (spectralRamp R a n t) ^ 2)
      (scalarMeasure R hSA f) :=
    ((spectralRamp R a n).continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs : ‖rampOperator R hSA a n f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [rampOperator, realCFC_norm_sq]
    calc
      _ ≤ ∫ _t : ResolventSpectrum R, (1 : ℝ) ∂scalarMeasure R hSA f := by
        apply integral_mono hI (integrable_const 1)
        intro t
        have hb := ramp_bounds a n (t : ℝ)
        have hm := mul_le_mul hb.2 hb.2 hb.1 zero_le_one
        nlinarith
      _ = ‖f‖ ^ 2 := by simpa [Measure.real] using scalarMeasure_mass R hSA f
  nlinarith [norm_nonneg (rampOperator R hSA a n f), norm_nonneg f]

def scalarError (a : ℝ) (n : ℕ) (f : H) : ℝ :=
  ∫ t : ResolventSpectrum R,
    (ramp a n (t : ℝ) - closedCut a (t : ℝ)) ^ 2 ∂scalarMeasure R hSA f

theorem scalarError_tendsto (a : ℝ) (f : H) :
    Tendsto (fun n => scalarError R hSA a n f) atTop (𝓝 0) :=
  ramp_error_sq_integral_tendsto_zero (spectrumCoordinate R) (scalarMeasure R hSA f) a

theorem scalarError_integrable (a : ℝ) (n : ℕ) (f : H) :
    Integrable (fun t : ResolventSpectrum R =>
      (ramp a n (t : ℝ) - closedCut a (t : ℝ)) ^ 2) (scalarMeasure R hSA f) := by
  have hm : Measurable (fun t : ResolventSpectrum R =>
      (ramp a n (t : ℝ) - closedCut a (t : ℝ)) ^ 2) :=
    (((spectralRamp R a n).continuous.measurable.sub
      (measurable_closedCut (spectrumCoordinate R) a)).pow_const 2)
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hr := ramp_bounds a n (t : ℝ)
  have hc := closedCut_bounds a (t : ℝ)
  have hb : |ramp a n (t : ℝ) - closedCut a (t : ℝ)| ≤ 1 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hp := mul_le_mul hb hb (abs_nonneg _) zero_le_one
  nlinarith [sq_abs (ramp a n (t : ℝ) - closedCut a (t : ℝ))]

theorem rampOperator_difference_sq_le (a : ℝ) (m n : ℕ) (f : H) :
    ‖rampOperator R hSA a m f - rampOperator R hSA a n f‖ ^ 2 ≤
      2 * (scalarError R hSA a m f + scalarError R hSA a n f) := by
  have hn := realCFC_norm_sq R hSA f (spectralRamp R a m - spectralRamp R a n)
  rw [map_sub, ContinuousLinearMap.sub_apply] at hn
  change ‖rampOperator R hSA a m f - rampOperator R hSA a n f‖ ^ 2 = _ at hn
  rw [hn]
  have hm := scalarError_integrable R hSA a m f
  have hn' := scalarError_integrable R hSA a n f
  calc
    _ ≤ ∫ t : ResolventSpectrum R,
        2 * ((ramp a m (t : ℝ) - closedCut a (t : ℝ)) ^ 2 +
          (ramp a n (t : ℝ) - closedCut a (t : ℝ)) ^ 2) ∂scalarMeasure R hSA f := by
      apply integral_mono
        (((spectralRamp R a m - spectralRamp R a n).continuous.pow 2)
          .integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        ((hm.add hn').const_mul 2)
      intro t
      change (ramp a m (t : ℝ) - ramp a n (t : ℝ)) ^ 2 ≤ _
      nlinarith [sq_nonneg (ramp a m (t : ℝ) + ramp a n (t : ℝ) -
        2 * closedCut a (t : ℝ))]
    _ = _ := by rw [integral_const_mul, integral_add hm hn']; rfl

/-- True vector Cauchy follows from actual scalar-measure DCT, with the
boundary atom included. No limiting-vector or spectral-projection input. -/
theorem rampOperator_cauchy (a : ℝ) (f : H) :
    CauchySeq (fun n => rampOperator R hSA a n f) := by
  apply Metric.cauchySeq_iff.mpr
  intro epsilon hepsilon
  have hsmall := (scalarError_tendsto R hSA a f).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < epsilon ^ 2 / 8))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hbound := rampOperator_difference_sq_le R hSA a m n f
  have hm' := hN m hm
  have hn' := hN n hn
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (rampOperator R hSA a m f - rampOperator R hSA a n f)]

theorem exists_ramp_limit (a : ℝ) (f : H) :
    ∃ u : H, Tendsto (fun n => rampOperator R hSA a n f) atTop (𝓝 u) :=
  cauchySeq_tendsto_of_complete (rampOperator_cauchy R hSA a f)

def intervalVector (a : ℝ) (f : H) : H := (exists_ramp_limit R hSA a f).choose

theorem tendsto_intervalVector (a : ℝ) (f : H) :
    Tendsto (fun n => rampOperator R hSA a n f) atTop (𝓝 (intervalVector R hSA a f)) :=
  (exists_ramp_limit R hSA a f).choose_spec

theorem intervalVector_add (a : ℝ) (f g : H) :
    intervalVector R hSA a (f + g) = intervalVector R hSA a f + intervalVector R hSA a g := by
  apply tendsto_nhds_unique (tendsto_intervalVector R hSA a (f + g))
  simpa only [map_add] using
    (tendsto_intervalVector R hSA a f).add (tendsto_intervalVector R hSA a g)

theorem intervalVector_smul (a : ℝ) (z : ℂ) (f : H) :
    intervalVector R hSA a (z • f) = z • intervalVector R hSA a f := by
  apply tendsto_nhds_unique (tendsto_intervalVector R hSA a (z • f))
  simpa only [map_smul] using (tendsto_intervalVector R hSA a f).const_smul z

theorem intervalVector_norm_le (a : ℝ) (f : H) : ‖intervalVector R hSA a f‖ ≤ ‖f‖ :=
  le_of_tendsto' (tendsto_intervalVector R hSA a f).norm
    (fun n => rampOperator_norm_le R hSA a n f)

def intervalLinearMap (a : ℝ) : H →ₗ[ℂ] H where
  toFun := intervalVector R hSA a
  map_add' := intervalVector_add R hSA a
  map_smul' := intervalVector_smul R hSA a

/-- The actual bounded complex-linear interval operator is built from the
proved strong limit; it is not supplied as a projection hypothesis. -/
def intervalProjection (a : ℝ) : H →L[ℂ] H :=
  (intervalLinearMap R hSA a).mkContinuous 1 (by
    intro f
    simpa only [one_mul] using intervalVector_norm_le R hSA a f)

theorem intervalProjection_apply (a : ℝ) (f : H) :
    intervalProjection R hSA a f = intervalVector R hSA a f := rfl

theorem tendsto_intervalProjection (a : ℝ) (f : H) :
    Tendsto (fun n => rampOperator R hSA a n f) atTop (𝓝 (intervalProjection R hSA a f)) :=
  tendsto_intervalVector R hSA a f

theorem intervalProjection_opNorm_le (a : ℝ) : ‖intervalProjection R hSA a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound (by norm_num : (0 : ℝ) ≤ 1)
  intro f
  simpa only [one_mul] using intervalVector_norm_le R hSA a f

theorem intervalProjection_selfAdjoint (a : ℝ) : IsSelfAdjoint (intervalProjection R hSA a) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro f g
  have hleft : Tendsto (fun n => inner ℂ (rampOperator R hSA a n f) g) atTop
      (𝓝 (inner ℂ (intervalProjection R hSA a f) g)) :=
    (tendsto_intervalProjection R hSA a f).inner tendsto_const_nhds
  have hright : Tendsto (fun n => inner ℂ f (rampOperator R hSA a n g)) atTop
      (𝓝 (inner ℂ f (intervalProjection R hSA a g))) :=
    tendsto_const_nhds.inner (tendsto_intervalProjection R hSA a g)
  have heq : (fun n => inner ℂ (rampOperator R hSA a n f) g) =
      (fun n => inner ℂ f (rampOperator R hSA a n g)) := by
    funext n
    exact (resolventCFC_selfAdjoint R hSA (spectralRamp R a n)).isSymmetric f g
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

end
end ImbalancedChen.Part3.GenericIntervalProjectionLimit20261025a
