import ImbalancedChen.Part3ActualKLIntegrableSpectralInverse
import ImbalancedChen.Part3IndicatorInvariantCyclicDensity
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Actual KL inversion of arbitrary raw spectral L2 data by truncation

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

For each finite R the ACTUAL scalar K integral of g*1_[0,R] is continuous
in the radial variable and represents the inverse unitary applied to the
actual spectral truncation.  Its physical L2 membership is established by
compact-test weak pairing, not by an invalid L2-valued kernel integral.
The resulting literal-integral L2 vectors converge to the inverse of g.
No pointwise full inverse integral is asserted for arbitrary L2 data.
The measure factor is (2/pi^2)*tau*sinh(pi*tau), not a Gamma quotient factor.
-/

namespace ImbalancedChen.Part3.ActualKLAllL2Inversion20261026a

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open RadialSchrodingerL2Form20261025a ActualKLCoreTransform20261025a
open ActualKLCoordinateMeasures20261025a ActualKLOntoUnitary20261025a
open ActualKLResolventCoordinate20261025a ActualKLCompactTestWeightedL220261025a
open ActualKLIntegrableSpectralInverse20261026a IndicatorInvariantCyclicDensity20261025a

local instance : SigmaFinite tauMeasure := by
  unfold tauMeasure positiveDensityMeasure
  infer_instance

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The actual raw measure has finite mass on every bounded positive
spectral interval, proved directly from its continuous literal density. -/
theorem tauMeasure_Icc_zero_lt_top (R : ℝ) : tauMeasure (Icc 0 R) < ⊤ := by
  have hc : Continuous tauDensity := by unfold tauDensity; fun_prop
  have hi : IntegrableOn tauDensity (Icc (0 : ℝ) R) := hc.continuousOn.integrableOn_Icc
  have hn : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Icc 0 R)] tauDensity := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with tau htau
    exact actualKLWeight_nonneg htau.1
  have hfin : (∫⁻ tau in Icc (0 : ℝ) R, ENNReal.ofReal (tauDensity tau)) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal hn).mp hi.hasFiniteIntegral
  unfold tauMeasure positiveDensityMeasure
  rw [withDensity_apply _ measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
  exact (lintegral_mono_measure (Measure.restrict_mono inter_subset_left le_rfl)).trans_lt hfin

def spectralCutoffFunction (g : RawTauL2) (R : ℝ) : ℝ → ℂ := (Icc 0 R).indicator g

def actualKLSpectralTruncation (g : RawTauL2) (R : ℝ) : RawTauL2 :=
  indicatorL2 tauMeasure (Icc 0 R) measurableSet_Icc g

theorem actualKLSpectralTruncation_ae (g : RawTauL2) (R : ℝ) :
    actualKLSpectralTruncation g R =ᵐ[tauMeasure] spectralCutoffFunction g R :=
  indicatorL2_coe_ae tauMeasure (Icc 0 R) measurableSet_Icc g

theorem spectralCutoffFunction_memLp (g : RawTauL2) (R : ℝ) :
    MemLp (spectralCutoffFunction g R) 2 tauMeasure :=
  (Lp.memLp g).indicator measurableSet_Icc

/-- Genuine scalar L1 integrability follows by finite-measure Holder on
the bounded spectral interval. It is not imposed on the original g. -/
theorem spectralCutoffFunction_integrable (g : RawTauL2) (R : ℝ) :
    Integrable (spectralCutoffFunction g R) tauMeasure := by
  letI : IsFiniteMeasure (tauMeasure.restrict (Icc 0 R)) :=
    isFiniteMeasure_restrict.mpr (tauMeasure_Icc_zero_lt_top R).ne
  have hi : IntegrableOn (g : ℝ → ℂ) (Icc 0 R) tauMeasure :=
    MemLp.integrable (by norm_num) ((Lp.memLp g).restrict (Icc 0 R))
  exact (integrable_indicator_iff measurableSet_Icc).mpr hi

def actualKLTruncatedIntegral (g : RawTauL2) (R r : ℝ) : ℂ :=
  ∫ tau in Icc (0 : ℝ) R, g tau * inverseKKernel tau r ∂tauMeasure

theorem actualKLTruncatedIntegral_eq_spectralL1Inverse (g : RawTauL2) (R r : ℝ) :
    actualKLTruncatedIntegral g R r = spectralL1Inverse (spectralCutoffFunction g R) r := by
  unfold actualKLTruncatedIntegral spectralL1Inverse
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  exact Eventually.of_forall (fun tau => by
    by_cases htau : tau ∈ Icc (0 : ℝ) R
    · simp only [spectralCutoffFunction, indicator_of_mem htau]
    · simp only [spectralCutoffFunction, indicator_of_notMem htau, zero_mul])

theorem actualKLTruncatedIntegral_integrable (g : RawTauL2) (R r : ℝ) :
    IntegrableOn (fun tau => g tau * inverseKKernel tau r) (Icc 0 R) tauMeasure := by
  have hi := spectralL1Inverse_integrable (spectralCutoffFunction_integrable g R) r
  apply (integrable_indicator_iff measurableSet_Icc).mp
  apply hi.congr
  exact Eventually.of_forall (fun tau => by
    by_cases htau : tau ∈ Icc (0 : ℝ) R
    · simp only [spectralCutoffFunction, indicator_of_mem htau]
    · simp only [spectralCutoffFunction, indicator_of_notMem htau, zero_mul])

theorem actualKLTruncatedIntegral_continuous (g : RawTauL2) (R : ℝ) :
    Continuous (actualKLTruncatedIntegral g R) := by
  have he : actualKLTruncatedIntegral g R = spectralL1Inverse (spectralCutoffFunction g R) :=
    funext (actualKLTruncatedIntegral_eq_spectralL1Inverse g R)
  rw [he]
  exact spectralL1Inverse_continuous (spectralCutoffFunction_integrable g R)

/-- A locally uniform scalar majorant in r, including arbitrary L2
spectral representatives rather than just continuous compact amplitudes. -/
theorem actualKLTruncatedIntegral_local_majorant (g : RawTauL2) (R a b : ℝ) :
    ∃ M : ℝ → ℝ, Integrable M tauMeasure ∧
      ∀ r ∈ Icc a b, ∀ tau : ℝ,
        ‖spectralCutoffFunction g R tau * inverseKKernel tau r‖ ≤ M tau := by
  refine ⟨fun tau => ComplexOrderKUniformStripDecay20261025a.stripDecayConstant
    0 (Real.exp a) 1 * ‖spectralCutoffFunction g R tau‖, ?_⟩
  exact spectralL1Inverse_local_majorant (spectralCutoffFunction_integrable g R) a b

/-- The actual scalar integral, identified against the actual raw density.
At tau=0 the density vanishes; the resulting positive interval is (0,R]. -/
theorem actualKLTruncatedIntegral_literal_weight (g : RawTauL2) (R r : ℝ) :
    actualKLTruncatedIntegral g R r = ∫ tau in Ioc (0 : ℝ) R,
      (((2 / Real.pi ^ 2) * tau * Real.sinh (Real.pi * tau) : ℝ) : ℂ) *
        g tau * complexOrderK ((tau : ℂ) * Complex.I) (Real.exp r) := by
  unfold actualKLTruncatedIntegral tauMeasure positiveDensityMeasure
  rw [restrict_withDensity measurableSet_Icc,
    integral_withDensity_eq_integral_toReal_smul
      (show Measurable (fun tau : ℝ => ENNReal.ofReal (tauDensity tau)) by
        unfold tauDensity
        fun_prop)
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    Measure.restrict_restrict measurableSet_Icc]
  have hset : Icc (0 : ℝ) R ∩ Ioi 0 = Ioc 0 R := by
    ext tau
    simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
    constructor
    · intro h
      exact ⟨h.2, h.1.2⟩
    · intro h
      exact ⟨⟨h.1.le, h.2⟩, h.1⟩
  rw [hset]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with tau htau
  rw [ENNReal.toReal_ofReal (show 0 ≤ tauDensity tau from actualKLWeight_nonneg htau.1.le)]
  simp only [Complex.real_smul, inverseKKernel, ComplexOrderKRadialRegularitySourceOnly.radialK,
    tauDensity]
  ring

def actualKLTruncatedL2Inverse (g : RawTauL2) (R : ℝ) : RadialL2 :=
  actualKLUnitary.symm (actualKLSpectralTruncation g R)

/-- This supplies the physical L2 representative by weak compact-test
pairing and the genuine unitary inverse; it never integrates K as an
L2-valued kernel. -/
theorem actualKLTruncatedIntegral_eq_inverse_ae (g : RawTauL2) (R : ℝ) :
    actualKLTruncatedIntegral g R =ᵐ[(volume : Measure ℝ)]
      (actualKLTruncatedL2Inverse g R : ℝ → ℂ) := by
  have hae := spectralL1Inverse_eq_unitary_inverse_ae
    (spectralCutoffFunction_integrable g R) (spectralCutoffFunction_memLp g R)
  have he : actualKLTruncatedIntegral g R = spectralL1Inverse (spectralCutoffFunction g R) :=
    funext (actualKLTruncatedIntegral_eq_spectralL1Inverse g R)
  rw [he]
  simpa only [actualKLTruncatedL2Inverse, actualKLSpectralTruncation, indicatorL2] using hae

theorem actualKLTruncatedIntegral_memLp (g : RawTauL2) (R : ℝ) :
    MemLp (actualKLTruncatedIntegral g R) 2 volume :=
  (Lp.memLp (actualKLTruncatedL2Inverse g R)).congr
    (actualKLTruncatedIntegral_eq_inverse_ae g R).symm

theorem actualKLTruncatedIntegral_toLp (g : RawTauL2) (R : ℝ) :
    (actualKLTruncatedIntegral_memLp g R).toLp (actualKLTruncatedIntegral g R) =
      actualKLTruncatedL2Inverse g R := by
  apply Lp.ext
  exact (actualKLTruncatedIntegral_memLp g R).coeFn_toLp.trans
    (actualKLTruncatedIntegral_eq_inverse_ae g R)

private theorem raw_norm_sq_integral (u : RawTauL2) :
    ‖u‖ ^ 2 = ∫ tau, ‖u tau‖ ^ 2 ∂tauMeasure := by
  have hL2 : inner ℂ u u = ∫ tau, inner ℂ (u tau) (u tau) ∂tauMeasure := L2.inner_def _ _
  simp_rw [inner_self_eq_norm_sq_to_K] at hL2
  rw [integral_ofReal] at hL2
  exact Complex.ofReal_injective hL2

/-- Actual raw L2 convergence of increasing finite spectral cutoffs.
The majorant is |g|^2, and positivity of the support is proved for the
original tauMeasure. No pointwise inverse integral is involved. -/
theorem actualKLSpectralTruncation_tendsto (g : RawTauL2) :
    Tendsto (actualKLSpectralTruncation g) atTop (𝓝 g) := by
  have hDCT : Tendsto (fun R : ℝ => ∫ tau,
      ‖spectralCutoffFunction g R tau - g tau‖ ^ 2 ∂tauMeasure) atTop (𝓝 0) := by
    have hi : Integrable (fun tau => ‖g tau‖ ^ 2) tauMeasure := by
      exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
    have h := tendsto_integral_filter_of_dominated_convergence (μ := tauMeasure) (l := atTop)
      (bound := fun tau => ‖g tau‖ ^ 2)
      (F := fun R tau => ‖spectralCutoffFunction g R tau - g tau‖ ^ 2)
      (f := fun _ => (0 : ℝ))
    have hlim : Tendsto (fun R : ℝ => ∫ tau,
        ‖spectralCutoffFunction g R tau - g tau‖ ^ 2 ∂tauMeasure) atTop
        (𝓝 (∫ _ : ℝ, (0 : ℝ) ∂tauMeasure)) := by
      apply h
      · exact Eventually.of_forall (fun R =>
          ((((Lp.aestronglyMeasurable g).indicator measurableSet_Icc).sub
            (Lp.aestronglyMeasurable g)).norm.pow 2))
      · exact Eventually.of_forall (fun R => Eventually.of_forall (fun tau => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          by_cases htau : tau ∈ Icc (0 : ℝ) R
          · simp only [spectralCutoffFunction, indicator_of_mem htau, sub_self, norm_zero,
              zero_pow (by norm_num : 2 ≠ 0)]
            exact sq_nonneg _
          · simp only [spectralCutoffFunction, indicator_of_notMem htau, zero_sub, norm_neg,
              le_refl]))
      · exact hi
      · filter_upwards [tauMeasure_positive_ae] with tau htau
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop tau] with R hR
        simp only [spectralCutoffFunction, indicator_of_mem (show tau ∈ Icc (0 : ℝ) R from
          ⟨htau.le, hR⟩), sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    simpa only [integral_zero] using hlim
  have hsq : Tendsto (fun R : ℝ => ‖actualKLSpectralTruncation g R - g‖ ^ 2)
      atTop (𝓝 0) := by
    apply hDCT.congr'
    exact Eventually.of_forall (fun R => by
      rw [raw_norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (actualKLSpectralTruncation g R) g,
        actualKLSpectralTruncation_ae g R] with tau hsub hcut
      rw [hsub, hcut])
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hnorm : Tendsto (fun R : ℝ => ‖actualKLSpectralTruncation g R - g‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hn
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [dist_eq_norm] using hnorm

theorem actualKLTruncatedL2Inverse_tendsto (g : RawTauL2) :
    Tendsto (actualKLTruncatedL2Inverse g) atTop (𝓝 (actualKLUnitary.symm g)) :=
  actualKLUnitary.symm.continuous.continuousAt.tendsto.comp
    (actualKLSpectralTruncation_tendsto g)

/-- Full L2 inversion for every actual raw spectral vector: the scalar
truncated K integrals, taken as their proved physical L2 classes, converge
to the genuine inverse KL unitary. No all-g pointwise integral is claimed. -/
theorem actualKLAllL2_inverse_by_truncated_integrals (g : RawTauL2) :
    Tendsto (fun R : ℝ =>
      (actualKLTruncatedIntegral_memLp g R).toLp (actualKLTruncatedIntegral g R))
      atTop (𝓝 (actualKLUnitary.symm g)) := by
  simpa only [actualKLTruncatedIntegral_toLp] using actualKLTruncatedL2Inverse_tendsto g

theorem actualKLTruncatedL2Inverse_error_norm (g : RawTauL2) (R : ℝ) :
    ‖actualKLTruncatedL2Inverse g R - actualKLUnitary.symm g‖ =
      ‖actualKLSpectralTruncation g R - g‖ := by
  rw [actualKLTruncatedL2Inverse, ← map_sub]
  exact actualKLUnitary.symm.norm_map _

end
end ImbalancedChen.Part3.ActualKLAllL2Inversion20261026a
