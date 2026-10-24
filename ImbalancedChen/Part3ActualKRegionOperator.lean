import ImbalancedChen.Part3ImaginaryOrderKExplicitMajorant
import ImbalancedChen.Part3ActualCommonHeightKFactorizationFullGram
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
SOURCEONLY 20261024z. UNCOMPILED; no acceptance credit.

This file constructs the K/q integral as a complex continuous linear
functional on the *actual* compact physical region. The measure on the
subtype is the pullback of Lebesgue volume; its pushforward is precisely
volume.restrict P.region. The operator bound uses the proved uniform
majorant of the actual imaginary-order K kernel and the real measure of
that same region. Its value on the actual restricted spectral test is
exactly the pre-existing kTestTransform, including dq/q and Y0.
No Kuznetsov identity, Gram/Parseval assertion or height decay is used.
-/

namespace ImbalancedChen.Part3.ActualKRegionOperatorSourceOnly

noncomputable section

open Set MeasureTheory
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralTest_contDiff spectralMode)
open ImbalancedChen.Part3.ImaginaryOrderKExplicitMajorantSourceOnly
  (restrictedKKernel restrictedKKernel_eq restrictedKKernel_norm_le)
open ImbalancedChen.Part3.ImaginaryOrderKBesselSourceOnly (imaginaryOrderK)
open ImbalancedChen.Part3.ActualCommonHeightKGramSourceOnly (kTestTransform)

variable {ι : Type*}

/-- Lebesgue measure transported onto the physical compact subtype. -/
def regionVolume (P : PacketData ι) : Measure P.region :=
  Measure.comap Subtype.val (volume : Measure ℝ)

/-- The transported measure is exactly the restricted real measure when
viewed in the ambient q variable. -/
theorem regionVolume_pushforward (P : PacketData ι) :
    (regionVolume P).map ((↑) : P.region → ℝ) =
      (volume : Measure ℝ).restrict P.region := by
  exact Measure.map_comap_subtype_coe
    (show MeasurableSet P.region from measurableSet_Icc) (volume : Measure ℝ)

theorem regionVolume_univ (P : PacketData ι) :
    regionVolume P Set.univ = (volume : Measure ℝ) P.region := by
  calc
    regionVolume P Set.univ =
        (volume : Measure ℝ) (((↑) : P.region → ℝ) '' Set.univ) :=
      Measure.comap_subtype_coe_apply
        (show MeasurableSet P.region from measurableSet_Icc) (volume : Measure ℝ) _
    _ = (volume : Measure ℝ) P.region := by
      simp only [Set.image_univ, Subtype.range_coe]

theorem regionVolume_real_univ (P : PacketData ι) :
    (regionVolume P).real Set.univ = (volume : Measure ℝ).real P.region := by
  simpa only [measureReal_def] using congrArg ENNReal.toReal (regionVolume_univ P)

private instance regionVolume_finite (P : PacketData ι) :
    IsFiniteMeasure (regionVolume P) :=
  ⟨by rw [regionVolume_univ]; exact isCompact_Icc.measure_lt_top⟩

/-- Genuine pointwise estimate for the particular K/q kernel. -/
theorem kWeight_norm_le (P : PacketData ι) (t : ℝ)
    (f : C(P.region, ℂ)) (q : P.region) :
    ‖f q * restrictedKKernel P t q‖ ≤ (512 / P.Y0^2) * ‖f‖ := by
  calc
    ‖f q * restrictedKKernel P t q‖ =
        ‖f q‖ * ‖restrictedKKernel P t q‖ := norm_mul _ _
    _ ≤ ‖f‖ * ‖restrictedKKernel P t q‖ :=
      mul_le_mul_of_nonneg_right (f.norm_coe_le_norm q) (norm_nonneg _)
    _ ≤ ‖f‖ * (512 / P.Y0^2) :=
      mul_le_mul_of_nonneg_left
        ((restrictedKKernel P t).norm_coe_le_norm q |>.trans
          (restrictedKKernel_norm_le P t)) (norm_nonneg _)
    _ = (512 / P.Y0^2) * ‖f‖ := mul_comm _ _

private theorem kWeight_integrable (P : PacketData ι) (t : ℝ)
    (f : C(P.region, ℂ)) :
    Integrable (fun q : P.region => f q * restrictedKKernel P t q)
      (regionVolume P) := by
  have hc : Continuous (fun q : P.region => f q * restrictedKKernel P t q) :=
    f.continuous.mul (restrictedKKernel P t).continuous
  exact Integrable.of_bound hc.aestronglyMeasurable
    ((512 / P.Y0^2) * ‖f‖)
    (Filter.Eventually.of_forall (kWeight_norm_le P t f))

/-- The underlying complex-linear integral, before adding its norm bound. -/
def kRegionLinearMap (P : PacketData ι) (t : ℝ) :
    C(P.region, ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫ q : P.region, f q * restrictedKKernel P t q ∂regionVolume P
  map_add' f g := by
    simpa only [ContinuousMap.add_apply, add_mul] using
      (integral_add (kWeight_integrable P t f) (kWeight_integrable P t g))
  map_smul' c f := by
    simpa only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc] using
      (integral_smul (μ := regionVolume P) c
        (fun q : P.region => f q * restrictedKKernel P t q))

/-- The actual kernel sup and actual interval volume control the integral. -/
theorem kRegionLinearMap_bound (P : PacketData ι) (t : ℝ)
    (f : C(P.region, ℂ)) :
    ‖kRegionLinearMap P t f‖ ≤
      ((512 / P.Y0^2) * (volume : Measure ℝ).real P.region) * ‖f‖ := by
  change ‖∫ q : P.region, f q * restrictedKKernel P t q ∂regionVolume P‖ ≤ _
  calc
    ‖∫ q : P.region, f q * restrictedKKernel P t q ∂regionVolume P‖ ≤
        ((512 / P.Y0^2) * ‖f‖) * (regionVolume P).real Set.univ :=
      norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall (kWeight_norm_le P t f))
    _ = ((512 / P.Y0^2) * (volume : Measure ℝ).real P.region) * ‖f‖ := by
      rw [regionVolume_real_univ]
      ring

/-- Continuous K/q integral functional on the actual physical region. -/
def kRegionFunctional (P : PacketData ι) (t : ℝ) :
    C(P.region, ℂ) →L[ℂ] ℂ :=
  (kRegionLinearMap P t).mkContinuous
    ((512 / P.Y0^2) * (volume : Measure ℝ).real P.region)
    (kRegionLinearMap_bound P t)

theorem kRegionFunctional_norm_le (P : PacketData ι) (t : ℝ) :
    ‖kRegionFunctional P t‖ ≤
      (512 / P.Y0^2) * (volume : Measure ℝ).real P.region := by
  exact LinearMap.mkContinuous_norm_le (kRegionLinearMap P t)
    (by positivity) (kRegionLinearMap_bound P t)

/-- Restriction of the *actual* spectralTest, with its original Y0. -/
def restrictedSpectralTest (P : PacketData ι) (k : D4 → ℤ) : C(P.region, ℂ) :=
  ⟨fun q => spectralTest k P.Y0 (q : ℝ),
    (spectralTest_contDiff k P.Y0).continuous.comp continuous_subtype_val⟩

/-- Exact normalization bridge to the previously defined full-axis
K transform. The off-region equality uses the actual chi support. -/
theorem kRegionFunctional_restrictedSpectralTest_eq_kTestTransform
    (P : PacketData ι) (k : D4 → ℤ) (t : ℝ) :
    kRegionFunctional P t (restrictedSpectralTest P k) = kTestTransform P k t := by
  change (∫ q : P.region,
      restrictedSpectralTest P k q * restrictedKKernel P t q ∂regionVolume P) = _
  calc
    (∫ q : P.region,
        restrictedSpectralTest P k q * restrictedKKernel P t q ∂regionVolume P) =
      ∫ q : P.region, spectralTest k P.Y0 (q : ℝ) *
        ((imaginaryOrderK t (q : ℝ) : ℂ) / ((q : ℝ) : ℂ)) ∂regionVolume P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun q => by
        rw [restrictedKKernel_eq]
        rfl)
    _ = ∫ q in P.region, spectralTest k P.Y0 q *
        ((imaginaryOrderK t q : ℂ) / (q : ℂ)) :=
      integral_subtype_comap (show MeasurableSet P.region from measurableSet_Icc)
        (fun q : ℝ => spectralTest k P.Y0 q *
          ((imaginaryOrderK t q : ℂ) / (q : ℂ)))
    _ = kTestTransform P k t := by
      unfold kTestTransform
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro q hq
      simp only [spectralTest, spectralMode, P.chi_scaled_zero_off q hq,
        Complex.ofReal_zero, zero_mul]

end
end ImbalancedChen.Part3.ActualKRegionOperatorSourceOnly
