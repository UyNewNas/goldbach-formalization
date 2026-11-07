import ImbalancedChen.Part3ActualCommonHeightKFactorizationFullGram
import ImbalancedChen.Part3ImaginaryOrderKExplicitMajorant
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCEONLY / UNCOMPILED / no acceptance credit, 2026-10-24.
The actual spectral test has fixed compact physical support.  The already
proved imaginary-order K bound is uniform in t, so it gives one integrable
majorant for the actual dq/q transform.  This proves continuity in t by
dominated convergence, including t = 0.  The common-height integral follows
from its exact, previously proved coefficient factorization.
-/

namespace ImbalancedChen.Part3.ActualKTransformContinuity20261024z

noncomputable section

open Set MeasureTheory Filter
open scoped Topology
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralMode)
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKExplicitMajorantSourceOnly
open ActualCommonHeightKGramSourceOnly
open ActualKPacketAdapterSourceOnly (kModeFunction)

variable {ι : Type*}

private def transformIntegrand (P : PacketData ι) (k : D4 → ℤ)
    (t q : ℝ) : ℂ :=
  spectralTest k P.Y0 q * ((imaginaryOrderK t q : ℂ) / (q : ℂ))

private def transformMajorant (P : PacketData ι) (k : D4 → ℤ)
    (q : ℝ) : ℝ :=
  P.region.indicator (fun x => ‖spectralTest k P.Y0 x‖ * (512 / P.Y0^2)) q

/-- The fixed physical interval makes the uniform K bound integrable on ℝ. -/
private theorem transformMajorant_integrable (P : PacketData ι)
    (k : D4 → ℤ) : Integrable (transformMajorant P k) := by
  have hc : Continuous (fun q : ℝ =>
      ‖spectralTest k P.Y0 q‖ * (512 / P.Y0^2)) :=
    (P3Period64NativeReconstructionSourceOnly.spectralTest_contDiff k P.Y0).continuous.norm.mul
      continuous_const
  have hi : IntegrableOn (fun q : ℝ =>
      ‖spectralTest k P.Y0 q‖ * (512 / P.Y0^2)) P.region := by
    exact hc.continuousOn.integrableOn_compact (isCompact_Icc : IsCompact P.region)
  exact hi.integrable_indicator (isClosed_Icc : IsClosed P.region).measurableSet

/-- Pointwise t continuity uses the actual jointly continuous K integral.
The zero-support case also handles q = 0 without ever dividing by it. -/
private theorem transformIntegrand_continuous_height (P : PacketData ι)
    (k : D4 → ℤ) (q : ℝ) :
    Continuous (fun t : ℝ => transformIntegrand P k t q) := by
  by_cases hq : q ∈ P.region
  · have hqpos : 0 < q := by
      have hl : P.Y0/16 ≤ q := hq.1
      linarith [P.Y0_pos]
    have hp : Continuous (fun t : ℝ =>
        (t, (⟨q, by change q ≤ q; rfl⟩ : Ici q))) := by
      fun_prop
    have hK : Continuous (fun t : ℝ => (imaginaryOrderK t q : ℂ)) :=
      Complex.continuous_ofReal.comp
        ((imaginaryOrderK_joint_continuous q hqpos).comp hp)
    change Continuous (fun t : ℝ =>
      spectralTest k P.Y0 q * ((imaginaryOrderK t q : ℂ) / (q : ℂ)))
    exact continuous_const.mul (hK.div_const (q : ℂ))
  · have hz : ∀ t : ℝ, transformIntegrand P k t q = 0 := by
      intro t
      simp only [transformIntegrand, spectralTest, spectralMode,
        P.chi_scaled_zero_off q hq, Complex.ofReal_zero, zero_mul]
    simpa only [hz] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))

/-- One bound works for every height, with the precise physical support. -/
private theorem transformIntegrand_norm_le (P : PacketData ι)
    (k : D4 → ℤ) (t q : ℝ) :
    ‖transformIntegrand P k t q‖ ≤ transformMajorant P k q := by
  by_cases hq : q ∈ P.region
  · have hqpos : 0 < q := by
      have hl : P.Y0/16 ≤ q := hq.1
      linarith [P.Y0_pos]
    have hK : ‖(imaginaryOrderK t q : ℂ) / (q : ℂ)‖ ≤
        512 / P.Y0^2 := by
      simpa only [extendedKKernel_eq_on_physical_region P t q hq] using
        (extendedKKernel_norm_le_on_region P t q hq)
    change ‖spectralTest k P.Y0 q *
      ((imaginaryOrderK t q : ℂ) / (q : ℂ))‖ ≤
      P.region.indicator
        (fun x => ‖spectralTest k P.Y0 x‖ * (512 / P.Y0^2)) q
    rw [norm_mul, Set.indicator_of_mem hq]
    exact mul_le_mul_of_nonneg_left hK (norm_nonneg _)
  · have hz : transformIntegrand P k t q = 0 := by
      simp only [transformIntegrand, spectralTest, spectralMode,
        P.chi_scaled_zero_off q hq, Complex.ofReal_zero, zero_mul]
    rw [hz, norm_zero]
    change 0 ≤ P.region.indicator
      (fun x => ‖spectralTest k P.Y0 x‖ * (512 / P.Y0^2)) q
    rw [Set.indicator_of_notMem hq]
    exact le_rfl

/-- Continuity of the ACTUAL `kTestTransform`; no height-continuity
hypothesis is supplied by the caller. -/
theorem kTestTransform_continuous (P : PacketData ι) (k : D4 → ℤ) :
    Continuous (kTestTransform P k) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hdct : Tendsto
      (fun r : ℝ => ∫ q : ℝ, transformIntegrand P k r q)
      (𝓝 t) (𝓝 (∫ q : ℝ, transformIntegrand P k t q)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (transformMajorant P k)
    · exact Filter.Eventually.of_forall (fun r =>
        (kTestTransform_integrable P k r).aestronglyMeasurable)
    · exact Filter.Eventually.of_forall (fun r =>
        Filter.Eventually.of_forall (fun q =>
          transformIntegrand_norm_le P k r q))
    · exact transformMajorant_integrable P k
    · exact Filter.Eventually.of_forall (fun q =>
        (transformIntegrand_continuous_height P k q).continuousAt)
  exact hdct

/-- The genuine common-height mode integral inherits continuity from the
transform and the height-independent completed packet sum. -/
theorem common_height_modeIntegral_continuous (P : PacketData ι)
    (k : D4 → ℤ) :
    Continuous (fun t : ℝ =>
      ∫ q : ℝ, kModeFunction P (commonHeight t) k q) := by
  have hc : Continuous (fun t : ℝ =>
      kTestTransform P k t * completedPacketSum P k) :=
    (kTestTransform_continuous P k).mul continuous_const
  have he : (fun t : ℝ =>
      ∫ q : ℝ, kModeFunction P (commonHeight t) k q) =
      (fun t : ℝ => kTestTransform P k t * completedPacketSum P k) := by
    funext t
    exact actual_common_height_modeIntegral P k t
  rw [he]
  exact hc

end
end ImbalancedChen.Part3.ActualKTransformContinuity20261024z
