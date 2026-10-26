import ImbalancedChen.Part3GammaZeroAtomConstantClosure
import ImbalancedChen.Part3GenericBorelProjectionScalarRestriction
import Mathlib.MeasureTheory.Measure.Dirac

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Physical mean subtraction for the original Gamma0 quotient L2. The actual
unbounded Laplace scalar measure of that vector is proved to be precisely
the original measure restricted away from zero. The removed measure is
the Dirac atom with the original quotient-volume coefficient. Mixed
complex spectral coefficients vanish for every real Borel set and two
independent vectors; the full complex linear-combination law follows.
No cusp/Eisenstein completeness, gap, or heat limit is used or asserted.
-/
namespace ImbalancedChen.Part3.GammaMeanCenteredScalarMeasure20261026b

noncomputable section
open Set MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0QuotientCellPushforward20261025a
open Gamma0ActualConstantMode20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualUnboundedScalarMeasure20261025a
open GammaZeroSpectralProjectionKernel20261026a
open GammaZeroAtomConstantClosure20261026a
open GenericResolventScalarMeasure20261025a
open GenericResolventUnboundedScalarMeasure20261025a
open GenericGlobalBorelProjection20261025a
open GenericBorelProjectionScalarRestriction20261026b

/-- Literal physical subtraction, with no probability rescaling. -/
def physicalMeanCentered (N : ℕ) [NeZero N] (f : QuotientL2 N) : QuotientL2 N :=
  f - ((∫ q, f q ∂carrierPushforward N) / (actualVolume N : ℂ)) • constantL2 N

theorem physicalMeanCentered_eq_sub_zeroProjection (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    physicalMeanCentered N f = f - actualZeroProjection N f := by
  rw [actualZeroProjection_apply_mean]
  rfl

/-- The real lambda-coordinate Borel projection, pulled back through the
same inverse-resolvent coordinate used to define actualLaplaceMeasure. -/
def actualLaplaceBorelProjection (N : ℕ) [NeZero N]
    (B : Set ℝ) (hB : MeasurableSet B) : QuotientL2 N →L[ℂ] QuotientL2 N :=
  globalBorelProjection (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
    (spectralLambda (actualGammaResolvent N) ⁻¹' B)
    ((measurable_spectralLambda (actualGammaResolvent N)) hB)

/-- Restriction in the genuine unbounded coordinate, retaining the zero fiber. -/
theorem actualLaplaceMeasure_zeroProjection_eq_restrict (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    actualLaplaceMeasure N (actualZeroProjection N f) =
      (actualLaplaceMeasure N f).restrict {0} := by
  change ((scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
      (globalBorelProjection (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
        (oneFiber (actualGammaResolvent N)) (oneFiber_measurable (actualGammaResolvent N)) f)).map
      (spectralLambda (actualGammaResolvent N))) =
    ((scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f).map
      (spectralLambda (actualGammaResolvent N))).restrict {0}
  rw [scalarMeasure_projection_eq_restrict]
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_spectralLambda (actualGammaResolvent N)) hB,
    Measure.restrict_apply ((measurable_spectralLambda (actualGammaResolvent N)) hB),
    Measure.restrict_apply hB,
    Measure.map_apply (measurable_spectralLambda (actualGammaResolvent N))
      (hB.inter measurableSet_singleton)]
  simp only [Set.preimage_inter, spectralLambda_preimage_zero]

/-- Main residual identity: the scalar measure is computed for the actual
physical mean-centered vector, rather than stipulated as a residual measure. -/
theorem actualLaplaceMeasure_meanCentered_eq_restrict (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    actualLaplaceMeasure N (physicalMeanCentered N f) =
      (actualLaplaceMeasure N f).restrict ({0}ᶜ : Set ℝ) := by
  rw [physicalMeanCentered_eq_sub_zeroProjection]
  change ((scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
      (f - globalBorelProjection (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
        (oneFiber (actualGammaResolvent N)) (oneFiber_measurable (actualGammaResolvent N)) f)).map
      (spectralLambda (actualGammaResolvent N))) =
    ((scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f).map
      (spectralLambda (actualGammaResolvent N))).restrict ({0}ᶜ : Set ℝ)
  rw [scalarMeasure_residual_eq_restrict_compl]
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_spectralLambda (actualGammaResolvent N)) hB,
    Measure.restrict_apply ((measurable_spectralLambda (actualGammaResolvent N)) hB),
    Measure.restrict_apply hB,
    Measure.map_apply (measurable_spectralLambda (actualGammaResolvent N))
      (hB.inter measurableSet_singleton.compl)]
  simp only [Set.preimage_inter, Set.preimage_compl, spectralLambda_preimage_zero]

/-- The removed measure is precisely the physical constant atom. -/
theorem actualLaplaceMeasure_zeroProjection_eq_atom (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    actualLaplaceMeasure N (actualZeroProjection N f) =
      ENNReal.ofReal (‖∫ q, f q ∂carrierPushforward N‖ ^ 2 / actualVolume N) •
        Measure.dirac (0 : ℝ) := by
  rw [actualLaplaceMeasure_zeroProjection_eq_restrict, Measure.restrict_singleton,
    actualLaplaceMeasure_zero_eq_mean_norm_sq]

/-- Exact positive-measure constant-atom plus residual decomposition. -/
theorem actualLaplaceMeasure_eq_constantAtom_add_meanCentered (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    actualLaplaceMeasure N f =
      ENNReal.ofReal (‖∫ q, f q ∂carrierPushforward N‖ ^ 2 / actualVolume N) •
        Measure.dirac (0 : ℝ) + actualLaplaceMeasure N (physicalMeanCentered N f) := by
  rw [← actualLaplaceMeasure_zeroProjection_eq_atom N f,
    actualLaplaceMeasure_zeroProjection_eq_restrict,
    actualLaplaceMeasure_meanCentered_eq_restrict,
    Measure.restrict_add_restrict_compl measurableSet_singleton]

theorem actualLaplaceMeasure_meanCentered_zero (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    actualLaplaceMeasure N (physicalMeanCentered N f) {0} = 0 := by
  rw [actualLaplaceMeasure_meanCentered_eq_restrict,
    Measure.restrict_apply measurableSet_singleton]
  simp only [Set.inter_compl_self, measure_empty]

/-- Physical mean zero is a consequence of the proved spectral restriction. -/
theorem physicalMeanCentered_integral_zero (N : ℕ) [NeZero N]
    (f : QuotientL2 N) :
    (∫ q, physicalMeanCentered N f q ∂carrierPushforward N) = 0 :=
  (actualLaplaceMeasure_zero_eq_zero_iff_mean_zero N (physicalMeanCentered N f)).mp
    (actualLaplaceMeasure_meanCentered_zero N f)

/-- The complex mixed spectral term vanishes for every real Borel set,
for two independent original vectors. This is not just real orthogonality. -/
theorem actual_constant_residual_spectral_cross_zero (N : ℕ) [NeZero N]
    (f g : QuotientL2 N) (B : Set ℝ) (hB : MeasurableSet B) :
    inner ℂ (actualLaplaceBorelProjection N B hB (actualZeroProjection N f))
      (physicalMeanCentered N g) = 0 := by
  rw [physicalMeanCentered_eq_sub_zeroProjection]
  exact projection_residual_cross_zero (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) f g
    (spectralLambda (actualGammaResolvent N) ⁻¹' B)
    (oneFiber (actualGammaResolvent N))
    ((measurable_spectralLambda (actualGammaResolvent N)) hB)
    (oneFiber_measurable (actualGammaResolvent N))

/-- Reverse orientation of the mixed complex coefficient. -/
theorem actual_residual_constant_spectral_cross_zero (N : ℕ) [NeZero N]
    (f g : QuotientL2 N) (B : Set ℝ) (hB : MeasurableSet B) :
    inner ℂ (actualLaplaceBorelProjection N B hB (physicalMeanCentered N g))
      (actualZeroProjection N f) = 0 := by
  rw [globalBorelProjection_inner (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N)
    (spectralLambda (actualGammaResolvent N) ⁻¹' B)
    ((measurable_spectralLambda (actualGammaResolvent N)) hB)]
  rw [← inner_conj_symm, actual_constant_residual_spectral_cross_zero N f g B hB,
    map_zero]

/-- Full complex polarization law for the physical constant sector of f
and the physical mean-centered sector of an independent vector g. -/
theorem actualLaplaceMeasure_constant_residual_linear_combination (N : ℕ) [NeZero N]
    (f g : QuotientL2 N) (a b : ℂ) :
    actualLaplaceMeasure N
      (a • actualZeroProjection N f + b • physicalMeanCentered N g) =
      (ENNReal.ofReal (‖a‖ ^ 2) *
        ENNReal.ofReal (‖∫ q, f q ∂carrierPushforward N‖ ^ 2 / actualVolume N)) •
          Measure.dirac (0 : ℝ) +
        ENNReal.ofReal (‖b‖ ^ 2) • actualLaplaceMeasure N (physicalMeanCentered N g) := by
  have hs : scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
      (a • actualZeroProjection N f + b • physicalMeanCentered N g) =
      ENNReal.ofReal (‖a‖ ^ 2) •
        scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
          (actualZeroProjection N f) +
      ENNReal.ofReal (‖b‖ ^ 2) •
        scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
          (physicalMeanCentered N g) := by
    simp only [physicalMeanCentered_eq_sub_zeroProjection N g]
    change scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
      (a • globalBorelProjection (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
        (oneFiber (actualGammaResolvent N)) (oneFiber_measurable (actualGammaResolvent N)) f +
       b • (g - globalBorelProjection (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
        (oneFiber (actualGammaResolvent N)) (oneFiber_measurable (actualGammaResolvent N)) g)) = _
    rw [scalarMeasure_complementary_linear_combination,
      scalarMeasure_projection_eq_restrict, scalarMeasure_residual_eq_restrict_compl]
  have hm := congrArg (fun μ : Measure (ResolventSpectrum (actualGammaResolvent N)) =>
    μ.map (spectralLambda (actualGammaResolvent N))) hs
  rw [Measure.map_add _ _ (measurable_spectralLambda (actualGammaResolvent N)),
    Measure.map_smul, Measure.map_smul] at hm
  change actualLaplaceMeasure N
      (a • actualZeroProjection N f + b • physicalMeanCentered N g) =
    ENNReal.ofReal (‖a‖ ^ 2) • actualLaplaceMeasure N (actualZeroProjection N f) +
      ENNReal.ofReal (‖b‖ ^ 2) • actualLaplaceMeasure N (physicalMeanCentered N g) at hm
  rw [actualLaplaceMeasure_zeroProjection_eq_atom, smul_smul] at hm
  exact hm

end
end ImbalancedChen.Part3.GammaMeanCenteredScalarMeasure20261026b
