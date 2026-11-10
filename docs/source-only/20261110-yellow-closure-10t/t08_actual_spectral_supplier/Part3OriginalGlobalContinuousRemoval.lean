import ImbalancedChen.Part3OriginalCumulativeContinuousRemoval

/-! All real heights in the original ABL continuous n-removal.  The
nonnegative integral is allowed to be infinite.  A finite reduced mass
then gives genuine integrability of the source and the Bochner bound. -/
namespace ImbalancedChen.Part3.OriginalGlobalContinuousRemoval20261110

noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
open OriginalCumulativeContinuousRemoval20261110 OriginalContinuousCuspGram20261110
open OriginalContinuousClassRemoval20261110 ActualContinuousClassFourier20261110
open OriginalSimultaneousPrefixCompletion20261102 OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 OriginalPrimaryPacketRows20261102
open OriginalTwoZFourierAssembly20261102 OriginalSignedTraceInput20261102
open P3NativePeriod64SamplingSourceOnly (D4)

variable (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k)
  (upper negativeM : Bool) (ell : D4 → ℤ)

def sourceDensity (t : ℝ) : ℝ :=
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  nativeMass z.val (fun a => source D r k z upper negativeM ell (fun n => nativeR a true n t)) /
    Real.cosh (Real.pi*t)

def reducedDensity (t : ℝ) : ℝ :=
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  nativeMass z.val (fun a => reduced D r k z upper negativeM ell (fun n => nativeR a true n t)) /
    Real.cosh (Real.pi*t)

private theorem source_cont : Continuous (sourceDensity D r k z upper negativeM ell) := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  exact marked_density_cont _ _ _ _ _

private theorem reduced_cont : Continuous (reducedDensity D r k z upper negativeM ell) := by
  letI : NeZero z.val := ⟨(levelCarrier_licensed D k z.property).1.ne'⟩
  exact marked_density_cont _ _ _ _ _

private theorem source_nonneg (t : ℝ) : 0 ≤ sourceDensity D r k z upper negativeM ell t := by
  dsimp only [sourceDensity,nativeMass]
  exact div_nonneg (Finset.sum_nonneg (fun a _ => div_nonneg (sq_nonneg _) (by positivity)))
    (Real.cosh_pos _).le

private theorem reduced_nonneg (t : ℝ) : 0 ≤ reducedDensity D r k z upper negativeM ell t := by
  dsimp only [reducedDensity,nativeMass]
  exact div_nonneg (Finset.sum_nonneg (fun a _ => div_nonneg (sq_nonneg _) (by positivity)))
    (Real.cosh_pos _).le

private theorem density_le (t : ℝ) : sourceDensity D r k z upper negativeM ell t ≤
    ((D.block.atom.residue.natAbs*k.1).divisors.card : ℝ)^2 *
      reducedDensity D r k z upper negativeM ell t := by
  simpa only [sourceDensity,reducedDensity,mul_div_assoc] using
    div_le_div_of_nonneg_right (original_native_removal D r k z upper negativeM ell t) (Real.cosh_pos _).le

/-- Whole real line with the same measure on both original densities.
The ordinary dt version is μ = volume. A restriction, or a nonnegative
test incorporated by withDensity, preserves the identical divisor cost. -/
theorem original_global_lintegral_removal (μ : Measure ℝ) :
    (∫⁻ t, ENNReal.ofReal (sourceDensity D r k z upper negativeM ell t) ∂μ) ≤
      ENNReal.ofReal (((D.block.atom.residue.natAbs*k.1).divisors.card : ℝ)^2) *
        ∫⁻ t, ENNReal.ofReal (reducedDensity D r k z upper negativeM ell t) ∂μ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro t
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (density_le D r k z upper negativeM ell t)

/-- Finiteness is needed only for the actual reduced mass. Both genuine
Bochner integrals and the pointwise-to-integral comparison follow. -/
theorem original_global_finite_removal (μ : Measure ℝ)
    (hred : (∫⁻ t, ENNReal.ofReal (reducedDensity D r k z upper negativeM ell t) ∂μ) < ∞) :
    Integrable (sourceDensity D r k z upper negativeM ell) μ ∧
    Integrable (reducedDensity D r k z upper negativeM ell) μ ∧
    (∫ t, sourceDensity D r k z upper negativeM ell t ∂μ) ≤
      ((D.block.atom.residue.natAbs*k.1).divisors.card : ℝ)^2 *
        ∫ t, reducedDensity D r k z upper negativeM ell t ∂μ := by
  have hG : Integrable (reducedDensity D r k z upper negativeM ell) μ :=
    ⟨(reduced_cont D r k z upper negativeM ell).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all μ (reduced_nonneg D r k z upper negativeM ell))).mpr hred⟩
  have hsrc := lt_of_le_of_lt (original_global_lintegral_removal D r k z upper negativeM ell μ)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hred)
  have hF : Integrable (sourceDensity D r k z upper negativeM ell) μ :=
    ⟨(source_cont D r k z upper negativeM ell).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all μ (source_nonneg D r k z upper negativeM ell))).mpr hsrc⟩
  refine ⟨hF,hG,?_⟩
  rw [← integral_const_mul]
  exact integral_mono hF (hG.const_mul _) (density_le D r k z upper negativeM ell)

end
end ImbalancedChen.Part3.OriginalGlobalContinuousRemoval20261110
