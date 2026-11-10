import ImbalancedChen.Part3OriginalFullModulusTestJets
import ImbalancedChen.Part3OriginalNativeCuspFunctionals
import ImbalancedChen.Part3ActualJCriticalLogBound
import ImbalancedChen.Part3ImaginaryOrderKQDerivative
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Drappeau (4.10) at weight zero, including the removable central value
on the original mode test with measure dq/q. The actual native Bessel
order derivative gives -8. No trace or spectral inequality is an input.
-/
namespace ImbalancedChen.Part3.OriginalPositiveMaassCentralTransform20261110

noncomputable section
open Set Filter Complex MeasureTheory
open scoped Topology MatrixGroups
open ActualGeneralJBesselSourceOnly ActualJLocalOrderHolomorphic20261026a
open ActualJCriticalOrderZero20261026a ActualJCriticalLogBound20261026a
open ImaginaryOrderKBesselSourceOnly ImaginaryOrderKQDerivativeSourceOnly
open ImaginaryOrderKExplicitMajorantSourceOnly OriginalSignedTraceInput20261102
open OriginalFullModulusSupport20261102 OriginalFullModulusTestJets20261102
open OriginalCompletedReciprocalSource20261102 OriginalPrimaryPacketRows20261102
open OriginalSimultaneousPrefixCompletion20261102 OriginalTwoZSourceAssembly20261102
open ActualFullCuspEigenbasis20261026b ActualCuspEigenbasisNativeLabels20261026b
open OriginalNativeCuspFunctionals20261102
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest spectralTest_contDiff)

private def density (ell : D4 → ℤ) (Y t q : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ)) * criticalJRealKernel q (t : ℂ) *
    (spectralTest ell Y q / (q : ℂ))

private def raw (ell : D4 → ℤ) (Y t q : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * I / (Real.sinh (Real.pi*t) : ℂ)) *
    ((generalJ (2*I*(t : ℂ)) q - generalJ (-(2*I*(t : ℂ))) q) *
      (spectralTest ell Y q / (q : ℂ)))

private theorem density_raw (ell : D4 → ℤ) (Y : ℝ) {t : ℝ} (ht : t ≠ 0) (q : ℝ) :
    density ell Y t q = raw ell Y t q := by
  rw [density, raw, criticalJRealKernel, criticalJQuotient_eq (Complex.ofReal_ne_zero.mpr ht),
    Complex.ofReal_sinh, Complex.ofReal_mul]
  ring

private theorem raw_measurable (ell : D4 → ℤ) (Y t : ℝ) :
    AEStronglyMeasurable (raw ell Y t) (volume.restrict (Ioi 0)) := by
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
  intro q hq
  have hp : -1 < (2*I*(t : ℂ)).re := by norm_num [Complex.mul_re, Complex.mul_im]
  have hn : -1 < (-(2*I*(t : ℂ))).re := by norm_num [Complex.mul_re, Complex.mul_im]
  exact (continuousAt_const.mul
    (((generalJ_differentiableAt hp hq).continuousAt.sub
      (generalJ_differentiableAt hn hq).continuousAt).mul
      ((spectralTest_contDiff ell Y).continuous.continuousAt.div
        Complex.continuous_ofReal.continuousAt (Complex.ofReal_ne_zero.mpr hq.ne')))).continuousWithinAt

private theorem density_continuous_zero (ell : D4 → ℤ) (Y : ℝ) {q : ℝ} (hq : 0 < q) :
    ContinuousAt (fun t : ℝ => density ell Y t q) 0 := by
  have h : ContinuousAt (fun t : ℝ => criticalJRealKernel q (t : ℂ)) 0 :=
    (criticalJRealKernel_analyticAt_zero hq).continuousAt.comp Complex.continuous_ofReal.continuousAt
  exact (continuousAt_const.mul h).mul continuousAt_const

private theorem density_measurable (ell : D4 → ℤ) (Y t : ℝ) :
    AEStronglyMeasurable (density ell Y t) (volume.restrict (Ioi 0)) := by
  by_cases ht : t = 0
  · subst t
    apply aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℝ)) (f := raw ell Y)
    · exact raw_measurable ell Y
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
      apply ((density_continuous_zero ell Y hq).tendsto.mono_left nhdsWithin_le_nhds).congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact density_raw ell Y ht q
  · exact (raw_measurable ell Y t).congr (ae_of_all _ (fun q => (density_raw ell Y ht q).symm))

private theorem compact_height_domination (ell : D4 → ℤ) {Y T : ℝ} (hY : 0 < Y)
    (hT : 0 ≤ T) :
    ∃ b : ℝ → ℝ, IntegrableOn b (Ioi 0) ∧ ∀ t : ℝ, |t| ≤ T →
      ∀ q : ℝ, 0 < q → ‖density ell Y t q‖ ≤ b q := by
  obtain ⟨C, hC, hK⟩ := exists_criticalJRealKernel_log_bound hT
  have hlog : ContinuousOn Real.log (Icc (Y/16) (16*Y)) := by
    intro q hq
    have hpos : 0 < q := lt_of_lt_of_le (by positivity : 0 < Y/16) hq.1
    exact (Real.continuousAt_log hpos.ne').continuousWithinAt
  obtain ⟨L, hL⟩ := (isCompact_Icc : IsCompact (Icc (Y/16) (16*Y))).exists_bound_of_continuousOn hlog
  let A := ‖2 * (Real.pi : ℂ)‖ * (C * (1 + |L|))
  refine ⟨fun q => A * ‖spectralTest ell Y q / (q : ℂ)‖,
    ((spectralTest_div_q_integrable ell hY).norm.const_mul A).integrableOn, ?_⟩
  intro t ht q hq
  by_cases hz : spectralTest ell Y q = 0
  · simp [density, hz]
  · have hs := spectralTest_support ell hY hz
    have hlogq : |Real.log q| ≤ |L| := (hL q ⟨hs.1.le, hs.2.le⟩).trans (le_abs_self L)
    have hker := (hK q hq t ht).trans
      (mul_le_mul_of_nonneg_left (add_le_add_left hlogq 1) hC.le)
    rw [density, norm_mul, norm_mul (2 * (Real.pi : ℂ)) (criticalJRealKernel q (t : ℂ))]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hker (norm_nonneg _))
      (norm_nonneg _)

/-- The extension uses the genuine J-order derivative at zero. -/
def plusTransform (ell : D4 → ℤ) (Y t : ℝ) : ℂ :=
  ∫ q in Ioi 0, density ell Y t q

def printedPlus (ell : D4 → ℤ) (Y t : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * I / (Real.sinh (Real.pi*t) : ℂ)) *
    ∫ q in Ioi (0 : ℝ), (generalJ (2*I*(t : ℂ)) q - generalJ (-(2*I*(t : ℂ))) q) *
      (spectralTest ell Y q / (q : ℂ))

def orderDerivativeIntegral (ell : D4 → ℤ) (Y : ℝ) : ℂ :=
  ∫ q in Ioi (0 : ℝ), actualJOrderDerivative 0 q * (spectralTest ell Y q / (q : ℂ))

theorem plusTransform_eq_printed (ell : D4 → ℤ) (Y : ℝ) {t : ℝ} (ht : t ≠ 0) :
    plusTransform ell Y t = printedPlus ell Y t := by
  rw [plusTransform, printedPlus, ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ (density_raw ell Y ht))

private theorem density_integrable (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) (t : ℝ) :
    IntegrableOn (density ell Y t) (Ioi 0) := by
  obtain ⟨b, hb, hbound⟩ := compact_height_domination ell hY (abs_nonneg t)
  apply hb.mono' (density_measurable ell Y t)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  exact hbound t le_rfl q hq

private theorem density_zero (ell : D4 → ℤ) (Y : ℝ) :
    density ell Y 0 =ᵐ[volume.restrict (Ioi 0)]
      fun q : ℝ => (-8 : ℂ) * (actualJOrderDerivative 0 q * (spectralTest ell Y q / (q : ℂ))) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  rw [density, Complex.ofReal_zero, criticalJRealKernel_zero hq]
  have hscalar : (2 * (Real.pi : ℂ)) * (-(4 / (Real.pi : ℂ))) = -8 := by
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring
  rw [← mul_assoc (2 * (Real.pi : ℂ)), hscalar, mul_assoc]

theorem orderDerivative_integrable (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun q : ℝ => actualJOrderDerivative 0 q * (spectralTest ell Y q / (q : ℂ)))
      (Ioi 0) := by
  have h := (integrable_congr (density_zero ell Y)).mp (density_integrable ell hY 0)
  have hs := h.const_mul ((-8 : ℂ)⁻¹)
  simpa only [← mul_assoc, inv_mul_cancel₀ (by norm_num : (-8 : ℂ) ≠ 0), one_mul] using hs

theorem plusTransform_zero (ell : D4 → ℤ) (Y : ℝ) :
    plusTransform ell Y 0 = -8 * orderDerivativeIntegral ell Y := by
  rw [plusTransform, orderDerivativeIntegral, ← integral_const_mul]
  exact integral_congr_ae (density_zero ell Y)

/-- The unrestricted positive-height transform has the asserted genuine
limit from either side of t=0, for the original test and dq/q. -/
theorem printedPlus_tendsto_zero (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) :
    Tendsto (printedPlus ell Y) (𝓝[≠] 0) (𝓝 (-8 * orderDerivativeIntegral ell Y)) := by
  obtain ⟨b, hb, hbound⟩ := compact_height_domination ell hY (by norm_num : (0 : ℝ) ≤ 1)
  have h : ContinuousAt (plusTransform ell Y) 0 := by
    apply tendsto_integral_filter_of_dominated_convergence b
    · exact Eventually.of_forall (density_measurable ell Y)
    · filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
        with t ht
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
      exact hbound t (abs_le.mpr ⟨ht.1.le, ht.2.le⟩) q hq
    · exact hb
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
      exact density_continuous_zero ell Y hq
  rw [← plusTransform_zero]
  apply (h.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact plusTransform_eq_printed ell Y ht

def KIntegral (ell : D4 → ℤ) (Y t : ℝ) : ℂ :=
  ∫ q in Ioi (0 : ℝ), (imaginaryOrderK t q : ℂ) * (spectralTest ell Y q / (q : ℂ))

/-- The native parameter t already denotes order 2it in imaginaryOrderK.
This is the printed negative-sign dq/q integral on the same mode test. -/
theorem KIntegral_integrable (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) (t : ℝ) :
    IntegrableOn (fun q : ℝ => (imaginaryOrderK t q : ℂ) * (spectralTest ell Y q / (q : ℂ)))
      (Ioi 0) := by
  have hcont : ContinuousOn (fun q : ℝ =>
      (imaginaryOrderK t q : ℂ) * (spectralTest ell Y q / (q : ℂ))) (Ioi 0) :=
    (Complex.continuous_ofReal.comp_continuousOn (imaginaryOrderK_differentiableOn_q t).continuousOn).mul
      ((spectralTest_contDiff ell Y).continuous.continuousOn.div Complex.continuous_ofReal.continuousOn
        (fun _ hq => Complex.ofReal_ne_zero.mpr hq.ne'))
  have hb := ((spectralTest_div_q_integrable ell hY).norm.const_mul (2/(Y/16))).integrableOn
    (s := Ioi (0 : ℝ))
  apply hb.mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with q hq
  by_cases hf : spectralTest ell Y q = 0
  · simp [hf]
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (imaginaryOrderK_abs_le t hq).trans
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) (spectralTest_support ell hY hf).1.le)

def signedRegularTransform (negative : Bool) (ell : D4 → ℤ) (Y t : ℝ) : ℂ :=
  if negative then 8 * (Real.cosh (Real.pi*t) : ℂ) * KIntegral ell Y t
  else plusTransform ell Y t

/-- Drappeau (4.17)/(4.19), at an actual native central eigenvector,
with the original sign and the original conjugated S20 row functional.
The K branch has factor 8. The J branch has the order derivative and
factor -8. This computes the spectral summand on each legal branch. -/
theorem original_central_row (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (J j : ℕ) (ell : D4 → ℤ)
    {N : ℝ} (hN : 0 < N) (ha : D.block.atom.residue ≠ 0)
    (z : ℕ) [NeZero z] (hz : 0 < z) (i : actualCuspBasisIndex z hz)
    (hi : actualCuspNativeEigenvalue z hz i = 1/4) :
    let Y := chartY0 D k upper j N
    let t := Real.sqrt (actualCuspNativeEigenvalue z hz i - 1/4)
    let P := starRingEnd ℂ (originalMFunctional J j ell z hz i) *
      originalNFunctional D r k upper negativeM ell z hz i
    Tendsto (printedPlus ell Y) (𝓝[≠] 0) (𝓝 (-8 * orderDerivativeIntegral ell Y)) ∧
      signedRegularTransform (traceNegative D k negativeM) ell Y t /
          (Real.cosh (Real.pi*t) : ℂ) * P =
        (if traceNegative D k negativeM then 8 * KIntegral ell Y 0
          else -8 * orderDerivativeIntegral ell Y) * P := by
  have hY := original_spectral_scale_pos D k upper j hN ha
  constructor
  · exact printedPlus_tendsto_zero ell hY
  · simp [hi, signedRegularTransform, plusTransform_zero]

end
end ImbalancedChen.Part3.OriginalPositiveMaassCentralTransform20261110
