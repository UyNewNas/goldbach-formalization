/-!
SOURCE ONLY / UNCOMPILED.

This module does not redo the sharp full-cutoff certificate already supplied by
Part4ActualThirdTailBound. It adds the missing strict-domain and shrinking-cutoff
interface for that same actual ideal cap. The quantitative shrinking envelope is
obtained from the actual D(10) pointwise estimate and the existing improper
log-square integral, with a square enlargement for the xy ordering triangle.
No bound for the final integral is a hypothesis.

The imported Part4ActualThirdTailBound and SymmetricTriangleIntegral remain
source candidates: this file has not been compiled or kernel checked either.
No original constant, domain normalization, or global reserve is changed.
-/
import ImbalancedChen.Part4ActualThirdTailBound

set_option Elab.async false

namespace ImbalancedChen.P2CompleteThirdTailIntegral

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal

/-- The literal all-strict ordered tail. Every radial variable may approach
zero; there is no positive lower truncation hidden in this definition. -/
def strictTailMass (h : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Ioo 0 h, ∫⁻ x in Ioo z thirdPrefixRho, ∫⁻ y in Ioo z x,
    ENNReal.ofReal (if x + y + 3 * z < thirdPrefixTheta then
      thirdPrefixCorrectionKernel thirdPrefixTheta
        (actualExtendedThirdIdealCap x y z) x y z else 0)

/-- All three closed upper faces have zero Lebesgue mass. This equality
requires no integrability or measurability premise on the kernel itself. -/
theorem strictTailMass_eq_actual (h : ℝ) :
    strictTailMass h = actualExtendedThirdIdealTailMass 0 h := by
  unfold strictTailMass actualExtendedThirdIdealTailMass thirdPrefixTailMass
  simp only [mul_zero, sub_zero, Measure.restrict_Ioo_eq_restrict_Ioc,
    actualExtendedThirdIdealCap]

/-- Nonnegative masses are monotone in the actual cutoff, with no positivity
restriction on either cutoff and no Bochner-integrability prerequisite. -/
theorem actualTailMass_mono {a b : ℝ} (hab : a ≤ b) :
    actualExtendedThirdIdealTailMass 0 a ≤ actualExtendedThirdIdealTailMass 0 b := by
  unfold actualExtendedThirdIdealTailMass thirdPrefixTailMass
  exact lintegral_mono_set (fun z hz => ⟨hz.1, hz.2.trans hab⟩)

theorem strictTailMass_mono {a b : ℝ} (hab : a ≤ b) :
    strictTailMass a ≤ strictTailMass b := by
  rw [strictTailMass_eq_actual, strictTailMass_eq_actual]
  exact actualTailMass_mono hab

theorem strictTailMass_eq_zero_of_nonpos {h : ℝ} (hh : h ≤ 0) :
    strictTailMass h = 0 := by
  simp [strictTailMass, Ioo_eq_empty_of_le hh]

/-- A fixed D(10) coefficient, valid simultaneously for every smaller
cutoff. It is independent of any final integral enclosure. -/
def d10EnvelopeCoefficient : ℝ :=
  400 * OriginalThirdTailActualIdealSourceOnly.d10 /
    (thirdPrefixRho - 1 / 100) ^ 2

theorem d10EnvelopeCoefficient_nonneg : 0 ≤ d10EnvelopeCoefficient := by
  norm_num [d10EnvelopeCoefficient, OriginalThirdTailActualIdealSourceOnly.d10,
    thirdPrefixRho]

/-- Quantitative modulus for deleting the strict small-z tail. The coefficient
uses the square enlargement, so it is not advertised as the sharp Tnew bound. -/
def cutoffEnvelope (h : ℝ) : ℝ :=
  d10EnvelopeCoefficient * thirdTailLogPrimitive thirdPrefixRho h

/-- Direct integration of the actual D(10) majorant on every smaller tail.
The only inequality supplier is the already-derived pointwise profile decay;
no hypothesis asserting the value of this improper integral appears. -/
theorem actualTailMass_le_cutoffEnvelope {h : ℝ}
    (hh : 0 < h) (hsmall : h ≤ 1 / 100) :
    actualExtendedThirdIdealTailMass 0 h ≤ ENNReal.ofReal (cutoffEnvelope h) := by
  have hrho : 0 < thirdPrefixRho := by norm_num [thirdPrefixRho]
  have hhrho : h ≤ thirdPrefixRho :=
    hsmall.trans (by norm_num [thirdPrefixRho])
  have hc := d10EnvelopeCoefficient_nonneg
  change thirdPrefixTailMass thirdPrefixTheta actualExtendedThirdIdealCap
    thirdPrefixRho h ≤ ENNReal.ofReal (cutoffEnvelope h)
  calc
    _ ≤ ∫⁻ z in Ioc 0 h, ∫⁻ x in Ioc z thirdPrefixRho, ∫⁻ y in Ioc z x,
        ENNReal.ofReal (d10EnvelopeCoefficient * (1 / x) * (1 / y)) := by
      unfold thirdPrefixTailMass
      apply setLIntegral_mono' measurableSet_Ioc
      intro z hz
      apply setLIntegral_mono' measurableSet_Ioc
      intro x hx
      apply setLIntegral_mono' measurableSet_Ioc
      intro y hy
      apply ENNReal.ofReal_le_ofReal
      split_ifs with hgate
      · simpa only [d10EnvelopeCoefficient] using
          (OriginalThirdTailActualIdealSourceOnly.ideal_kernel_bound
            hz.1 (hz.2.trans hsmall) hy.1.le hy.2 hx.2).2
      · exact mul_nonneg
          (mul_nonneg hc (one_div_nonneg.mpr (hz.1.trans hx.1).le))
          (one_div_nonneg.mpr (hz.1.trans hy.1).le)
    _ ≤ ∫⁻ z in Ioc 0 h, ∫⁻ x in Ioc z thirdPrefixRho,
        ∫⁻ y in Ioc z thirdPrefixRho,
          ENNReal.ofReal (d10EnvelopeCoefficient * (1 / x) * (1 / y)) := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro z hz
      apply setLIntegral_mono' measurableSet_Ioc
      intro x hx
      exact lintegral_mono_set (fun y hy => ⟨hy.1, hy.2.trans hx.2⟩)
    _ = ENNReal.ofReal (cutoffEnvelope h) :=
      thirdTail_lintegral_majorant hc hrho hh hhrho

theorem strictTailMass_le_cutoffEnvelope {h : ℝ}
    (hh : 0 < h) (hsmall : h ≤ 1 / 100) :
    strictTailMass h ≤ ENNReal.ofReal (cutoffEnvelope h) := by
  rw [strictTailMass_eq_actual]
  exact actualTailMass_le_cutoffEnvelope hh hsmall

theorem strictTailMass_ne_top {h : ℝ}
    (hh : 0 < h) (hsmall : h ≤ 1 / 100) : strictTailMass h ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (strictTailMass_le_cutoffEnvelope hh hsmall)

/-- The sharp previously-written certificate propagates to every smaller
strict tail by a genuine measure-domain inclusion. -/
theorem strictTailMass_le_Tnew {h : ℝ} (hsmall : h ≤ 1 / 100) :
    strictTailMass h ≤ ENNReal.ofReal OriginalThirdTailActualIdealSourceOnly.Tnew := by
  rw [strictTailMass_eq_actual]
  exact (actualTailMass_mono hsmall).trans
    OriginalThirdTailActualIdealSourceOnly.ideal_tailMass_le_Tnew

/-- The new quantitative majorant really vanishes at the improper endpoint. -/
theorem cutoffEnvelope_tendsto_zero :
    Tendsto cutoffEnvelope (𝓝[>] 0) (𝓝 0) := by
  simpa only [cutoffEnvelope, mul_zero] using
    (tendsto_thirdTailLogPrimitive_zero
      (by norm_num [thirdPrefixRho] : 0 < thirdPrefixRho)).const_mul
        d10EnvelopeCoefficient

/-- Vanishing is proved at the nonnegative-mass level before toReal is used. -/
theorem strictTailMass_tendsto_zero :
    Tendsto strictTailMass (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) := by
  have hupper : Tendsto (fun h => ENNReal.ofReal (cutoffEnvelope h))
      (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal cutoffEnvelope_tendsto_zero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper (Eventually.of_forall fun _ => bot_le) ?_
  have hsmall : Iio ((1 : ℝ) / 100) ∈ 𝓝[>] (0 : ℝ) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hs
  exact strictTailMass_le_cutoffEnvelope hh hs.le

/-- The existing closed manuscript functional receives the same new cutoff
modulus, including its old own-cube boundary and actual ideal cap. -/
theorem manuscriptIntegral_le_cutoffEnvelope {h : ℝ}
    (hh : 0 < h) (hsmall : h ≤ 1 / 100) :
    (∫ t in actualExtendedThirdManuscriptTailRegion 0 h,
      actualExtendedThirdOrderedKernel 0 (t 0) (t 1) (t 2)) ≤ cutoffEnvelope h := by
  have hs : h ≤ thirdPrefixTailMargin / 4 :=
    hsmall.trans (by norm_num [thirdPrefixTailMargin])
  rw [integral_actualExtendedThirdManuscriptKernel_eq_core (by norm_num) hs]
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (actualTailMass_le_cutoffEnvelope hh hsmall)
  have hp : 0 ≤ thirdTailLogPrimitive thirdPrefixRho h := by
    have hlog : 0 ≤ Real.log (thirdPrefixRho / h) :=
      Real.log_nonneg ((le_div_iff₀ hh).2
        (hsmall.trans (by norm_num [thirdPrefixRho])))
    unfold thirdTailLogPrimitive
    positivity
  have hnonneg : 0 ≤ cutoffEnvelope h :=
    mul_nonneg d10EnvelopeCoefficient_nonneg hp
  simpa only [ENNReal.toReal_ofReal hnonneg] using hb

end
end ImbalancedChen.P2CompleteThirdTailIntegral
