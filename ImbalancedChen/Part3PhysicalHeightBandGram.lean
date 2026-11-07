import ImbalancedChen.Part3FiniteHeightScatteringGram
import ImbalancedChen.Part3WeightedHeightLogMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
# Literal dy/y^2 finite-height Gram and its boundary-kernel formula

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
This closes the coordinate gap: the left side integrates the physical
waves against the existing subtype heightMeasure, restricted to
exp(a)<y<=exp(b). The actual measure-preserving exponential map and its
radial exp(-r) density yield the log-coordinate Gram. There is no
assumed Jacobian or spectral normalization.
-/
namespace ImbalancedChen.Part3.PhysicalHeightBandGram20261026b
noncomputable section
open Set MeasureTheory
open CuspCylinderMeasure20261024z WeightedHeightLogMeasure20261026a
open HeightScatteringWaveGram20261026b FiniteLogHeightKernel20261026b
open FiniteHeightScatteringGram20261026b
attribute [local instance] Measure.Subtype.measureSpace

def heightLogBand (a b : ℝ) : Set PositiveHeight :=
  {y | Real.log (y : ℝ) ∈ Ioc a b}

theorem heightLogBand_measurable (a b : ℝ) : MeasurableSet (heightLogBand a b) :=
  measurableSet_Ioc.preimage (Real.measurable_log.comp measurable_subtype_coe)

theorem heightLogBand_eq_physical_band (a b : ℝ) :
    heightLogBand a b = {y : PositiveHeight | Real.exp a < (y : ℝ) ∧ (y : ℝ) ≤ Real.exp b} := by
  ext y
  change (a < Real.log (y : ℝ) ∧ Real.log (y : ℝ) ≤ b) ↔ _
  constructor
  · intro h
    constructor
    · simpa only [Real.exp_log y.property] using Real.exp_lt_exp.mpr h.1
    · simpa only [Real.exp_log y.property] using Real.exp_le_exp.mpr h.2
  · intro h
    constructor
    · apply Real.exp_lt_exp.mp
      simpa only [Real.exp_log y.property] using h.1
    · apply Real.exp_le_exp.mp
      simpa only [Real.exp_log y.property] using h.2

theorem scaledHeightEquiv_one_eq_expHeight (r : ℝ) :
    scaledHeightEquiv 1 (by norm_num) r = expHeight r := by
  apply Subtype.ext
  simp only [scaledHeightEquiv_coe, expHeight, div_one]

theorem heightLogBand_preimage (a b : ℝ) :
    (scaledHeightEquiv 1 (by norm_num)) ⁻¹' heightLogBand a b = Ioc a b := by
  ext r
  simp only [Set.mem_preimage, heightLogBand, Set.mem_setOf_eq,
    scaledHeightEquiv_coe, div_one, Real.log_exp]

/-- Arbitrary Bochner-integral transport on the literal physical band.
The normalized radial density exp(-r) is derived from heightMeasure. -/
theorem heightLogBand_integral (a b : ℝ) (q : PositiveHeight → ℂ) :
    (∫ y in heightLogBand a b, q y ∂heightMeasure) =
      ∫ r in Ioc a b, (Real.exp (-r) : ℝ) • q (expHeight r) := by
  have hmp := (scaledHeightEquiv_measurePreserving 1 (by norm_num)).restrict_preimage
    (heightLogBand_measurable a b)
  rw [heightLogBand_preimage] at hmp
  have hmap := hmp.integral_comp (scaledHeightEquiv 1 (by norm_num)).measurableEmbedding q
  rw [← hmap]
  unfold radialHeightMeasure
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (radialHeightDensity_continuous 1).measurable.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _ measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with r
  rw [ENNReal.toReal_ofReal (radialHeightDensity_pos (by norm_num : (0 : ℝ) < 1) r).le,
    scaledHeightEquiv_one_eq_expHeight]
  simp only [radialHeightDensity, one_mul]

def physicalBandScatteringGram (a b t u : ℝ) (c d : ℂ) : ℂ :=
  ∫ y in heightLogBand a b, star (scatteringWave t c y) * scatteringWave u d y ∂heightMeasure

/-- The original dy/y^2 physical finite band, with no missing Jacobian. -/
theorem physicalBandScatteringGram_eq_logGram (a b t u : ℝ) (c d : ℂ) (hab : a ≤ b) :
    physicalBandScatteringGram a b t u c d = finiteHeightScatteringGram a b t u c d := by
  unfold physicalBandScatteringGram finiteHeightScatteringGram
  rw [heightLogBand_integral, intervalIntegral.integral_of_le hab]
  apply integral_congr_ae
  filter_upwards with r
  rw [Complex.real_smul, Real.exp_neg, Complex.ofReal_inv]
  ring

/-- Literal physical-band four-kernel identity. -/
theorem physicalBandScatteringGram_eq_four_kernels
    (a b t u : ℝ) (c d : ℂ) (hab : a ≤ b) :
    physicalBandScatteringGram a b t u c d =
      logBandKernel a b (t - u) + d * logBandKernel a b (t + u) +
      star c * logBandKernel a b (-t - u) +
      star c * d * logBandKernel a b (u - t) := by
  rw [physicalBandScatteringGram_eq_logGram a b t u c d hab,
    finiteHeightScatteringGram_eq_four_kernels]

end
end ImbalancedChen.Part3.PhysicalHeightBandGram20261026b
