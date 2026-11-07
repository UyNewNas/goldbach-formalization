import ImbalancedChen.Part3ShiftOneEulerNormalizedTestUniqueness
import ImbalancedChen.Part3ActualInfinityCuspAnnihilator
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

A CONSTRUCTED original admissible normalized test with support [1,2].
The genuine smooth bump has center 3/2, inner radius 1/4 and outer radius
1/2. Multiplication by y^2 pays the physical dy/y^2 density, giving actual
height mean exactly one. For every alpha<=0 its actual weighted power
moment has real part at least 2^alpha>0. Thus the shift-one normalized-
test uniqueness theorem now has a fixed genuine test and no assumed
nonzero-moment field. Its original HeightSeed matches the existing
normalized original zeroSeed norm estimate's exact [1,2] input contract.

The old mean witness's wider support is NOT silently relabeled [1,2].
No geometric normalized-test bound is claimed automatically, and no
pointwise growth or global-mean L2 inference is introduced.
-/

namespace ImbalancedChen.Part3.ShiftOneEulerFixedNormalizedTest20261026b
noncomputable section
open Set MeasureTheory Filter
open CuspCylinderMeasure20261024z NormalizedHeightProfileScaling20261026b
open ShiftOneEulerClassification20261026b ShiftOneEulerTailSelection20261026b
open ShiftOneEulerNormalizedTestEstimate20261026b ShiftOneEulerNormalizedTestUniqueness20261026b
open ActualInfinityCuspAnnihilator20261026b
attribute [local instance] Measure.Subtype.measureSpace

def fixedTestBump : ContDiffBump (3 / 2 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def fixedNormalizedBump : ℝ → ℝ := fixedTestBump.normed (volume : Measure ℝ)

theorem fixedNormalizedBump_support_bounds {y : ℝ}
    (hy : y ∈ tsupport fixedNormalizedBump) : y ∈ Icc (1 : ℝ) 2 := by
  rw [fixedNormalizedBump, fixedTestBump.tsupport_normed_eq,
    Metric.mem_closedBall, Real.dist_eq, abs_le] at hy
  change -(1 / 2 : ℝ) ≤ y - 3 / 2 ∧ y - 3 / 2 ≤ 1 / 2 at hy
  constructor <;> linarith [hy.1, hy.2]

theorem fixedNormalizedBump_positive_support : tsupport fixedNormalizedBump ⊆ Ioi (0 : ℝ) :=
  fun y hy => zero_lt_one.trans_le (fixedNormalizedBump_support_bounds hy).1

def fixedHeightFunction (y : ℝ) : ℂ := (y : ℂ) ^ 2 * (fixedNormalizedBump y : ℂ)

theorem fixedHeightFunction_support : support fixedHeightFunction ⊆ Icc (1 : ℝ) 2 := by
  intro y hy
  have hb : fixedNormalizedBump y ≠ 0 := by
    intro hz
    exact hy (by simp only [fixedHeightFunction, hz, Complex.ofReal_zero, mul_zero])
  exact fixedNormalizedBump_support_bounds (subset_closure hb)

def fixedOriginalHeightSeed : HeightSeed where
  toFun := fixedHeightFunction
  continuous := (Complex.continuous_ofReal.pow 2).mul
    (Complex.continuous_ofReal.comp fixedTestBump.continuous_normed)
  compact := ((fixedTestBump.hasCompactSupport_normed (μ := (volume : Measure ℝ))).comp_left
    (by simp)).mul_left
  positive := by
    have hs : tsupport fixedHeightFunction ⊆ Icc (1 : ℝ) 2 :=
      closure_minimal fixedHeightFunction_support isClosed_Icc
    exact fun y hy => zero_lt_one.trans_le (hs hy).1

theorem fixedOriginalHeightSeed_support : support fixedOriginalHeightSeed.toFun ⊆ Icc (1 : ℝ) 2 :=
  fixedHeightFunction_support

theorem fixedOriginalHeightSeed_cinfty : ContDiff ℝ ∞ fixedOriginalHeightSeed.toFun :=
  (Complex.ofRealCLM.contDiff.pow 2).mul
    (Complex.ofRealCLM.contDiff.comp fixedTestBump.contDiff_normed)

def fixedRealProfile (y : PositiveHeight) : ℝ := (y : ℝ) ^ 2 * fixedNormalizedBump y
def fixedNormalizedTest (y : PositiveHeight) : ℂ := fixedOriginalHeightSeed.toFun y

theorem fixedNormalizedTest_eq_real (y : PositiveHeight) :
    fixedNormalizedTest y = (fixedRealProfile y : ℂ) := by
  change (y : ℂ) ^ 2 * (fixedNormalizedBump y : ℂ) =
    (((y : ℝ) ^ 2 * fixedNormalizedBump y : ℝ) : ℂ)
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]

theorem fixedNormalizedTest_continuous : Continuous fixedNormalizedTest :=
  fixedOriginalHeightSeed.continuous.comp continuous_subtype_val

theorem fixedRealProfile_continuous : Continuous fixedRealProfile :=
  (continuous_subtype_val.pow 2).mul (fixedTestBump.continuous_normed.comp continuous_subtype_val)

theorem fixedRealProfile_nonneg (y : PositiveHeight) : 0 ≤ fixedRealProfile y :=
  mul_nonneg (sq_nonneg _) (fixedTestBump.nonneg_normed (μ := (volume : Measure ℝ)) y)

theorem fixedRealProfile_compact : HasCompactSupport fixedRealProfile := by
  let a : PositiveHeight := ⟨1, by norm_num⟩
  let b : PositiveHeight := ⟨2, by norm_num⟩
  have hs : support fixedRealProfile ⊆ Icc a b := by
    intro y hy
    have hb : fixedNormalizedBump y ≠ 0 := by
      intro hz
      exact hy (by simp only [fixedRealProfile, hz, mul_zero])
    exact fixedNormalizedBump_support_bounds (subset_closure hb)
  have ht : tsupport fixedRealProfile ⊆ Icc a b := closure_minimal hs isClosed_Icc
  exact (positiveHeight_Icc_isCompact a b).of_isClosed_subset isClosed_tsupport ht

theorem fixedNormalizedTest_compact : HasCompactSupport fixedNormalizedTest := by
  have h : HasCompactSupport (fun y : PositiveHeight => (fixedRealProfile y : ℂ)) :=
    fixedRealProfile_compact.comp_left (by simp)
  simpa only [← fixedNormalizedTest_eq_real] using h

/-- Exact actual physical height mean, independently of quotient pairing. -/
theorem fixedRealProfile_height_mass_one : (∫ y, fixedRealProfile y ∂heightMeasure) = 1 := by
  calc
    _ = ∫ y : PositiveHeight, fixedNormalizedBump y := by
      rw [weightedHeight_integral]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        change (1 / (y : ℝ)) ^ 2 * ((y : ℝ) ^ 2 * fixedNormalizedBump y) = fixedNormalizedBump y
        field_simp [y.property.ne']
        <;> ring
    _ = ∫ y in Ioi (0 : ℝ), fixedNormalizedBump y := integral_subtype measurableSet_Ioi
    _ = ∫ y : ℝ, fixedNormalizedBump y := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      exact image_eq_zero_of_notMem_tsupport
        (fun ht => hy (fixedNormalizedBump_positive_support ht))
    _ = 1 := fixedTestBump.integral_normed (μ := (volume : Measure ℝ))

theorem fixedPowerProfile_integrable (alpha : ℝ) :
    Integrable (fun y : PositiveHeight => fixedRealProfile y * (y : ℝ) ^ alpha) heightMeasure := by
  have hp : Continuous (fun y : PositiveHeight => (y : ℝ) ^ alpha) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (Real.continuousAt_rpow_const (y : ℝ) alpha (Or.inl y.property.ne')).comp y
      continuous_subtype_val.continuousAt
  exact (fixedRealProfile_continuous.mul hp).integrable_of_hasCompactSupport
    fixedRealProfile_compact.mul_right

theorem fixedPowerMoment_eq_realIntegral (alpha : ℝ) :
    heightPowerPairing alpha fixedNormalizedTest =
      ((∫ y : PositiveHeight, fixedRealProfile y * (y : ℝ) ^ alpha ∂heightMeasure) : ℂ) := by
  unfold heightPowerPairing
  have heq : (fun y : PositiveHeight => star (fixedNormalizedTest y) * heightPower alpha y) =
      (fun y : PositiveHeight => ((fixedRealProfile y * (y : ℝ) ^ alpha : ℝ) : ℂ)) := by
    funext y
    rw [fixedNormalizedTest_eq_real]
    simp only [heightPower, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
  rw [heq, integral_complex_ofReal]

/-- Constructive actual nonzero weighted moment, with the exact [1,2]
support needed by normalized original zeroSeed norm estimates. -/
theorem fixedPowerMoment_re_lower {alpha : ℝ} (ha : alpha ≤ 0) :
    (2 : ℝ) ^ alpha ≤ (heightPowerPairing alpha fixedNormalizedTest).re := by
  have hreal : Integrable fixedRealProfile heightMeasure :=
    fixedRealProfile_continuous.integrable_of_hasCompactSupport fixedRealProfile_compact
  have hpoint : ∀ y : PositiveHeight,
      (2 : ℝ) ^ alpha * fixedRealProfile y ≤ fixedRealProfile y * (y : ℝ) ^ alpha := by
    intro y
    by_cases hz : fixedRealProfile y = 0
    · simp only [hz, mul_zero, zero_mul, le_refl]
    · have hb : fixedNormalizedBump y ≠ 0 := by
        intro h
        exact hz (by simp only [fixedRealProfile, h, mul_zero])
      have hy2 := (fixedNormalizedBump_support_bounds (subset_closure hb)).2
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos y.property hy2 ha) (fixedRealProfile_nonneg y)
  have hi := integral_mono (hreal.const_mul ((2 : ℝ) ^ alpha))
    (fixedPowerProfile_integrable alpha) (Eventually.of_forall hpoint)
  rw [integral_const_mul, fixedRealProfile_height_mass_one, mul_one] at hi
  rw [fixedPowerMoment_eq_realIntegral, Complex.ofReal_re]
  exact hi

theorem fixedAlphaMinusMoment_ne_zero : heightPowerPairing alphaMinus fixedNormalizedTest ≠ 0 := by
  have hl := fixedPowerMoment_re_lower (by linarith [alphaMinus_lt_negHalf] : alphaMinus ≤ 0)
  have hp : (0 : ℝ) < (2 : ℝ) ^ alphaMinus := Real.rpow_pos_of_pos (by norm_num) _
  intro hz
  rw [hz, Complex.zero_re] at hl
  exact (not_le_of_gt hp) hl

/-- Final scalar input variant uses a fixed CONSTRUCTED original test;
only the genuine geometric normalized-test bound remains to be supplied. -/
theorem physical_shiftOne_deficiency_fixedNormalizedTest_unique (f : ℝ → ℂ)
    (hC2 : ContDiffOn ℝ 2 f (Ioi (0 : ℝ)))
    (hODE : ∀ y : ℝ, 0 < y → -((y : ℂ) ^ 2) * deriv (deriv f) y + f y = 0)
    (hL2 : MemLp f 2 physicalTailMeasure)
    (C : ℝ) (hbound : NormalizedEulerTestBound C fixedNormalizedTest f) :
    ∀ y : ℝ, 0 < y → f y = 0 :=
  physical_shiftOne_deficiency_normalizedTest_unique f hC2 hODE hL2
    fixedNormalizedTest fixedNormalizedTest_continuous fixedNormalizedTest_compact
    fixedAlphaMinusMoment_ne_zero C hbound

end
end ImbalancedChen.Part3.ShiftOneEulerFixedNormalizedTest20261026b
