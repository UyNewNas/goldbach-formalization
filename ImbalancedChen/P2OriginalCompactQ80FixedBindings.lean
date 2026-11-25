import ImbalancedChen.P2OriginalCompactQ80Arithmetic
import ImbalancedChen.P2FirstIntegralPolynomialEnclosure
import ImbalancedChen.Part4ActualThirdTailBound

/-!
SOURCE ONLY / UNEVALUATED / UNCOMPILED / broad endpoints OPEN.

Bindings for the unchanged original Q80 firstBounds, tailUpper and fixedUpper.
The first comparison uses the general analytic polynomial enclosure at orders
24,24 and the literal firstSeries 21, followed by the original ceiling. It does
not compare the unrelated selected catalog endpoint with the original source
endpoint. The exact rational comparison proof below has NOT been executed.

The tail uses val(dInteger 10) from the original grid=16384, maximum=12 Q80
table. Its actual gap bound and quadratic decay feed the existing ordered-half
integral theorem. The original log32 and I80 operations enclose its scalar in
their original order. Neither the later P112 anchor nor Tnew is used.

Only an upper fixed-component bound is claimed. In particular fixedLower and
the even firstSeries 20 are unchanged and have no new lower-bound theorem here.
No compact-run, stopping, resource, full functional, or kernel receipt follows.
Install this file only after the frozen L Arithmetic/Encloser/Table sources at
their registered ImbalancedChen module names; no frozen file imports this one.
-/

namespace ImbalancedChen.P2OriginalCompactQ80FixedBindingsSourceOnly

noncomputable section

open Set MeasureTheory
open scoped ENNReal
open Certificates.P2HistoricQ80DefectLookup
open Certificates.P2HistoricI80DivisionSoundness
open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80ArithmeticSourceOnly
open OriginalU2CoupledRecurrenceSourceOnly
open P4AActualSquaredGapDecay20261024zSourceOnly

namespace First

open P2FirstIntegralSeriesSourceOnly
open P2FirstIntegralPolynomialEnclosureSourceOnly

/-- The actual unrounded odd partial sum in original firstBounds. -/
def partialUpperQ : ℚ :=
  4 * (firstSeries 21).2 / P2OriginalCompactQ80EncloserSourceOnly.theta

/-- Exact finite comparison request, not a saved endpoint premise. The higher
orders are chosen for comparison against the original odd-21 partial sum.
The comparison's truth and resource sufficiency remain UNEVALUATED. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem polynomial_upper_le_original_odd_partial :
    centerQ 24 24 + radiusQ 24 24 ≤ partialUpperQ := by
  norm_num [centerQ, coefficientQ, degree, radiusQ, errorQ, dQ,
    partialUpperQ, firstSeries, P2OriginalCompactQ80EncloserSourceOnly.theta,
    P2OriginalCompactQ80EncloserSourceOnly.rho, Finset.sum_range_succ]

/-- The original final upper integer is exactly the standard single Q80
ceiling of the actual odd-21 partial sum, without evaluating that integer. -/
theorem firstBounds_upper_eq_point :
    firstBounds.upper = (I80.point partialUpperQ).hi := by
  rw [point_constructor_source]
  rfl

theorem originalFirstIntegral_le_partialUpperQ :
    originalFirstIntegral ≤ (partialUpperQ : ℝ) := by
  have ha := (originalFirstIntegral_polynomial_enclosure 24 24).2
  have hq : ((centerQ 24 24 + radiusQ 24 24 : ℚ) : ℝ) ≤
      (partialUpperQ : ℝ) := by
    exact_mod_cast polynomial_upper_le_original_odd_partial
  exact ha.trans hq

/-- Actual first integral bounded by the actual original upper integer. -/
theorem originalFirstIntegral_le_firstBounds_upper :
    originalFirstIntegral ≤ val firstBounds.upper := by
  rw [firstBounds_upper_eq_point]
  exact originalFirstIntegral_le_partialUpperQ.trans
    ((contains_iff _ _).1 (I80.point_contains partialUpperQ)).2

theorem literal_first_integral_le_firstBounds_upper :
    (4 / (299 / 500 : ℝ)) *
        (∫ s in (2 : ℝ)..((299 / 500 : ℝ) / (19 / 96 : ℝ) - 1),
          Real.log (s - 1) / s) ≤ val firstBounds.upper := by
  simpa only [originalFirstIntegral, kernel, stop,
    P2FirstIntegralSeriesSourceOnly.theta, P2FirstIntegralSeriesSourceOnly.rho]
    using originalFirstIntegral_le_firstBounds_upper

end First

/-- The original Q80 max12 anchor, not an evaluated or stored D10 literal. -/
def tailAnchor : ℝ := val (dInteger 10)

theorem actual_gap_ten_le_tailAnchor :
    upper (10 : ℝ) - lower (10 : ℝ) ≤ tailAnchor :=
  dInteger_bounds_actual_gap 10 (by norm_num) (by norm_num)

theorem tailAnchor_nonneg : 0 ≤ tailAnchor :=
  (normalized_gap_nonneg (s := (10 : ℝ)) (by norm_num)).trans
    actual_gap_ten_le_tailAnchor

/-- Exact scalar from the existing ordered-half integral with original s0=10.
The polynomial in the logarithm is evaluated only by interval soundness. -/
def originalTailScalar : ℝ :=
  (2 * tailAnchor * 100 * (1 / 100) / ((19 / 96 : ℝ) - 1 / 100)^2) *
    (Real.log (475 / 24 : ℝ)^2 + 2 * Real.log (475 / 24 : ℝ) + 2)

theorem originalTailScalar_nonneg : 0 ≤ originalTailScalar := by
  have hd := tailAnchor_nonneg
  have hp : 0 ≤ Real.log (475 / 24 : ℝ)^2 +
      2 * Real.log (475 / 24 : ℝ) + 2 := by
    nlinarith only [sq_nonneg (Real.log (475 / 24 : ℝ) + 1)]
  exact mul_nonneg (by positivity) hp

/-- Actual ideal-cap pointwise estimate with the original table anchor.
This is the pointwise input to an already available integral theorem; no
integration or later numerical scalar certificate is repeated. -/
theorem original_ideal_kernel_le_anchor {x y z : ℝ}
    (hz : 0 < z) (hzh : z ≤ 1 / 100) (hzy : z ≤ y)
    (hyx : y ≤ x) (hxrho : x ≤ thirdPrefixRho) :
    thirdPrefixCorrectionKernel thirdPrefixTheta
        (actualExtendedThirdIdealCap x y z) x y z ≤
      (400 * tailAnchor / (thirdPrefixRho - 1 / 100)^2) * (1 / x) * (1 / y) := by
  have hx : 0 < x := hz.trans_le (hzy.trans hyx)
  have hy : 0 < y := hz.trans_le hzy
  have hg := OriginalThirdIdealRhoMarginSourceOnly.literal_ideal_original_tail_geometry
    hz hzh hyx hxrho
  have hs := hg.2.2.2.2
  have hst : (actualExtendedThirdIdealCap x y z - x - y - z) / z ≤
      (thirdPrefixTheta - x - y - z) / z :=
    (div_le_div_iff_of_pos_right hz).2 (by linarith only [hg.2.1])
  have hdiff := thirdTailLowerFactor_difference
    (by linarith only [hs] :
      (2 : ℝ) ≤ (actualExtendedThirdIdealCap x y z - x - y - z) / z) hst
  have hnorm :
      thirdTailLowerFactor ((thirdPrefixTheta - x - y - z) / z) -
          thirdTailLowerFactor ((actualExtendedThirdIdealCap x y z - x - y - z) / z) ≤
        upper ((actualExtendedThirdIdealCap x y z - x - y - z) / z) -
          lower ((actualExtendedThirdIdealCap x y z - x - y - z) / z) := by
    rw [normalized_gap_eq_actualSieveGap_div]
    exact hdiff.2
  have hdecay := normalized_gap_le_quadratic_tail (k := (10 : ℝ))
    (by norm_num) hs
  have hgap := hdecay.trans
    (mul_le_mul_of_nonneg_right actual_gap_ten_le_tailAnchor (sq_nonneg _))
  have hres : thirdPrefixRho - 1 / 100 ≤
      actualExtendedThirdIdealCap x y z - x - y - z := by
    have hm : thirdPrefixRho ≤ actualExtendedThirdIdealCap x y z - x - y := by
      simpa only [thirdPrefixRho] using hg.1
    linarith only [hm, hzh]
  have hlow : 0 < thirdPrefixRho - 1 / 100 := by norm_num [thirdPrefixRho]
  have hrespos : 0 < actualExtendedThirdIdealCap x y z - x - y - z :=
    hlow.trans_le hres
  have hden : 0 < x * y * z^2 := by positivity
  have hd := tailAnchor_nonneg
  unfold thirdPrefixCorrectionKernel
  calc
    _ ≤ 4 * (tailAnchor *
        (10 / ((actualExtendedThirdIdealCap x y z - x - y - z) / z))^2) /
          (x * y * z^2) :=
      (div_le_div_iff_of_pos_right hden).2
        (mul_le_mul_of_nonneg_left (hnorm.trans hgap) (by norm_num))
    _ = 400 * tailAnchor /
        (x * y * (actualExtendedThirdIdealCap x y z - x - y - z)^2) := by
      field_simp [hx.ne', hy.ne', hz.ne', hrespos.ne']
      ring
    _ ≤ 400 * tailAnchor / (x * y * (thirdPrefixRho - 1 / 100)^2) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      gcongr
    _ = (400 * tailAnchor / (thirdPrefixRho - 1 / 100)^2) * (1 / x) * (1 / y) := by
      field_simp [hx.ne', hy.ne', hlow.ne']
      <;> ring

theorem original_tailMass_le_scalar :
    thirdPrefixTailMass thirdPrefixTheta actualExtendedThirdIdealCap
      thirdPrefixRho (1 / 100) ≤ ENNReal.ofReal originalTailScalar := by
  exact OriginalThirdOrderedTailSourceOnly.originalNumericalTailMass_le_of_pointwise
    thirdPrefixTheta actualExtendedThirdIdealCap tailAnchor tailAnchor_nonneg
    (by
      intro x y z hz hzh hzy hyx hxrho
      exact original_ideal_kernel_le_anchor hz hzh hzy hyx hxrho)

/-- The sole tail division guard is derived from its literal positive rational
denominator. This small exact rounding proof is also UNEVALUATED. -/
theorem tail_denominator_lo_pos :
    0 < (I80.point ((rho - cutoff)^2)).lo := by
  rw [point_constructor_source]
  norm_num [rho, cutoff, scale]

/-- Every original I80/log32 operation in tailInterval contains the exact
ordered-tail scalar. In particular the raw anchor remains the original one. -/
theorem tailInterval_contains_scalar : tailInterval.Contains originalTailScalar := by
  have hd : (I80.raw (dInteger 10)).Contains tailAnchor := by
    simpa [tailAnchor, val, scale, Q] using I80.raw_contains (dInteger 10)
  have hell := logI_contains (rho / cutoff) (by norm_num [rho, cutoff])
  have hp := I80.add_contains
    (I80.add_contains (I80.mul_contains hell hell)
      (I80.mul_contains (I80.point_contains 2) hell)) (I80.point_contains 2)
  have hn := I80.mul_contains
    (I80.mul_contains
      (I80.mul_contains (I80.mul_contains (I80.point_contains 2) hd)
        (I80.point_contains (10^2))) (I80.point_contains cutoff)) hp
  have h := historicalDiv_contains hn (I80.point_contains ((rho - cutoff)^2))
    tail_denominator_lo_pos
  unfold tailInterval
  convert h using 1 <;> norm_num [originalTailScalar, rho, cutoff] <;> ring

theorem originalTailScalar_le_tailUpper : originalTailScalar ≤ val tailUpper :=
  ((contains_iff _ _).1 tailInterval_contains_scalar).2

theorem original_tailMass_le_tailUpper :
    thirdPrefixTailMass thirdPrefixTheta actualExtendedThirdIdealCap
      thirdPrefixRho (1 / 100) ≤ ENNReal.ofReal (val tailUpper) :=
  original_tailMass_le_scalar.trans (ENNReal.ofReal_le_ofReal originalTailScalar_le_tailUpper)

theorem original_tailMass_ne_top :
    thirdPrefixTailMass thirdPrefixTheta actualExtendedThirdIdealCap
      thirdPrefixRho (1 / 100) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top original_tailMass_le_tailUpper

theorem original_canonical_tail_le_tailUpper :
    thirdPrefixTail thirdPrefixTheta actualExtendedThirdIdealCap
      thirdPrefixRho (1 / 100) ≤ val tailUpper := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top original_tailMass_le_scalar
  have hs : thirdPrefixTail thirdPrefixTheta actualExtendedThirdIdealCap
      thirdPrefixRho (1 / 100) ≤ originalTailScalar := by
    simpa only [thirdPrefixTail, ENNReal.toReal_ofReal originalTailScalar_nonneg] using h
  exact hs.trans originalTailScalar_le_tailUpper

theorem original_manuscript_tail_integral_le_tailUpper :
    (∫ t in actualExtendedThirdManuscriptTailRegion 0 (1 / 100),
      actualExtendedThirdOrderedKernel 0 (t 0) (t 1) (t 2)) ≤ val tailUpper := by
  rw [integral_actualExtendedThirdManuscriptKernel_eq_core
    (by norm_num : (0 : ℝ) ≤ 1 / 384)
    (by norm_num [thirdPrefixTailMargin] : (1 / 100 : ℝ) ≤ thirdPrefixTailMargin / 4)]
  have hcap : actualExtendedThirdIdealCap = actualExtendedThirdBufferedCap 0 := by
    funext x y z
    rfl
  simpa only [thirdPrefixTail, hcap, actualExtendedThirdIdealTailMass,
    mul_zero, sub_zero] using original_canonical_tail_le_tailUpper

/-- Exact cast of the original fixedUpper formula; no saved constant. -/
theorem fixedUpper_cast_eq :
    (fixedUpper : ℝ) = 4 / (299 / 500 : ℝ) +
      val firstBounds.upper + val tailUpper := by
  simp only [fixedUpper, theta, val, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_intCast, Int.cast_add]
  ring

/-- Canonical fixed source upper bound. No compact integral, finite-run total,
selected savings or global endpoint is a premise or conclusion. -/
theorem original_fixed_source_le_fixedUpper :
    4 / (299 / 500 : ℝ) + P2FirstIntegralSeriesSourceOnly.originalFirstIntegral +
      thirdPrefixTail thirdPrefixTheta actualExtendedThirdIdealCap
        thirdPrefixRho (1 / 100) ≤ (fixedUpper : ℝ) := by
  rw [fixedUpper_cast_eq]
  exact add_le_add
    (add_le_add_left First.originalFirstIntegral_le_firstBounds_upper _)
    original_canonical_tail_le_tailUpper

/-- Same fixed source bound in the actual manuscript tuple-space integral. -/
theorem original_fixed_manuscript_source_le_fixedUpper :
    4 / (299 / 500 : ℝ) + P2FirstIntegralSeriesSourceOnly.originalFirstIntegral +
      (∫ t in actualExtendedThirdManuscriptTailRegion 0 (1 / 100),
        actualExtendedThirdOrderedKernel 0 (t 0) (t 1) (t 2)) ≤ (fixedUpper : ℝ) := by
  rw [fixedUpper_cast_eq]
  exact add_le_add
    (add_le_add_left First.originalFirstIntegral_le_firstBounds_upper _)
    original_manuscript_tail_integral_le_tailUpper

end
end ImbalancedChen.P2OriginalCompactQ80FixedBindingsSourceOnly
