import ImbalancedChen.Part5OriginalH430D5D7PositiveRationalLower

/-!
P5.6 / h34, unchanged manuscript W2 geometry.
New strictly positive contribution from the previously unpaid FIRST D5
AFFINE SUPPORT PIECE. The prior second piece and entire real third
piece are retained. Complete lambda, count and h34 remain OPEN.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430D5FirstAffinePositive

noncomputable section

open Set MeasureTheory
open scoped Interval
open Certificates
open P2EnhancedSeedSingletonPrimitive (a0)
open P2EnhancedSeedD5PlusGeometry
open P2EnhancedSeedD5PlusLogFubini
open P2EnhancedSeedActualFeedbackAssembly
open P2EnhancedSeedActualSevenLogIdentity

/-- Exact rational certificate of the logarithm, not float input. -/
private theorem rational_log_thirteen_tenths :
    (1 / 4 : ℝ) ≤ Real.log (13 / 10 : ℝ) := by
  let c : RationalLogCertificate :=
    ⟨(13 / 10 : ℚ), 2, logSeriesLower (13 / 10) 2,
      logSeriesUpper (13 / 10) 2⟩
  have hc : c.check = true := by
    simpa only [RationalLogCertificate.check, decide_eq_true_eq] using
      (show c.Valid from ⟨by norm_num, le_rfl, le_rfl⟩)
  have h := (RationalLogCertificate.check_sound c hc).1
  have hn : (1 / 4 : ℝ) ≤
      (logSeriesLower (13 / 10 : ℚ) 2 : ℝ) := by
    norm_num [logSeriesLower, logParameter, Finset.sum_range_succ]
  exact hn.trans (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h)

/-- True first D5 support has lower=supportSum-u and upper=cap.
Uniform argument >=13/10 follows from geometry and product bounds. -/
theorem first_affine_argument_ge_thirteen_tenths
    {u : ℝ} (hu : u ∈ Icc a0 cutOne) :
    (13 / 10 : ℝ) ≤
      cap * (1 - u - (supportSum - u)) /
        ((supportSum - u) * (1 - u - cap)) := by
  have htop : cutOne ≤ top :=
    (le_of_lt three_cut_order.2.1).trans (le_of_lt three_cut_order.2.2)
  have hgeom : u ∈ Icc a0 top := ⟨hu.1, hu.2.trans htop⟩
  have hg := slice_geometry hgeom
  have ha := first_affine hu
  have hlow : 0 < supportSum - u := by
    simpa only [ha.1] using hg.2.1
  have hhigh : cap < 1 - u := by
    simpa only [ha.2] using hg.2.2.2
  have hden : 0 < (supportSum-u) * (1-u-cap) :=
    mul_pos hlow (by linarith only [hhigh])
  have ht : 0 ≤ u-a0 := sub_nonneg.mpr hu.1
  have hb : 0 ≤ 1-a0-cap := by norm_num [a0,cap]
  have hprod : 0 ≤ (u-a0)*((supportSum-u)+(1-a0-cap)) :=
    mul_nonneg ht (add_nonneg hlow.le hb)
  have hdenBound :
      (supportSum-u)*(1-u-cap) ≤
        (supportSum-a0)*(1-a0-cap) := by
    nlinarith only [hprod]
  have hconst :
      (13/10 : ℝ)*((supportSum-a0)*(1-a0-cap)) ≤
        cap*(1-supportSum) := by
    norm_num [a0,cap,supportSum]
  rw [show (1-u-(supportSum-u) : ℝ) = 1-supportSum by ring]
  apply (le_div_iff₀ hden).mpr
  nlinarith only [hdenBound,hconst]

/-- Genuine pointwise lower on the original first D5 affine subpiece. -/
theorem first_affine_slice_ge_one
    {u : ℝ} (hu : u ∈ Icc a0 cutOne) :
    (1 : ℝ) ≤ logSlice u (supportSum-u) cap := by
  have htop : cutOne ≤ top :=
    (le_of_lt three_cut_order.2.1).trans (le_of_lt three_cut_order.2.2)
  have hgeom : u ∈ Icc a0 top := ⟨hu.1,hu.2.trans htop⟩
  have hg := slice_geometry hgeom
  have hpos : 0 < u*(1-u) :=
    mul_pos hg.1 (by linarith only [hg.2.1,hg.2.2.1,hg.2.2.2])
  have hlog : (1/4 : ℝ) ≤ Real.log
      (cap*(1-u-(supportSum-u))/((supportSum-u)*(1-u-cap))) :=
    rational_log_thirteen_tenths.trans
      (Real.log_le_log (by norm_num : (0 : ℝ)<13/10)
        (first_affine_argument_ge_thirteen_tenths hu))
  have hquarter : u*(1-u) ≤ (1/4 : ℝ) := by
    nlinarith [sq_nonneg (u-1/2)]
  unfold logSlice
  apply (le_div_iff₀ hpos).mpr
  nlinarith only [hlog,hquarter]

/-- New strict positive integral mass from the WHOLE first affine piece. -/
theorem first_affine_integral_ge_37_per_1000 :
    (37/1000 : ℝ) ≤ ∫ u in a0..cutOne, outerSlice u := by
  have ha : a0 ≤ cutOne := le_of_lt three_cut_order.1
  have hb : cutOne ≤ top :=
    (le_of_lt three_cut_order.2.1).trans (le_of_lt three_cut_order.2.2)
  have hi := intervalIntegrable_outerSlice (le_refl a0) ha hb
  have hmono := intervalIntegral.integral_mono_on ha
    intervalIntegrable_const hi (fun u hu => by
      change (1 : ℝ) ≤ logSlice u (lower u) (upper u)
      rw [(first_affine hu).1,(first_affine hu).2]
      exact first_affine_slice_ge_one hu)
  have hval : (cutOne-a0)*(1 : ℝ) ≤
      ∫ u in a0..cutOne,outerSlice u := by
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hmono
  have hwidth : (37/1000 : ℝ) ≤ cutOne-a0 := by
    norm_num [a0,cutOne]
  nlinarith only [hval,hwidth]

/-- Full original D5: first >=.037, previously paid middle >=.037,
and the actual third region is nonnegative. -/
theorem actual_d5Logs_ge_74_per_1000 :
    (74/1000 : ℝ) ≤ d5Logs := by
  have ha : a0 ≤ cutOne := le_of_lt three_cut_order.1
  have hb : cutOne ≤ (3/10 : ℝ) := by norm_num [cutOne]
  have hc : (3/10 : ℝ) ≤ top := by norm_num [top]
  have hI₁ := intervalIntegrable_outerSlice (le_refl a0) ha (hb.trans hc)
  have hI₂ := intervalIntegrable_outerSlice ha hb hc
  have hI₃ := intervalIntegrable_outerSlice (ha.trans hb) hc (le_refl top)
  have hI₁₂ := intervalIntegrable_outerSlice (le_refl a0) (ha.trans hb) hc
  have hR : 0 ≤ ∫ u in (3/10 : ℝ)..top,outerSlice u := by
    have h := intervalIntegral.integral_mono_on hc
      intervalIntegrable_const hI₃
      (fun u hu =>
        Part5OriginalH430D5D7PositiveRationalLower.actual_d5_outer_nonneg
          ⟨(ha.trans hb).trans hu.1,hu.2⟩)
    simpa only [intervalIntegral.integral_const,smul_zero] using h
  have hL := first_affine_integral_ge_37_per_1000
  have hM :=
    Part5OriginalH430D5D7PositiveRationalLower.actual_d5_middle_interval_ge_37_per_1000
  have hSplit₁ := intervalIntegral.integral_add_adjacent_intervals hI₁ hI₂
  have hSplit₂ := intervalIntegral.integral_add_adjacent_intervals hI₁₂ hI₃
  rw [Part5OriginalH430D5D7PositiveRationalLower.actual_d5Logs_eq_outer]
  linarith only [hR,hL,hM,hSplit₁,hSplit₂]

/-- The untouched actual seven-source coefficient, /5 once.
Only a partial candidate: 0.0646 < 0.13. -/
theorem actual_lambda_ge_323_over_5000 :
    (323/5000 : ℝ) ≤ lambda := by
  have hs0 :=
    Part5OriginalH430ThreeSingletonRationalLower.original_singleton_zero_ge_57_per_1000
  have hs1 :=
    Part5OriginalH430ThreeSingletonRationalLower.original_singleton_one_ge_1_per_200
  have hs2 :=
    Part5OriginalH430ThreeSingletonRationalLower.original_singleton_two_ge_29_per_1000
  have hd5 := actual_d5Logs_ge_74_per_1000
  have hd6 :=
    Part5OriginalH430ActualD6BisectedRational.actual_d6Log_ge_11_over_100
  have hd7 := Part5OriginalH430D5D7PositiveRationalLower.actual_d7Log_ge_1_per_125
  have hd8 :=
    Part5OriginalH430D8SecondAffineRationalLower.actual_d8Logs_ge_1_over_25
  rw [lambda_exact_seven_logs]
  linarith

theorem actual_feedback_one_fiftieth_ge_323_over_250000 :
    (323/250000 : ℝ) ≤ actualFeedback (1/50) := by
  rw [actualFeedback_one_fiftieth]
  have h := actual_lambda_ge_323_over_5000
  linarith

end
end ImbalancedChen.Part5OriginalH430D5FirstAffinePositive
