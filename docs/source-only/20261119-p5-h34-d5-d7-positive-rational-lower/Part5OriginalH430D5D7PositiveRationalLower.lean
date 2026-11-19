import ImbalancedChen.Part5OriginalH430D8SecondAffineRationalLower
import ImbalancedChen.P2EnhancedSeedD5PlusLogFubini
import ImbalancedChen.P2EnhancedSeedPairD7AffinePieces

/-!
P5.6/h34: NEW strictly positive, manuscript-internal rational contributions
from two previously unquantified ORIGINAL W2 pair supports: D5+ and D7.
All remaining portions of both real integration domains are explicitly
shown nonnegative, not dropped as empty or substituted by rectangles.

The actual seven-source lambda is not assumed; the final lower bound is
only partial. SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430D5D7PositiveRationalLower

noncomputable section

open Set MeasureTheory
open scoped Interval
open Certificates
open P2EnhancedSeedActualSevenLogIdentity
open P2EnhancedSeedActualFeedbackAssembly

/-- Mathlib-backed *rational* odd-logarithm series, not a floating
approximation or a declaration of the target real logarithm as a premise. -/
private theorem rational_log_five_fourths :
    (11 / 50 : ℝ) ≤ Real.log (5 / 4 : ℝ) := by
  let c : RationalLogCertificate :=
    ⟨(5 / 4 : ℚ), 2, logSeriesLower (5 / 4) 2,
      logSeriesUpper (5 / 4) 2⟩
  have hc : c.check = true := by
    simpa only [RationalLogCertificate.check, decide_eq_true_eq] using
      (show c.Valid from ⟨by norm_num, le_rfl, le_rfl⟩)
  have h := (RationalLogCertificate.check_sound c hc).1
  have hn : (11 / 50 : ℝ) ≤
      (logSeriesLower (5 / 4 : ℚ) 2 : ℝ) := by
    norm_num [logSeriesLower, logParameter, Finset.sum_range_succ]
  exact hn.trans (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h)

private theorem rational_log_six_fifths :
    (9 / 50 : ℝ) ≤ Real.log (6 / 5 : ℝ) := by
  let c : RationalLogCertificate :=
    ⟨(6 / 5 : ℚ), 2, logSeriesLower (6 / 5) 2,
      logSeriesUpper (6 / 5) 2⟩
  have hc : c.check = true := by
    simpa only [RationalLogCertificate.check, decide_eq_true_eq] using
      (show c.Valid from ⟨by norm_num, le_rfl, le_rfl⟩)
  have h := (RationalLogCertificate.check_sound c hc).1
  have hn : (9 / 50 : ℝ) ≤
      (logSeriesLower (6 / 5 : ℚ) 2 : ℝ) := by
    norm_num [logSeriesLower, logParameter, Finset.sum_range_succ]
  exact hn.trans (by simpa only [Rat.cast_div, Rat.cast_ofNat] using h)

section D5

open P2EnhancedSeedD5PlusGeometry
open P2EnhancedSeedD5PlusLogFubini
open P2EnhancedSeedSingletonPrimitive (a0)

/-- The original max/min D5 support, including its first and third
affine pieces, has a nonnegative outer logarithmic integrand. -/
theorem actual_d5_outer_nonneg {u : ℝ} (hu : u ∈ Icc a0 top) :
    0 ≤ outerSlice u := by
  have hg := slice_geometry hu
  have hden : 0 < lower u * (1-u-upper u) :=
    mul_pos hg.2.1 (by linarith only [hg.2.2.2])
  have harg : (1 : ℝ) ≤
      upper u * (1-u-lower u) / (lower u * (1-u-upper u)) := by
    apply (le_div_iff₀ hden).mpr
    have hm : 0 ≤ (upper u-lower u)*(1-u) :=
      mul_nonneg (sub_nonneg.mpr hg.2.2.1)
        (by linarith only [hg.2.2.2])
    nlinarith only [hm]
  have hpos : 0 < u * (1-u) :=
    mul_pos hg.1 (by linarith only [hg.2.2.2])
  change 0 ≤ Real.log
    (upper u*(1-u-lower u)/(lower u*(1-u-upper u)))/(u*(1-u))
  exact div_nonneg (Real.log_nonneg harg) hpos.le

/-- A genuine subinterval of the SECOND D5 affine slice: cutOne <= u <=
3/10, lower=u and upper=10/29. The argument is uniformly >= 5/4. -/
theorem actual_d5_second_argument_ge_five_fourths
    {u : ℝ} (hu : u ∈ Icc cutOne (3/10 : ℝ)) :
    (5/4 : ℝ) ≤ cap*(1-2*u)/(u*(1-u-cap)) := by
  have hcut : (3/10 : ℝ) ≤ cutTwo := by norm_num [cutTwo]
  have hm : u ∈ Icc cutOne cutTwo := ⟨hu.1,hu.2.trans hcut⟩
  have ha := second_affine hm
  have hgeom : u ∈ Icc a0 top := by
    constructor
    · exact (le_of_lt three_cut_order.1).trans hu.1
    · exact hu.2.trans (by norm_num [top])
  have hg := slice_geometry hgeom
  have hden : 0 < u*(1-u-cap) := by
    have hr : cap < 1-u := by
      simpa only [ha.2] using hg.2.2.2
    exact mul_pos hg.1 (by linarith only [hr])
  have hA : 0 ≤ (3/10 : ℝ)-u := sub_nonneg.mpr hu.2
  have hB : 0 ≤ (7/10 : ℝ)-cap-u := by
    dsimp [cap]
    linarith only [hu.2]
  have hprod : 0 ≤ ((3/10 : ℝ)-u)*((7/10 : ℝ)-cap-u) :=
    mul_nonneg hA hB
  have hdenBound : u*(1-u-cap) ≤ (3/10 : ℝ)*(7/10-cap) := by
    nlinarith only [hprod]
  have hnumBound : cap*(2/5 : ℝ) ≤ cap*(1-2*u) := by
    dsimp [cap]
    linarith only [hu.2]
  have hconst : (5/4 : ℝ)*((3/10 : ℝ)*(7/10-cap)) ≤
      cap*(2/5 : ℝ) := by norm_num [cap]
  apply (le_div_iff₀ hden).mpr
  nlinarith only [hdenBound,hnumBound,hconst]

theorem actual_d5_second_slice_ge_22_over_25
    {u : ℝ} (hu : u ∈ Icc cutOne (3/10 : ℝ)) :
    (22/25 : ℝ) ≤ logSlice u u cap := by
  have hcut : (3/10 : ℝ) ≤ cutTwo := by norm_num [cutTwo]
  have hm : u ∈ Icc cutOne cutTwo := ⟨hu.1,hu.2.trans hcut⟩
  have hgeom : u ∈ Icc a0 top :=
    ⟨(le_of_lt three_cut_order.1).trans hu.1,
      hu.2.trans (by norm_num [top])⟩
  have hg := slice_geometry hgeom
  have hpos : 0 < u*(1-u) :=
    mul_pos hg.1 (by linarith only [hg.2.2.2])
  have hlog : (11/50 : ℝ) ≤
      Real.log (cap*(1-2*u)/(u*(1-u-cap))) :=
    rational_log_five_fourths.trans
      (Real.log_le_log (by norm_num : (0 : ℝ)<5/4)
        (actual_d5_second_argument_ge_five_fourths hu))
  have hquarter : u*(1-u) ≤ (1/4 : ℝ) := by
    nlinarith [sq_nonneg (u-1/2)]
  unfold logSlice
  apply (le_div_iff₀ hpos).mpr
  nlinarith only [hlog,hquarter]

/-- This bound uses an actual, interior D5 interval with length
3/10 - 117/454. Its exact Darboux contribution exceeds 37/1000. -/
theorem actual_d5_middle_interval_ge_37_per_1000 :
    (37/1000 : ℝ) ≤
      ∫ u in cutOne..(3/10 : ℝ), outerSlice u := by
  have ha : a0 ≤ cutOne := le_of_lt three_cut_order.1
  have hb : cutOne ≤ (3/10 : ℝ) := by norm_num [cutOne]
  have hc : (3/10 : ℝ) ≤ top := by norm_num [top]
  have hi := intervalIntegrable_outerSlice ha hb hc
  have hmono := intervalIntegral.integral_mono_on hb
    intervalIntegrable_const hi (fun u hu => by
      have ht : u ∈ Icc cutOne cutTwo :=
        ⟨hu.1,hu.2.trans (by norm_num [cutTwo])⟩
      have hh := second_affine ht
      change (22/25 : ℝ) ≤ logSlice u (lower u) (upper u)
      rw [hh.1,hh.2]
      exact actual_d5_second_slice_ge_22_over_25 hu)
  have hval : ((3/10 : ℝ)-cutOne)*(22/25 : ℝ) ≤
      ∫ u in cutOne..(3/10 : ℝ),outerSlice u := by
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hmono
  have hwidth : (37/1000 : ℝ) ≤
      ((3/10 : ℝ)-cutOne)*(22/25 : ℝ) := by norm_num [cutOne]
  exact hwidth.trans hval

/-- The existing true D5 Fubini and exact three-affine identities,
rather than a newly assumed equality, identify the entire coefficient
with one outer interval integral. -/
theorem actual_d5Logs_eq_outer :
    d5Logs = ∫ u in a0..top,outerSlice u := by
  have hthree := feedback_three_affine_logs (1 : ℝ)
  have houter := feedback_outer_log (1 : ℝ)
  have heq : (∫ u in Ioo a0 top,outerSlice u) = d5Logs := by
    unfold d5Logs
    calc
      _ = ∫ x in D5plus,feedback 1 x := by
        simpa only [one_mul] using houter.symm
      _ = _ := by simpa only [one_mul] using hthree
  have horder : a0 ≤ top :=
    (le_of_lt three_cut_order.1).trans
      ((le_of_lt three_cut_order.2.1).trans
        (le_of_lt three_cut_order.2.2))
  rw [integral_Ioo_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le horder] at heq
  exact heq.symm

/-- First and third affine support pieces are not discarded: their
nonnegative outer contributions complete the actual D5 bound. -/
theorem actual_d5Logs_ge_37_per_1000 :
    (37/1000 : ℝ) ≤ d5Logs := by
  have ha : a0 ≤ cutOne := le_of_lt three_cut_order.1
  have hb : cutOne ≤ (3/10 : ℝ) := by norm_num [cutOne]
  have hc : (3/10 : ℝ) ≤ top := by norm_num [top]
  have hstart : a0 ≤ top := ha.trans (hb.trans hc)
  have hI₁ := intervalIntegrable_outerSlice (le_refl a0) ha (ha.trans (hb.trans hc))
  have hI₂ := intervalIntegrable_outerSlice ha hb hc
  have hI₃ := intervalIntegrable_outerSlice (ha.trans hb) hc (le_refl top)
  have hI₁₂ := intervalIntegrable_outerSlice (le_refl a0)
    (ha.trans hb) hc
  have hL : 0 ≤ ∫ u in a0..cutOne,outerSlice u := by
    have h := intervalIntegral.integral_mono_on ha
      intervalIntegrable_const hI₁
      (fun u hu => actual_d5_outer_nonneg
        ⟨hu.1,hu.2.trans (hb.trans hc)⟩)
    simpa only [intervalIntegral.integral_const,smul_zero] using h
  have hR : 0 ≤ ∫ u in (3/10 : ℝ)..top,outerSlice u := by
    have h := intervalIntegral.integral_mono_on hc
      intervalIntegrable_const hI₃
      (fun u hu => actual_d5_outer_nonneg
        ⟨(ha.trans hb).trans hu.1,hu.2⟩)
    simpa only [intervalIntegral.integral_const,smul_zero] using h
  have hM := actual_d5_middle_interval_ge_37_per_1000
  have hSplit₁ := intervalIntegral.integral_add_adjacent_intervals hI₁ hI₂
  have hSplit₂ := intervalIntegral.integral_add_adjacent_intervals hI₁₂ hI₃
  rw [actual_d5Logs_eq_outer]
  linarith only [hL,hR,hM,hSplit₁,hSplit₂]

end D5

section D7

open P2EnhancedSeedPairD7Domain
open P2EnhancedSeedPairD7Integral

/-- Original D7 moving max endpoint and the entire original interval,
including the pre-junction support wall, give a nonnegative integrand. -/
theorem actual_d7_outer_nonneg {u : ℝ}
    (hu : u ∈ Icc supportStart uHi) :
    0 ≤ outerSlice u := by
  have hg := endpoint_geometry hu
  have hden : 0 < lowerEndpoint u*(1-u-uHi) :=
    mul_pos hg.2.1 (by linarith only [hg.2.2.2])
  have harg : (1 : ℝ) ≤ logArgument u := by
    unfold logArgument
    apply (le_div_iff₀ hden).mpr
    have hm : 0 ≤ (uHi-lowerEndpoint u)*(1-u) :=
      mul_nonneg (sub_nonneg.mpr hg.2.2.1)
        (by linarith only [hg.2.2.2])
    nlinarith only [hm]
  have hpos : 0 < u*(1-u) :=
    mul_pos hg.1 (by linarith only [hg.2.2.2])
  unfold outerSlice
  exact div_nonneg (Real.log_nonneg harg) hpos.le

/-- On the literal D7 SECOND affine support, keep only the actual
subinterval [5/21,1/4]; the correct moving lower endpoint is exactly u. -/
theorem actual_d7_second_argument_ge_six_fifths
    {u : ℝ} (hu : u ∈ Icc boundaryCut (1/4 : ℝ)) :
    (6/5 : ℝ) ≤ logArgument u := by
  have hstart : supportStart ≤ boundaryCut :=
    by norm_num [supportStart,boundaryCut]
  have hend : (1/4 : ℝ) ≤ uHi := by norm_num [uHi]
  have hg := endpoint_geometry
    (show u ∈ Icc supportStart uHi from
      ⟨hstart.trans hu.1,hu.2.trans hend⟩)
  have hlow := lowerEndpoint_second hu.1
  have hden : 0 < u*(1-u-uHi) :=
    mul_pos hg.1 (by linarith only [hg.2.2.2])
  have hA : 0 ≤ (1/4 : ℝ)-u := sub_nonneg.mpr hu.2
  have hB : 0 ≤ (3/4 : ℝ)-uHi-u := by
    dsimp [uHi]
    linarith only [hu.2]
  have hproduct : 0 ≤ ((1/4 : ℝ)-u)*((3/4 : ℝ)-uHi-u) :=
    mul_nonneg hA hB
  have hdenBound : u*(1-u-uHi) ≤ (1/4 : ℝ)*(3/4-uHi) := by
    nlinarith only [hproduct]
  have hnumBound : uHi*(1/2 : ℝ) ≤ uHi*(1-2*u) := by
    dsimp [uHi]
    linarith only [hu.2]
  have hconstant : (6/5 : ℝ)*((1/4 : ℝ)*(3/4-uHi)) ≤
      uHi*(1/2 : ℝ) := by norm_num [uHi]
  unfold logArgument
  rw [hlow]
  apply (le_div_iff₀ hden).mpr
  nlinarith only [hdenBound,hnumBound,hconstant]

theorem actual_d7_second_slice_ge_18_over_25
    {u : ℝ} (hu : u ∈ Icc boundaryCut (1/4 : ℝ)) :
    (18/25 : ℝ) ≤ outerSlice u := by
  have hstart : supportStart ≤ boundaryCut :=
    by norm_num [supportStart,boundaryCut]
  have hend : (1/4 : ℝ) ≤ uHi := by norm_num [uHi]
  have hg := endpoint_geometry
    (show u ∈ Icc supportStart uHi from
      ⟨hstart.trans hu.1,hu.2.trans hend⟩)
  have hpos : 0 < u*(1-u) :=
    mul_pos hg.1 (by linarith only [hg.2.2.2])
  have hlog : (9/50 : ℝ) ≤ Real.log (logArgument u) :=
    rational_log_six_fifths.trans
      (Real.log_le_log (by norm_num : (0 : ℝ)<6/5)
        (actual_d7_second_argument_ge_six_fifths hu))
  have hquarter : u*(1-u) ≤ (1/4 : ℝ) := by
    nlinarith [sq_nonneg (u-1/2)]
  unfold outerSlice
  apply (le_div_iff₀ hpos).mpr
  nlinarith only [hlog,hquarter]

theorem actual_d7_middle_interval_ge_1_per_125 :
    (1/125 : ℝ) ≤
      ∫ u in boundaryCut..(1/4 : ℝ),outerSlice u := by
  have hstart : supportStart ≤ boundaryCut :=
    by norm_num [supportStart,boundaryCut]
  have hmid : boundaryCut ≤ (1/4 : ℝ) :=
    by norm_num [boundaryCut]
  have hend : (1/4 : ℝ) ≤ uHi := by norm_num [uHi]
  have hcont := continuousOn_outerSlice.mono
    (show Icc boundaryCut (1/4 : ℝ) ⊆ Icc supportStart uHi from
      fun u hu => ⟨hstart.trans hu.1,hu.2.trans hend⟩)
  have hint : IntervalIntegrable outerSlice volume boundaryCut (1/4 : ℝ) :=
    hcont.intervalIntegrable_of_Icc hmid
  have hmono := intervalIntegral.integral_mono_on hmid
    intervalIntegrable_const hint
    (fun u hu => actual_d7_second_slice_ge_18_over_25 hu)
  have hval : ((1/4 : ℝ)-boundaryCut)*(18/25 : ℝ) ≤
      ∫ u in boundaryCut..(1/4 : ℝ),outerSlice u := by
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hmono
  have hwidth : (1/125 : ℝ) ≤
      ((1/4 : ℝ)-boundaryCut)*(18/25 : ℝ) := by
    norm_num [boundaryCut]
  exact hwidth.trans hval

/-- D7 first affine interval and the omitted tail of its second affine
interval contribute nonnegative mass. The full original domain remains. -/
theorem actual_d7Log_ge_1_per_125 :
    (1/125 : ℝ) ≤ d7Log := by
  have ha : supportStart ≤ boundaryCut :=
    by norm_num [supportStart,boundaryCut]
  have hb : boundaryCut ≤ (1/4 : ℝ) :=
    by norm_num [boundaryCut]
  have hc : (1/4 : ℝ) ≤ uHi := by norm_num [uHi]
  have hI₁ := P2EnhancedSeedPairD7AffinePieces.first_intervalIntegrable
  have hI₂ : IntervalIntegrable outerSlice volume boundaryCut (1/4 : ℝ) :=
    (continuousOn_outerSlice.mono
      (show Icc boundaryCut (1/4 : ℝ) ⊆ Icc supportStart uHi from
        fun u hu => ⟨ha.trans hu.1,hu.2.trans hc⟩)).intervalIntegrable_of_Icc hb
  have hI₃ : IntervalIntegrable outerSlice volume (1/4 : ℝ) uHi :=
    (continuousOn_outerSlice.mono
      (show Icc (1/4 : ℝ) uHi ⊆ Icc supportStart uHi from
        fun u hu => ⟨(ha.trans hb).trans hu.1,hu.2⟩)).intervalIntegrable_of_Icc hc
  have hI₁₂ : IntervalIntegrable outerSlice volume supportStart (1/4 : ℝ) :=
    (continuousOn_outerSlice.mono
      (show Icc supportStart (1/4 : ℝ) ⊆ Icc supportStart uHi from
        fun u hu => ⟨hu.1,hu.2.trans hc⟩)).intervalIntegrable_of_Icc (ha.trans hb)
  have hL : 0 ≤ ∫ u in supportStart..boundaryCut,outerSlice u := by
    have h := intervalIntegral.integral_mono_on ha
      intervalIntegrable_const hI₁
      (fun u hu => actual_d7_outer_nonneg ⟨hu.1,hu.2.trans (hb.trans hc)⟩)
    simpa only [intervalIntegral.integral_const,smul_zero] using h
  have hR : 0 ≤ ∫ u in (1/4 : ℝ)..uHi,outerSlice u := by
    have h := intervalIntegral.integral_mono_on hc
      intervalIntegrable_const hI₃
      (fun u hu => actual_d7_outer_nonneg
        ⟨(ha.trans hb).trans hu.1,hu.2⟩)
    simpa only [intervalIntegral.integral_const,smul_zero] using h
  have hM := actual_d7_middle_interval_ge_1_per_125
  have hSplit₁ := intervalIntegral.integral_add_adjacent_intervals hI₁ hI₂
  have hSplit₂ := intervalIntegral.integral_add_adjacent_intervals hI₁₂ hI₃
  have hFull : (∫ u in supportStart..uHi,outerSlice u)=d7Log := by
    unfold d7Log
    rw [integral_Ioo_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (ha.trans (hb.trans hc))]
    rfl
  rw [← hFull]
  linarith only [hL,hR,hM,hSplit₁,hSplit₂]

end D7

/-- Combined ACTUAL seven-piece feedback: earlier three singleton
certificates and D6/D8, plus newly positive D5 and D7. Only a partial
coefficient (143/2500 < 13/100); no synthetic count or seed licence. -/
theorem actual_lambda_ge_143_over_2500 :
    (143/2500 : ℝ) ≤ lambda := by
  have hs0 :=
    Part5OriginalH430ThreeSingletonRationalLower.original_singleton_zero_ge_57_per_1000
  have hs1 :=
    Part5OriginalH430ThreeSingletonRationalLower.original_singleton_one_ge_1_per_200
  have hs2 :=
    Part5OriginalH430ThreeSingletonRationalLower.original_singleton_two_ge_29_per_1000
  have hd5 := actual_d5Logs_ge_37_per_1000
  have hd6 := Part5OriginalH430ActualD6BisectedRational.actual_d6Log_ge_11_over_100
  have hd7 := actual_d7Log_ge_1_per_125
  have hd8 :=
    Part5OriginalH430D8SecondAffineRationalLower.actual_d8Logs_ge_1_over_25
  rw [lambda_exact_seven_logs]
  linarith

theorem actual_feedback_one_fiftieth_ge_143_over_125000 :
    (143/125000 : ℝ) ≤ actualFeedback (1/50) := by
  rw [actualFeedback_one_fiftieth]
  have h := actual_lambda_ge_143_over_2500
  linarith

end
end ImbalancedChen.Part5OriginalH430D5D7PositiveRationalLower
