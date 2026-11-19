import ImbalancedChen.Part5OriginalH430ThreeSingletonRationalLower
import ImbalancedChen.P2EnhancedSeedPairD8PieceSum

/-!
P5.6/h34: first strictly positive rational certificate for the ORIGINAL D8
pair source.  The moving first affine support interval is NOT discarded:
its nonnegativity is proved from the literal support geometry.  The second
affine interval gives a rational-log certificate on its entire true range.

No count-source licence, seed intercept, full lambda >= 13/100, or CLOSED-CELL
induction is assumed. SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430D8SecondAffineRationalLower

noncomputable section

open Set MeasureTheory
open scoped Interval
open Certificates
open P2EnhancedSeedPairD8Geometry
open P2EnhancedSeedActualFeedbackAssembly
open P2EnhancedSeedActualSevenLogIdentity

/-- The existing rational log checker supplies an exact (not floating)
logarithm lower bound at a convenient argument strictly below the true
D8 second-piece argument throughout its complete interval. -/
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

/-- Literal D8 logarithmic outer integrand is nonnegative on the WHOLE
unchanged interval, including the first moving affine support. -/
theorem actual_d8_outer_nonneg {u : ℝ} (hu : u ∈ Icc uLo uHi) :
    0 ≤ P2EnhancedSeedPairD8Integral.outerSlice u := by
  have hg := P2EnhancedSeedPairD8PieceSum.closed_slice_geometry hu
  have hden : 0 <
      P2EnhancedSeedPairD8Integral.lowerEndpoint u * (1 - u - vHi) :=
    mul_pos hg.2.2.1 hg.2.2.2.2.1
  have harg : (1 : ℝ) ≤
      vHi * (1 - u - P2EnhancedSeedPairD8Integral.lowerEndpoint u) /
      (P2EnhancedSeedPairD8Integral.lowerEndpoint u * (1 - u - vHi)) := by
    apply (le_div_iff₀ hden).mpr
    have hm := mul_nonneg
      (sub_nonneg.mpr hg.2.2.2.1.le) hg.2.1.le
    nlinarith only [hm]
  have hlog := Real.log_nonneg harg
  change 0 ≤ Real.log
    (vHi * (1 - u - P2EnhancedSeedPairD8Integral.lowerEndpoint u) /
      (P2EnhancedSeedPairD8Integral.lowerEndpoint u * (1 - u - vHi))) /
    (u * (1 - u))
  exact div_nonneg hlog (mul_pos hg.1 hg.2.1).le

/-- On the true second affine piece, the entire real logarithm is >=
log(6/5); the denominator is at most 1/4. No false constant-bound
assumption about the source has been inserted. -/
theorem actual_d8_second_slice_ge_18_over_25
    {u : ℝ} (hu : u ∈ Icc cut uHi) :
    (18 / 25 : ℝ) ≤ P2EnhancedSeedPairD8Integral.secondSlice u := by
  have huFull : u ∈ Icc uLo uHi :=
    ⟨literal_geometry.1.le.trans hu.1, hu.2⟩
  have hg := P2EnhancedSeedPairD8PieceSum.closed_slice_geometry huFull
  have hden : 0 < vLo * (1 - u - vHi) :=
    mul_pos literal_geometry.2.2.1 hg.2.2.2.2.1
  have harg : (6 / 5 : ℝ) ≤
      vHi * (1 - u - vLo) / (vLo * (1 - u - vHi)) := by
    apply (le_div_iff₀ hden).mpr
    dsimp [vHi, vLo, uHi] at *
    nlinarith only [hu.2]
  have hlog : (9 / 50 : ℝ) ≤
      Real.log (vHi * (1 - u - vLo) / (vLo * (1 - u - vHi))) :=
    rational_log_six_fifths.trans
      (Real.log_le_log (by norm_num : (0 : ℝ) < 6 / 5) harg)
  have hpos : 0 < u * (1 - u) := mul_pos hg.1 hg.2.1
  have hquarter : u * (1 - u) ≤ (1 / 4 : ℝ) := by
    nlinarith [sq_nonneg (u - 1 / 2)]
  change (18 / 25 : ℝ) ≤
    Real.log (vHi * (1 - u - vLo) / (vLo * (1 - u - vHi))) /
      (u * (1 - u))
  apply (le_div_iff₀ hpos).mpr
  nlinarith only [hlog, hquarter]

/-- A positive source from the ORIGINAL second D8 affine interval.
The exact lower endpoint is 1265/5648, not an enlarged rectangle. -/
theorem actual_d8_second_integral_ge_1_over_25 :
    (1 / 25 : ℝ) ≤
      ∫ u in Ioo cut uHi, P2EnhancedSeedPairD8Integral.secondSlice u := by
  have hsubset : Icc cut uHi ⊆ Icc uLo uHi :=
    fun _ hu => ⟨literal_geometry.1.le.trans hu.1, hu.2⟩
  have hcont := P2EnhancedSeedPairD8PieceSum.continuousOn_outerSlice.mono hsubset
  have hint : IntervalIntegrable P2EnhancedSeedPairD8Integral.outerSlice
      volume cut uHi :=
    hcont.intervalIntegrable_of_Icc literal_geometry.2.1.le
  have hmono := intervalIntegral.integral_mono_on
    literal_geometry.2.1.le intervalIntegrable_const hint
    (fun u hu => by
      rw [(P2EnhancedSeedPairD8Integral.second_affine_piece hu).2]
      exact actual_d8_second_slice_ge_18_over_25 hu)
  have hval : (uHi - cut) * (18 / 25 : ℝ) ≤
      ∫ u in cut..uHi, P2EnhancedSeedPairD8Integral.outerSlice u := by
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hmono
  have hsame :
      (∫ u in Ioo cut uHi, P2EnhancedSeedPairD8Integral.secondSlice u) =
      ∫ u in cut..uHi, P2EnhancedSeedPairD8Integral.outerSlice u := by
    calc
      _ = ∫ u in Ioo cut uHi, P2EnhancedSeedPairD8Integral.outerSlice u := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro u hu
        exact (P2EnhancedSeedPairD8Integral.second_affine_piece
          ⟨hu.1.le, hu.2.le⟩).2.symm
      _ = _ := by
        rw [integral_Ioo_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le literal_geometry.2.1.le]
  have hwidth : (1 / 25 : ℝ) ≤ (uHi - cut) * (18 / 25 : ℝ) := by
    norm_num [uHi, cut]
  rw [hsame]
  exact hwidth.trans hval

/-- The first support piece is present and nonnegative, so the second
piece's strict rational mass pays part of the actual full D8 coefficient. -/
theorem actual_d8Logs_ge_1_over_25 :
    (1 / 25 : ℝ) ≤ d8Logs := by
  have hfirst : 0 ≤
      ∫ u in Ioc uLo cut, P2EnhancedSeedPairD8Integral.firstSlice u := by
    apply MeasureTheory.setIntegral_nonneg
    intro u hu
    rw [← (P2EnhancedSeedPairD8Integral.first_affine_piece
      ⟨hu.1.le, hu.2⟩).2]
    exact actual_d8_outer_nonneg
      ⟨hu.1.le, hu.2.trans literal_geometry.2.1.le⟩
  have hsecond := actual_d8_second_integral_ge_1_over_25
  unfold d8Logs
  linarith

/-- Four independently bounded genuine terms (3 singleton + D6 + D8).
D5 and D7 remain only nonnegative; the 0.13 total remains UNPROVED. -/
theorem actual_lambda_ge_241_over_5000 :
    (241 / 5000 : ℝ) ≤ lambda := by
  have hs0 :=
    Part5OriginalH430ThreeSingletonRationalLower.original_singleton_zero_ge_57_per_1000
  have hs1 :=
    Part5OriginalH430ThreeSingletonRationalLower.original_singleton_one_ge_1_per_200
  have hs2 :=
    Part5OriginalH430ThreeSingletonRationalLower.original_singleton_two_ge_29_per_1000
  have hd6 :=
    Part5OriginalH430ActualD6BisectedRational.actual_d6Log_ge_11_over_100
  have hd8 := actual_d8Logs_ge_1_over_25
  obtain ⟨hd5, hd7, _⟩ :=
    Part5OriginalH430ActualD6RationalLower.other_pair_log_terms_nonneg
  rw [lambda_exact_seven_logs]
  linarith

theorem actual_feedback_one_fiftieth_ge_241_over_250000 :
    (241 / 250000 : ℝ) ≤ actualFeedback (1 / 50) := by
  rw [actualFeedback_one_fiftieth]
  have h := actual_lambda_ge_241_over_5000
  linarith

end
end ImbalancedChen.Part5OriginalH430D8SecondAffineRationalLower
