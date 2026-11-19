import ImbalancedChen.Part5OriginalH430ThreeSingletonFourCell

/-!
P5.6 / h34. Genuine four-cell rational lower bound for the WHOLE
SECOND affine piece of original D8. The first moving affine piece stays
in the actual source through its established nonnegativity proof.

This is manuscript-internal candidate Lean source. No count-source
licence, PP/same-rho hypothesis, h34 closure, or external analytic
statement has been introduced. Original seven-source /5 unchanged.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430D8SecondFourCell
noncomputable section

open Set MeasureTheory Certificates
open scoped Interval
open P2EnhancedSeedPairD8Geometry
open P2EnhancedSeedPairD8Integral
open P2EnhancedSeedActualSevenLogIdentity
open P2EnhancedSeedActualFeedbackAssembly

/-- Exact rational lower mass for one true D8 second-affine cell.
The logarithm is evaluated at the left edge; u(1-u) at the right. -/
def cellMass (l r q : ℚ) : ℚ :=
  (r-l) * logSeriesLower q 2 / (r*(1-r))

private theorem rational_log_floor (q : ℚ) (hq : 1 ≤ q) :
    (logSeriesLower q 2 : ℝ) ≤ Real.log (q : ℝ) := by
  let c : RationalLogCertificate :=
    ⟨q, 2, logSeriesLower q 2, logSeriesUpper q 2⟩
  have hc : c.check = true := by
    simpa only [RationalLogCertificate.check, decide_eq_true_eq] using
      (show c.Valid from ⟨hq, le_rfl, le_rfl⟩)
  exact (RationalLogCertificate.check_sound c hc).1

/-- On the literal second affine D8 interval the true logarithm
argument is increasing: its positive cross-product difference is
(vHi-vLo)*(u-l). No rectangular or constant-profile replacement. -/
private theorem second_argument_mono (l u : ℝ)
    (hl : cut ≤ l) (hlu : l ≤ u) (hu : u ≤ uHi) :
    vHi*(1-l-vLo)/(vLo*(1-l-vHi)) ≤
      vHi*(1-u-vLo)/(vLo*(1-u-vHi)) := by
  have hL : l ∈ Icc uLo uHi :=
    ⟨literal_geometry.1.le.trans hl,hlu.trans hu⟩
  have hU : u ∈ Icc uLo uHi :=
    ⟨hL.1.trans hlu,hu⟩
  have gL := P2EnhancedSeedPairD8PieceSum.closed_slice_geometry hL
  have gU := P2EnhancedSeedPairD8PieceSum.closed_slice_geometry hU
  have hvLo : 0 ≤ vLo := literal_geometry.2.2.1.le
  have hvHi : 0 ≤ vHi :=
    (literal_geometry.2.2.1.trans literal_geometry.2.2.2.1).le
  have hDenL : 0 < vLo*(1-l-vHi) :=
    mul_pos literal_geometry.2.2.1 gL.2.2.2.2.1
  have hDenU : 0 < vLo*(1-u-vHi) :=
    mul_pos literal_geometry.2.2.1 gU.2.2.2.2.1
  have hFactor : 0 ≤ (vHi-vLo)*(u-l) :=
    mul_nonneg (sub_nonneg.mpr literal_geometry.2.2.2.1.le)
      (sub_nonneg.mpr hlu)
  have hCross :
      (1-l-vLo)*(1-u-vHi) ≤ (1-u-vLo)*(1-l-vHi) := by
    nlinarith only [hFactor]
  have hScaled := mul_le_mul_of_nonneg_left hCross
    (mul_nonneg hvLo hvHi)
  apply (div_le_div_iff₀ hDenL hDenU).mpr
  nlinarith only [hScaled]

private theorem interval_integrable (l r : ℝ)
    (hl : uLo ≤ l) (hlr : l ≤ r) (hr : r ≤ uHi) :
    IntervalIntegrable outerSlice volume l r := by
  have hcont := P2EnhancedSeedPairD8PieceSum.continuousOn_outerSlice.mono
    (show Icc l r ⊆ Icc uLo uHi from
      fun _ hu => ⟨hl.trans hu.1,hu.2.trans hr⟩)
  exact hcont.intervalIntegrable_of_Icc hlr

/-- Actual D8 second-affine rational Darboux cell, not a hypothesis
that a putative approximation is below the true logarithmic integral. -/
private theorem second_cell (l r q : ℚ)
    (hl : cut ≤ (l : ℝ)) (hlr : l ≤ r)
    (hr : (r : ℝ) ≤ uHi) (hq : 1 ≤ q)
    (hs : 0 ≤ logSeriesLower q 2)
    (hqv : (q : ℝ) =
      vHi*(1-(l : ℝ)-vLo)/(vLo*(1-(l : ℝ)-vHi))) :
    (cellMass l r q : ℝ) ≤
      ∫ u in (l : ℝ)..(r : ℝ), outerSlice u := by
  have hlrR : (l : ℝ) ≤ (r : ℝ) := by exact_mod_cast hlr
  have hLo : uLo ≤ (l : ℝ) := literal_geometry.1.le.trans hl
  have hInt := interval_integrable (l : ℝ) (r : ℝ) hLo hlrR hr
  have hFloor : ∀ u ∈ Icc (l : ℝ) (r : ℝ),
      (logSeriesLower q 2 : ℝ)/
        ((r : ℝ)*(1-(r : ℝ))) ≤ outerSlice u := by
    intro u hu
    have hFull : u ∈ Icc uLo uHi :=
      ⟨hLo.trans hu.1,hu.2.trans hr⟩
    have hg := P2EnhancedSeedPairD8PieceSum.closed_slice_geometry hFull
    have hUR : 0 < u*(1-u) := mul_pos hg.1 hg.2.1
    have hRFull : (r : ℝ) ∈ Icc uLo uHi :=
      ⟨hLo.trans hlrR,hr⟩
    have hgR := P2EnhancedSeedPairD8PieceSum.closed_slice_geometry hRFull
    have hRR : 0 < (r : ℝ)*(1-(r : ℝ)) :=
      mul_pos hgR.1 hgR.2.1
    have hHalf : 2*uHi ≤ 1 := by norm_num [uHi]
    have hDelta : 0 ≤ 1-(r : ℝ)-u := by
      linarith only [hHalf,hr,hu.2]
    have hProd : 0 ≤ ((r : ℝ)-u)*(1-(r : ℝ)-u) :=
      mul_nonneg (sub_nonneg.mpr hu.2) hDelta
    have hDenBound : u*(1-u) ≤ (r : ℝ)*(1-(r : ℝ)) := by
      nlinarith only [hProd]
    have hArg : (q : ℝ) ≤
        vHi*(1-u-vLo)/(vLo*(1-u-vHi)) := by
      rw [hqv]
      exact second_argument_mono (l : ℝ) u hl hu.1
        (hu.2.trans hr)
    have hqPositive : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) hq)
    have hLog : (logSeriesLower q 2 : ℝ) ≤
        Real.log (vHi*(1-u-vLo)/(vLo*(1-u-vHi))) :=
      (rational_log_floor q hq).trans
        (Real.log_le_log hqPositive hArg)
    have hSeries : (0 : ℝ) ≤ (logSeriesLower q 2 : ℝ) := by
      exact_mod_cast hs
    rw [(second_affine_piece
      (show u ∈ Icc cut uHi from ⟨hl.trans hu.1,hu.2.trans hr⟩)).2]
    change (logSeriesLower q 2 : ℝ) /
      ((r : ℝ)*(1-(r : ℝ))) ≤
      Real.log (vHi*(1-u-vLo)/(vLo*(1-u-vHi)))/(u*(1-u))
    apply (div_le_div_iff₀ hRR hUR).mpr
    exact (mul_le_mul_of_nonneg_left hDenBound hSeries).trans
      (mul_le_mul_of_nonneg_right hLog hRR.le)
  have hMono := intervalIntegral.integral_mono_on hlrR
    intervalIntegrable_const hInt hFloor
  have hVal :
      ((r : ℝ)-(l : ℝ)) *
        (logSeriesLower q 2 : ℝ)/((r : ℝ)*(1-(r : ℝ))) ≤
          ∫ u in (l : ℝ)..(r : ℝ), outerSlice u := by
    convert hMono using 1 <;>
      simp only [intervalIntegral.integral_const,smul_eq_mul]
    ring
  have hCast :
      (cellMass l r q : ℝ) =
        ((r : ℝ)-(l : ℝ)) *
        (logSeriesLower q 2 : ℝ)/((r : ℝ)*(1-(r : ℝ))) := by
    simp only [cellMass,Rat.cast_div,Rat.cast_mul,Rat.cast_sub,Rat.cast_one]
  exact hCast.le.trans hVal

/-- Four cells cover every point of the true D8 SECOND affine source,
from cut=1265/5648 to uHi=100/353; the first source is nonnegative.
The independent exact rational Darboux sum is > 0.103239. -/
theorem genuine_d8_four_cell_ge_103_per_1000 :
    (103/1000 : ℝ) ≤ d8Logs := by
  let a : ℚ := 1265/5648
  let t₁ : ℚ := 1/4
  let t₂ : ℚ := 13/50
  let t₃ : ℚ := 27/100
  let b : ℚ := 100/353
  have h₁ := second_cell a t₁ (982399/706270)
    (by norm_num [a,cut]) (by norm_num [a,t₁])
    (by norm_num [t₁,uHi]) (by norm_num)
    (by norm_num [logSeriesLower,logParameter,Finset.sum_range_succ])
    (by norm_num [a,vHi,vLo])
  have h₂ := second_cell t₁ t₂ (659/470)
    (by norm_num [t₁,cut]) (by norm_num [t₁,t₂])
    (by norm_num [t₂,uHi]) (by norm_num)
    (by norm_num [logSeriesLower,logParameter,Finset.sum_range_succ])
    (by norm_num [t₁,vHi,vLo])
  have h₃ := second_cell t₂ t₃ (2687/1910)
    (by norm_num [t₂,cut]) (by norm_num [t₂,t₃])
    (by norm_num [t₃,uHi]) (by norm_num)
    (by norm_num [logSeriesLower,logParameter,Finset.sum_range_succ])
    (by norm_num [t₂,vHi,vLo])
  have h₄ := second_cell t₃ b (15769/11170)
    (by norm_num [t₃,cut]) (by norm_num [t₃,b])
    (by norm_num [b,uHi]) (by norm_num)
    (by norm_num [logSeriesLower,logParameter,Finset.sum_range_succ])
    (by norm_num [t₃,vHi,vLo])
  have hRat : (103/1000 : ℝ) ≤
      ((cellMass a t₁ (982399/706270) +
        cellMass t₁ t₂ (659/470) +
        cellMass t₂ t₃ (2687/1910) +
        cellMass t₃ b (15769/11170) : ℚ) : ℝ) := by
    norm_num [a,b,t₁,t₂,t₃,cellMass,
      logSeriesLower,logParameter,Finset.sum_range_succ]
  have hCast :
      (cellMass a t₁ (982399/706270) : ℝ) +
      (cellMass t₁ t₂ (659/470) : ℝ) +
      (cellMass t₂ t₃ (2687/1910) : ℝ) +
      (cellMass t₃ b (15769/11170) : ℝ) =
      ((cellMass a t₁ (982399/706270) +
        cellMass t₁ t₂ (659/470) +
        cellMass t₂ t₃ (2687/1910) +
        cellMass t₃ b (15769/11170) : ℚ) : ℝ) := by
    simp only [Rat.cast_add]
  have ha : cut ≤ (t₁ : ℝ) := by norm_num [cut,t₁]
  have hb : (t₁ : ℝ) ≤ (t₂ : ℝ) := by norm_num [t₁,t₂]
  have hc : (t₂ : ℝ) ≤ (t₃ : ℝ) := by norm_num [t₂,t₃]
  have hd : (t₃ : ℝ) ≤ uHi := by norm_num [t₃,uHi]
  have hI₁ := interval_integrable cut (t₁ : ℝ)
    literal_geometry.1.le
    ha (ha.trans (hb.trans (hc.trans hd)))
  have hI₂ := interval_integrable (t₁ : ℝ) (t₂ : ℝ)
    (literal_geometry.1.le.trans ha) hb (hb.trans (hc.trans hd))
  have hI₃ := interval_integrable (t₂ : ℝ) (t₃ : ℝ)
    (literal_geometry.1.le.trans (ha.trans hb)) hc (hc.trans hd)
  have hI₄ := interval_integrable (t₃ : ℝ) uHi
    (literal_geometry.1.le.trans (ha.trans (hb.trans hc))) hd (le_refl uHi)
  have hI₁₂ := interval_integrable cut (t₂ : ℝ)
    literal_geometry.1.le (ha.trans hb) (hb.trans (hc.trans hd))
  have hI₁₂₃ := interval_integrable cut (t₃ : ℝ)
    literal_geometry.1.le (ha.trans (hb.trans hc)) (hc.trans hd)
  have s₁₂ := intervalIntegral.integral_add_adjacent_intervals hI₁ hI₂
  have s₁₂₃ := intervalIntegral.integral_add_adjacent_intervals hI₁₂ hI₃
  have s₁₂₃₄ := intervalIntegral.integral_add_adjacent_intervals hI₁₂₃ hI₄
  have haEq : (a : ℝ) = cut := by norm_num [a,cut]
  have hbEq : (b : ℝ) = uHi := by norm_num [b,uHi]
  rw [haEq] at h₁
  rw [hbEq] at h₄
  have hSecond : (103/1000 : ℝ) ≤
      ∫ u in cut..uHi, outerSlice u := by
    linarith only [h₁,h₂,h₃,h₄,hRat,hCast,s₁₂,s₁₂₃,s₁₂₃₄]
  have hFirst : 0 ≤
      ∫ u in Ioc uLo cut, firstSlice u := by
    apply MeasureTheory.setIntegral_nonneg
    intro u hu
    rw [← (first_affine_piece ⟨hu.1.le,hu.2⟩).2]
    exact Part5OriginalH430D8SecondAffineRationalLower.actual_d8_outer_nonneg
      ⟨hu.1.le,hu.2.trans literal_geometry.2.1.le⟩
  have hSecondEq :
      (∫ u in Ioo cut uHi,secondSlice u) =
        ∫ u in cut..uHi,outerSlice u := by
    calc
      _ = ∫ u in Ioo cut uHi,outerSlice u := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro u hu
        exact (second_affine_piece ⟨hu.1.le,hu.2.le⟩).2.symm
      _ = _ := by
        rw [integral_Ioo_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le literal_geometry.2.1.le]
  unfold d8Logs
  rw [hSecondEq]
  linarith only [hFirst,hSecond]

/-- The seven *actual* source integrals, divided by the same original
5 exactly once. This is still strictly weaker than lambda >= 13/100. -/
theorem actual_lambda_ge_64_over_625 :
    (64/625 : ℝ) ≤ lambda := by
  have h0 :=
    Part5OriginalH430ThreeSingletonFourCell.original_singleton_zero_ge_89_per_1000
  have h1 :=
    Part5OriginalH430ThreeSingletonFourCell.original_singleton_one_ge_8_per_1000
  have h2 :=
    Part5OriginalH430ThreeSingletonFourCell.original_singleton_two_ge_45_per_1000
  have h5 :=
    Part5OriginalH430FourCellD5Darboux.genuine_four_cell_D5_ge_13_over_100
  have h6 :=
    Part5OriginalH430ActualD6BisectedRational.actual_d6Log_ge_11_over_100
  have h7 :=
    Part5OriginalH430D7EightCellRationalLower.genuine_d7_eight_cell_ge_27_per_1000
  have h8 := genuine_d8_four_cell_ge_103_per_1000
  rw [lambda_exact_seven_logs]
  linarith

end
end ImbalancedChen.Part5OriginalH430D8SecondFourCell
