import ImbalancedChen.Part5OriginalH430D5FirstAffinePositive

/-!
P5.6/h34. Four rational Darboux cells on the TRUE first and second
D5 affine support pieces. The third piece is retained as nonnegative.
No target/seed/count licence is assumed.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430FourCellD5Darboux
noncomputable section

open Set MeasureTheory Certificates
open scoped Interval
open P2EnhancedSeedSingletonPrimitive (a0)
open P2EnhancedSeedD5PlusGeometry
open P2EnhancedSeedD5PlusLogFubini
open P2EnhancedSeedActualSevenLogIdentity
open P2EnhancedSeedActualFeedbackAssembly

/-- Exact rational contribution from a cell, with the original 2-term
certified logarithm lower series and the exact endpoint u(1-u). -/
def cellMass (l r q : ℚ) : ℚ :=
  (r-l)*logSeriesLower q 2/(r*(1-r))

private theorem log_ge_rational_series (q : ℚ) (hq : 1 < q) :
    (logSeriesLower q 2 : ℝ) ≤ Real.log (q : ℝ) := by
  let c : RationalLogCertificate :=
    ⟨q, 2, logSeriesLower q 2, logSeriesUpper q 2⟩
  have hc : c.check = true := by
    simpa only [RationalLogCertificate.check, decide_eq_true_eq] using
      (show c.Valid from ⟨hq, le_rfl, le_rfl⟩)
  exact (RationalLogCertificate.check_sound c hc).1

/-- Real-integral Darboux soundness. On D5 all u≤1/3, hence u(1-u)
is increasing, so the RIGHT endpoint supplies its maximum. -/
private theorem actual_cell_lower (l r q : ℚ)
    (hl : a0 ≤ (l : ℝ)) (hlr : l ≤ r) (hr : (r : ℝ) ≤ top)
    (hq : 1 < q) (hseries : 0 ≤ logSeriesLower q 2)
    (harg : ∀ u ∈ Icc (l : ℝ) (r : ℝ),
      (q : ℝ) ≤
        upper u*(1-u-lower u)/(lower u*(1-u-upper u))) :
    (cellMass l r q : ℝ) ≤
      ∫ u in (l : ℝ)..(r : ℝ), outerSlice u := by
  have hlrR : (l : ℝ) ≤ (r : ℝ) := by exact_mod_cast hlr
  have hInt := intervalIntegrable_outerSlice hl hlrR hr
  have hFloor : ∀ u ∈ Icc (l : ℝ) (r : ℝ),
      (logSeriesLower q 2 : ℝ)/((r : ℝ)*(1-(r : ℝ))) ≤ outerSlice u := by
    intro u hu
    have huGeom : u ∈ Icc a0 top :=
      ⟨hl.trans hu.1, hu.2.trans hr⟩
    have hg := slice_geometry huGeom
    have hU : 0 < u*(1-u) :=
      mul_pos hg.1 (by linarith only [hg.2.2.2])
    have hR : 0 < (r : ℝ)*(1-(r : ℝ)) := by
      have hru : 0 < (r : ℝ) := lt_of_lt_of_le hg.1 hu.2
      have hr1 : (r : ℝ) < 1 :=
        lt_of_le_of_lt hr (by norm_num [top])
      exact mul_pos hru (by linarith only [hr1])
    have hRminus : 0 ≤ 1-(r : ℝ)-u := by
      have ht : top ≤ (1/3 : ℝ) := by norm_num [top]
      linarith only [hu.2, hr, ht]
    have hProd : 0 ≤ ((r : ℝ)-u)*(1-(r : ℝ)-u) :=
      mul_nonneg (sub_nonneg.mpr hu.2) hRminus
    have hUleR : u*(1-u) ≤ (r : ℝ)*(1-(r : ℝ)) := by
      nlinarith only [hProd]
    have hqreal : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast (lt_trans (by norm_num : (0 : ℚ) < 1) hq)
    have hlog : (logSeriesLower q 2 : ℝ) ≤
        Real.log (upper u*(1-u-lower u)/(lower u*(1-u-upper u))) :=
      (log_ge_rational_series q hq).trans
        (Real.log_le_log hqreal (harg u hu))
    have hseriesR : (0 : ℝ) ≤ (logSeriesLower q 2 : ℝ) := by
      exact_mod_cast hseries
    change (logSeriesLower q 2 : ℝ)/((r : ℝ)*(1-(r : ℝ))) ≤
      Real.log (upper u*(1-u-lower u)/(lower u*(1-u-upper u)))/(u*(1-u))
    apply (div_le_div_iff₀ hR hU).mpr
    exact (mul_le_mul_of_nonneg_left hUleR hseriesR).trans
      (mul_le_mul_of_nonneg_right hlog hR.le)
  have hMono := intervalIntegral.integral_mono_on hlrR
    intervalIntegrable_const hInt hFloor
  have hVal :
      ((r : ℝ)-(l : ℝ)) *
        ((logSeriesLower q 2 : ℚ) : ℝ)/((r : ℝ)*(1-(r : ℝ))) ≤
          ∫ u in (l : ℝ)..(r : ℝ), outerSlice u := by
    convert hMono using 1 <;>
      simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hCast :
      (cellMass l r q : ℝ) =
      ((r : ℝ)-(l : ℝ)) *
        ((logSeriesLower q 2 : ℚ) : ℝ)/((r : ℝ)*(1-(r : ℝ))) := by
    simp only [cellMass, Rat.cast_div, Rat.cast_mul, Rat.cast_sub, Rat.cast_one]
  exact hCast.le.trans hVal

/-- First affine denominator decreases on its original rational domain. -/
private theorem first_argument_floor (l r u : ℝ)
    (hl : a0 ≤ l) (hlr : l ≤ r) (hr : r ≤ cutOne)
    (hu : u ∈ Icc l r) :
    cap*(1-supportSum)/((supportSum-l)*(1-l-cap)) ≤
      cap*(1-u-(supportSum-u))/((supportSum-u)*(1-u-cap)) := by
  have ht : cutOne ≤ top :=
    (le_of_lt three_cut_order.2.1).trans (le_of_lt three_cut_order.2.2)
  have hUL : u ∈ Icc a0 cutOne := ⟨hl.trans hu.1,hu.2.trans hr⟩
  have hLL : l ∈ Icc a0 cutOne := ⟨hl,hlr.trans hr⟩
  have hgU := slice_geometry ⟨hUL.1,hUL.2.trans ht⟩
  have hgL := slice_geometry ⟨hLL.1,hLL.2.trans ht⟩
  have hfaU := first_affine hUL
  have hfaL := first_affine hLL
  have hA : 0 < supportSum-u := by simpa only [hfaU.1] using hgU.2.1
  have hB : 0 < 1-u-cap := by
    have h := hgU.2.2.2
    rw [hfaU.2] at h
    linarith only [h]
  have hC : 0 < supportSum-l := by simpa only [hfaL.1] using hgL.2.1
  have hD : 0 < 1-l-cap := by
    have h := hgL.2.2.2
    rw [hfaL.2] at h
    linarith only [h]
  have hDenBound :
      (supportSum-u)*(1-u-cap) ≤ (supportSum-l)*(1-l-cap) := by
    calc
      _ ≤ (supportSum-l)*(1-u-cap) :=
        mul_le_mul_of_nonneg_right (by linarith only [hu.1]) hB.le
      _ ≤ (supportSum-l)*(1-l-cap) :=
        mul_le_mul_of_nonneg_left (by linarith only [hu.1]) hC.le
  have hNum : 0 ≤ cap*(1-supportSum) := by norm_num [cap,supportSum]
  have h := (div_le_div_iff₀ (mul_pos hC hD) (mul_pos hA hB)).mpr
    (mul_le_mul_of_nonneg_left hDenBound hNum)
  simpa only [show (1-u-(supportSum-u) : ℝ) = 1-supportSum by ring] using h

/-- Second affine numerator decreases and denominator increases up to
the TRUE switch 19/58=(1-cap)/2. -/
private theorem second_argument_floor (l r u : ℝ)
    (hl : cutOne ≤ l) (hlr : l ≤ r) (hr : r ≤ cutTwo)
    (hu : u ∈ Icc l r) :
    cap*(1-2*r)/(r*(1-r-cap)) ≤ cap*(1-2*u)/(u*(1-u-cap)) := by
  have hTop : cutTwo ≤ top := le_of_lt three_cut_order.2.2
  have hUL : u ∈ Icc cutOne cutTwo := ⟨hl.trans hu.1,hu.2.trans hr⟩
  have hRL : r ∈ Icc cutOne cutTwo := ⟨hl.trans hlr,hr⟩
  have hgU := slice_geometry
    ⟨(le_of_lt three_cut_order.1).trans hUL.1,hUL.2.trans hTop⟩
  have hgR := slice_geometry
    ⟨(le_of_lt three_cut_order.1).trans hRL.1,hRL.2.trans hTop⟩
  have hAffineU := second_affine hUL
  have hAffineR := second_affine hRL
  have hBu : 0 < 1-u-cap := by
    have h := hgU.2.2.2
    rw [hAffineU.2] at h
    linarith only [h]
  have hBr : 0 < 1-r-cap := by
    have h := hgR.2.2.2
    rw [hAffineR.2] at h
    linarith only [h]
  have hDu : 0 < u*(1-u-cap) := mul_pos hgU.1 hBu
  have hDr : 0 < r*(1-r-cap) := mul_pos hgR.1 hBr
  have hCut : 1-cap-2*cutTwo=0 := by norm_num [cap,cutTwo]
  have hDelta : 0 ≤ 1-cap-r-u := by linarith only [hCut,hr,hu.2]
  have hProd : 0 ≤ (r-u)*(1-cap-r-u) :=
    mul_nonneg (sub_nonneg.mpr hu.2) hDelta
  have hDenBound : u*(1-u-cap) ≤ r*(1-r-cap) := by
    nlinarith only [hProd]
  have hNumBound : cap*(1-2*r) ≤ cap*(1-2*u) :=
    mul_le_mul_of_nonneg_left (by linarith only [hu.2]) (by norm_num [cap])
  have hNumR : 0 ≤ cap*(1-2*r) := by
    have ht : r ≤ top := hr.trans hTop
    have hc : 0 ≤ cap := by norm_num [cap]
    exact mul_nonneg hc (by dsimp [top] at ht; linarith only [ht])
  apply (div_le_div_iff₀ hDr hDu).mpr
  exact (mul_le_mul_of_nonneg_left hDenBound hNumR).trans
    (mul_le_mul_of_nonneg_right hNumBound hDr.le)

theorem first_cell (l r q : ℚ)
    (hl : a0 ≤ (l : ℝ)) (hlr : l ≤ r) (hr : (r : ℝ) ≤ cutOne)
    (hq : 1 < q) (hs : 0 ≤ logSeriesLower q 2)
    (hqv : (q : ℝ) =
      cap*(1-supportSum)/((supportSum-(l : ℝ))*(1-(l : ℝ)-cap))) :
    (cellMass l r q : ℝ) ≤ ∫ u in (l : ℝ)..(r : ℝ), outerSlice u := by
  apply actual_cell_lower l r q hl hlr
    (hr.trans ((le_of_lt three_cut_order.2.1).trans
      (le_of_lt three_cut_order.2.2))) hq hs
  intro u hu
  have hfr := first_argument_floor (l : ℝ) (r : ℝ) u hl
    (by exact_mod_cast hlr) hr hu
  have hfa := first_affine
    (show u ∈ Icc a0 cutOne from ⟨hl.trans hu.1,hu.2.trans hr⟩)
  change (q : ℝ) ≤
    upper u*(1-u-lower u)/(lower u*(1-u-upper u))
  rw [hfa.1,hfa.2]
  exact hqv.le.trans hfr

theorem second_cell (l r q : ℚ)
    (hl : cutOne ≤ (l : ℝ)) (hlr : l ≤ r) (hr : (r : ℝ) ≤ cutTwo)
    (hq : 1 < q) (hs : 0 ≤ logSeriesLower q 2)
    (hqv : (q : ℝ) =
      cap*(1-2*(r : ℝ))/((r : ℝ)*(1-(r : ℝ)-cap))) :
    (cellMass l r q : ℝ) ≤ ∫ u in (l : ℝ)..(r : ℝ), outerSlice u := by
  apply actual_cell_lower l r q
    ((le_of_lt three_cut_order.1).trans hl) hlr
    (hr.trans (le_of_lt three_cut_order.2.2)) hq hs
  intro u hu
  have hfr := second_argument_floor (l : ℝ) (r : ℝ) u hl
    (by exact_mod_cast hlr) hr hu
  have hfa := second_affine
    (show u ∈ Icc cutOne cutTwo from ⟨hl.trans hu.1,hu.2.trans hr⟩)
  change (q : ℝ) ≤
    upper u*(1-u-lower u)/(lower u*(1-u-upper u))
  rw [hfa.1,hfa.2]
  rw [show (1-u-u : ℝ) = 1-2*u by ring]
  exact hqv.le.trans hfr

/-- Each of the four original-domain rational cells is paid, and the
remaining third affine D5 piece is included by its proven nonnegativity.
The exact raw rational sum is >0.13032. -/
theorem genuine_four_cell_D5_ge_13_over_100 :
    (13/100 : ℝ) ≤ d5Logs := by
  let m₁ : ℚ := 217/908
  let m₂ : ℚ := 3853/13166
  have h₁ := first_cell (50/227) m₁ (249700/191821)
    (by norm_num [a0]) (by norm_num [m₁]) (by norm_num [m₁,cutOne])
    (by norm_num) (by norm_num [logSeriesLower,logParameter,Finset.sum_range_succ])
    (by norm_num [m₁,cap,supportSum])
  have h₂ := first_cell m₁ (117/454) (3995200/2750709)
    (by norm_num [m₁,a0]) (by norm_num [m₁]) (by norm_num [cutOne])
    (by norm_num) (by norm_num [logSeriesLower,logParameter,Finset.sum_range_succ])
    (by norm_num [m₁,cap,supportSum])
  have h₃ := second_cell (117/454) m₂ (8262800/6130123)
    (by norm_num [cutOne]) (by norm_num [m₂]) (by norm_num [m₂,cutTwo])
    (by norm_num) (by norm_num [logSeriesLower,logParameter,Finset.sum_range_succ])
    (by norm_num [m₂,cap])
  have h₄ := second_cell m₂ (19/58) (400/361)
    (by norm_num [m₂,cutOne]) (by norm_num [m₂]) (by norm_num [cutTwo])
    (by norm_num) (by norm_num [logSeriesLower,logParameter,Finset.sum_range_succ])
    (by norm_num [cap,cutTwo])
  have hRat : (13/100 : ℝ) ≤
      ((cellMass (50/227) m₁ (249700/191821) +
        cellMass m₁ (117/454) (3995200/2750709) +
        cellMass (117/454) m₂ (8262800/6130123) +
        cellMass m₂ (19/58) (400/361) : ℚ) : ℝ) := by
    norm_num [m₁,m₂,cellMass,logSeriesLower,logParameter,
      Finset.sum_range_succ]
  have hA : a0 ≤ (m₁ : ℝ) := by norm_num [a0,m₁]
  have hB : (m₁ : ℝ) ≤ cutOne := by norm_num [m₁,cutOne]
  have hC : cutOne ≤ (m₂ : ℝ) := by norm_num [m₂,cutOne]
  have hD : (m₂ : ℝ) ≤ cutTwo := by norm_num [m₂,cutTwo]
  have hE : cutTwo ≤ top := le_of_lt three_cut_order.2.2
  have hI₁ := intervalIntegrable_outerSlice (le_refl a0) hA
    (hB.trans (hC.trans (hD.trans hE)))
  have hI₂ := intervalIntegrable_outerSlice hA hB (hC.trans (hD.trans hE))
  have hI₃ := intervalIntegrable_outerSlice (hA.trans hB) hC (hD.trans hE)
  have hI₄ := intervalIntegrable_outerSlice
    (hA.trans (hB.trans hC)) hD hE
  have hI₁₂ := intervalIntegrable_outerSlice (le_refl a0)
    (hA.trans hB) (hC.trans (hD.trans hE))
  have hI₃₄ := intervalIntegrable_outerSlice
    (hA.trans hB) (hC.trans hD) hE
  have hI₁₄ := intervalIntegrable_outerSlice (le_refl a0)
    (hA.trans (hB.trans (hC.trans hD))) hE
  have hITail := intervalIntegrable_outerSlice
    (hA.trans (hB.trans (hC.trans hD))) hE (le_refl top)
  have s₁₂ := intervalIntegral.integral_add_adjacent_intervals hI₁ hI₂
  have s₃₄ := intervalIntegral.integral_add_adjacent_intervals hI₃ hI₄
  have s₁₄ := intervalIntegral.integral_add_adjacent_intervals hI₁₂ hI₃₄
  have sAll := intervalIntegral.integral_add_adjacent_intervals hI₁₄ hITail
  have hTail : 0 ≤ ∫ u in cutTwo..top, outerSlice u := by
    have h := intervalIntegral.integral_mono_on hE
      intervalIntegrable_const hITail
      (fun u hu =>
        Part5OriginalH430D5D7PositiveRationalLower.actual_d5_outer_nonneg
          ⟨(hA.trans (hB.trans (hC.trans hD))).trans hu.1,hu.2⟩)
    simpa only [intervalIntegral.integral_const,smul_zero] using h
  have hCast :
      (cellMass (50/227) m₁ (249700/191821) : ℝ) +
      (cellMass m₁ (117/454) (3995200/2750709) : ℝ) +
      (cellMass (117/454) m₂ (8262800/6130123) : ℝ) +
      (cellMass m₂ (19/58) (400/361) : ℝ) =
      ((cellMass (50/227) m₁ (249700/191821) +
        cellMass m₁ (117/454) (3995200/2750709) +
        cellMass (117/454) m₂ (8262800/6130123) +
        cellMass m₂ (19/58) (400/361) : ℚ) : ℝ) := by
    simp only [Rat.cast_add]
  rw [Part5OriginalH430D5D7PositiveRationalLower.actual_d5Logs_eq_outer]
  -- The endpoint equalities are definitional rational casts from the
  -- pinned source. Normalize only those endpoints, not the integral.
  dsimp [a0,cutOne,cutTwo] at hI₁ hI₂ hI₃ hI₄ hI₁₂ hI₃₄ hI₁₄ hITail
  linarith only [hRat,h₁,h₂,h₃,h₄,hTail,s₁₂,s₃₄,s₁₄,sAll,hCast]

/-- Full coefficient remains ORIGINAL seven-source /5 exactly once. -/
theorem actual_lambda_ge_379_over_5000 :
    (379/5000 : ℝ) ≤ lambda := by
  have h5 := genuine_four_cell_D5_ge_13_over_100
  have h0 :=
    Part5OriginalH430ThreeSingletonRationalLower.original_singleton_zero_ge_57_per_1000
  have h1 :=
    Part5OriginalH430ThreeSingletonRationalLower.original_singleton_one_ge_1_per_200
  have h2 :=
    Part5OriginalH430ThreeSingletonRationalLower.original_singleton_two_ge_29_per_1000
  have h6 :=
    Part5OriginalH430ActualD6BisectedRational.actual_d6Log_ge_11_over_100
  have h7 :=
    Part5OriginalH430D5D7PositiveRationalLower.actual_d7Log_ge_1_per_125
  have h8 :=
    Part5OriginalH430D8SecondAffineRationalLower.actual_d8Logs_ge_1_over_25
  rw [lambda_exact_seven_logs]
  linarith

end
end ImbalancedChen.Part5OriginalH430FourCellD5Darboux
