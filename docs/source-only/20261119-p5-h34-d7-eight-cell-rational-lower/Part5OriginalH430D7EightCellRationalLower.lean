import ImbalancedChen.Part5OriginalH430FourCellD5Darboux

/-!
P5.6 / h34. Eight exact rational D7 second-affine Darboux cells, with the
original moving first-affine support included as nonnegative.

This is a manuscript-INTERNAL source-only proof candidate. It does not
assume a target feedback, a seed, a count equivalence, or a new analytic
axiom. SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430D7EightCellRationalLower
noncomputable section

open Set MeasureTheory Certificates
open scoped Interval
open P2EnhancedSeedPairD7Domain
open P2EnhancedSeedPairD7Integral
open P2EnhancedSeedActualSevenLogIdentity
open P2EnhancedSeedActualFeedbackAssembly

/-- Lower mass for a genuine D7 second-affine cell, using the right
endpoint both for the decreasing logarithm argument and for u(1-u). -/
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

/-- The true D7 second-affine logarithm argument is decreasing. The
D7 boundary `max u (1-16u/5)` is resolved by the original lemma, not by
substituting a rectangle or treating an endpoint as an arithmetic null. -/
private theorem second_argument_floor (l r u : ℝ)
    (hl : boundaryCut ≤ l) (hlr : l ≤ r) (hr : r ≤ uHi)
    (hu : u ∈ Icc l r) :
    uHi*(1-2*r)/(r*(1-r-uHi)) ≤ logArgument u := by
  have hStart : supportStart ≤ boundaryCut := by
    norm_num [supportStart,boundaryCut]
  have hHi : 0 < uHi := by norm_num [uHi]
  have hThree : 0 ≤ 1-3*uHi := by norm_num [uHi]
  have hU : u ∈ Icc supportStart uHi :=
    ⟨hStart.trans (hl.trans hu.1),hu.2.trans hr⟩
  have hR : r ∈ Icc supportStart uHi :=
    ⟨hStart.trans (hl.trans hlr),hr⟩
  have hgU := endpoint_geometry hU
  have hgR := endpoint_geometry hR
  have hLowU := lowerEndpoint_second (hl.trans hu.1)
  have hBu : 0 < 1-u-uHi := by linarith only [hgU.2.2.2]
  have hBr : 0 < 1-r-uHi := by linarith only [hgR.2.2.2]
  have hDu : 0 < u*(1-u-uHi) := mul_pos hgU.1 hBu
  have hDr : 0 < r*(1-r-uHi) := mul_pos hgR.1 hBr
  have hDelta : 0 ≤ 1-uHi-r-u := by
    linarith only [hThree,hr,hu.2]
  have hProd : 0 ≤ (r-u)*(1-uHi-r-u) :=
    mul_nonneg (sub_nonneg.mpr hu.2) hDelta
  have hDenBound : u*(1-u-uHi) ≤ r*(1-r-uHi) := by
    nlinarith only [hProd]
  have hNumBound : uHi*(1-2*r) ≤ uHi*(1-2*u) :=
    mul_le_mul_of_nonneg_left (by linarith only [hu.2]) hHi.le
  have hHalf : uHi ≤ (1/2 : ℝ) := by norm_num [uHi]
  have hNumR : 0 ≤ uHi*(1-2*r) :=
    mul_nonneg hHi.le (by linarith only [hr,hHalf])
  unfold logArgument
  rw [hLowU]
  rw [show (1-u-u : ℝ) = 1-2*u by ring]
  apply (div_le_div_iff₀ hDr hDu).mpr
  exact (mul_le_mul_of_nonneg_left hDenBound hNumR).trans
    (mul_le_mul_of_nonneg_right hNumBound hDr.le)

private theorem interval_integrable (l r : ℝ)
    (hl : supportStart ≤ l) (hlr : l ≤ r) (hr : r ≤ uHi) :
    IntervalIntegrable outerSlice volume l r := by
  have hcont := continuousOn_outerSlice.mono
    (show Icc l r ⊆ Icc supportStart uHi from
      fun _ hu => ⟨hl.trans hu.1,hu.2.trans hr⟩)
  exact hcont.intervalIntegrable_of_Icc hlr

/-- Certified Darboux soundness for ANY rational cell fully inside the
original second D7 affine interval. This is a finite-cell consumer,
not a new hypothesis about the integral. The case q=1 is allowed. -/
private theorem actual_second_cell (l r q : ℚ)
    (hl : boundaryCut ≤ (l : ℝ)) (hlr : l ≤ r)
    (hr : (r : ℝ) ≤ uHi) (hq : 1 ≤ q)
    (hs : 0 ≤ logSeriesLower q 2)
    (harg : (q : ℝ) =
      uHi*(1-2*(r : ℝ))/((r : ℝ)*(1-(r : ℝ)-uHi))) :
    (cellMass l r q : ℝ) ≤
      ∫ u in (l : ℝ)..(r : ℝ), outerSlice u := by
  have hlrR : (l : ℝ) ≤ (r : ℝ) := by exact_mod_cast hlr
  have hStart : supportStart ≤ boundaryCut := by
    norm_num [supportStart,boundaryCut]
  have hInt := interval_integrable (l : ℝ) (r : ℝ)
    (hStart.trans hl) hlrR hr
  have hFloor : ∀ u ∈ Icc (l : ℝ) (r : ℝ),
      (logSeriesLower q 2 : ℝ)/((r : ℝ)*(1-(r : ℝ))) ≤ outerSlice u := by
    intro u hu
    have hFull : u ∈ Icc supportStart uHi :=
      ⟨hStart.trans (hl.trans hu.1),hu.2.trans hr⟩
    have hg := endpoint_geometry hFull
    have hU : 0 < u*(1-u) :=
      mul_pos hg.1 (by
        have hHiPos : 0 < uHi := by norm_num [uHi]
        linarith only [hg.2.2.2,hHiPos])
    have hR : 0 < (r : ℝ)*(1-(r : ℝ)) := by
      have hru : 0 < (r : ℝ) := lt_of_lt_of_le hg.1 hu.2
      have hhi : uHi < 1 := by norm_num [uHi]
      exact mul_pos hru (by linarith only [hr,hhi])
    have h2Hi : 2*uHi ≤ 1 := by norm_num [uHi]
    have hRminus : 0 ≤ 1-(r : ℝ)-u := by
      linarith only [h2Hi,hr,hu.2]
    have hProd : 0 ≤ ((r : ℝ)-u)*(1-(r : ℝ)-u) :=
      mul_nonneg (sub_nonneg.mpr hu.2) hRminus
    have hUleR : u*(1-u) ≤ (r : ℝ)*(1-(r : ℝ)) := by
      nlinarith only [hProd]
    have hqreal : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) hq)
    have hargU : (q : ℝ) ≤ logArgument u := by
      rw [harg]
      exact second_argument_floor (l : ℝ) (r : ℝ) u hl hlrR hr hu
    have hlog : (logSeriesLower q 2 : ℝ) ≤ Real.log (logArgument u) :=
      (rational_log_floor q hq).trans
        (Real.log_le_log hqreal hargU)
    have hsR : (0 : ℝ) ≤ (logSeriesLower q 2 : ℝ) := by
      exact_mod_cast hs
    change (logSeriesLower q 2 : ℝ)/((r : ℝ)*(1-(r : ℝ))) ≤
      Real.log (logArgument u)/(u*(1-u))
    apply (div_le_div_iff₀ hR hU).mpr
    exact (mul_le_mul_of_nonneg_left hUleR hsR).trans
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

/-- Eight actual second-affine D7 cells. The eighth cell has q=1 and
therefore contributes exactly zero, but its support is still counted.
The first-affine interval is also preserved as nonnegative. -/
theorem genuine_d7_eight_cell_ge_27_per_1000 :
    (27/1000 : ℝ) ≤ d7Log := by
  let a : ℚ := 5/21
  let t₁ : ℚ := 49/200
  let t₂ : ℚ := 1/4
  let t₃ : ℚ := 51/200
  let t₄ : ℚ := 13/50
  let t₅ : ℚ := 53/200
  let t₆ : ℚ := 27/100
  let t₇ : ℚ := 11/40
  let b : ℚ := 100/353
  have h₁ := actual_second_cell a t₁ (40000/31997)
    (by norm_num [a,boundaryCut]) (by norm_num [a,t₁])
    (by norm_num [t₁,uHi]) (by norm_num)
    (by norm_num [logSeriesLower,logParameter,Finset.sum_range_succ])
    (by norm_num [t₁,uHi])
  have h₂ := actual_second_cell t₁ t₂ (800/659)
    (by norm_num [t₁,boundaryCut]) (by norm_num [t₁,t₂])
    (by norm_num [t₂,uHi]) (by norm_num)
    (by norm_num [logSeriesLower,logParameter,Finset.sum_range_succ])
    (by norm_num [t₂,uHi])
  have h₃ := actual_second_cell t₂ t₃ (1960000/1662447)
    (by norm_num [t₂,boundaryCut]) (by norm_num [t₂,t₃])
    (by norm_num [t₃,uHi]) (by norm_num)
    (by norm_num [logSeriesLower,logParameter,Finset.sum_range_succ])
    (by norm_num [t₃,uHi])
  have h₄ := actual_second_cell t₃ t₄ (40000/34931)
    (by norm_num [t₃,boundaryCut]) (by norm_num [t₃,t₄])
    (by norm_num [t₄,uHi]) (by norm_num)
    (by norm_num [logSeriesLower,logParameter,Finset.sum_range_succ])
    (by norm_num [t₄,uHi])
  have h₅ := actual_second_cell t₄ t₅ (1880000/1690223)
    (by norm_num [t₄,boundaryCut]) (by norm_num [t₄,t₅])
    (by norm_num [t₅,uHi]) (by norm_num)
    (by norm_num [logSeriesLower,logParameter,Finset.sum_range_succ])
    (by norm_num [t₅,uHi])
  have h₆ := actual_second_cell t₅ t₆ (460000/425763)
    (by norm_num [t₅,boundaryCut]) (by norm_num [t₅,t₆])
    (by norm_num [t₆,uHi]) (by norm_num)
    (by norm_num [logSeriesLower,logParameter,Finset.sum_range_succ])
    (by norm_num [t₆,uHi])
  have h₇ := actual_second_cell t₆ t₇ (8000/7623)
    (by norm_num [t₆,boundaryCut]) (by norm_num [t₆,t₇])
    (by norm_num [t₇,uHi]) (by norm_num)
    (by norm_num [logSeriesLower,logParameter,Finset.sum_range_succ])
    (by norm_num [t₇,uHi])
  have h₈ := actual_second_cell t₇ b 1
    (by norm_num [t₇,boundaryCut]) (by norm_num [t₇,b])
    (by norm_num [b,uHi]) (by norm_num)
    (by norm_num [logSeriesLower,logParameter,Finset.sum_range_succ])
    (by norm_num [b,uHi])
  have hRational : (27/1000 : ℝ) ≤
      ((cellMass a t₁ (40000/31997) +
        cellMass t₁ t₂ (800/659) +
        cellMass t₂ t₃ (1960000/1662447) +
        cellMass t₃ t₄ (40000/34931) +
        cellMass t₄ t₅ (1880000/1690223) +
        cellMass t₅ t₆ (460000/425763) +
        cellMass t₆ t₇ (8000/7623) +
        cellMass t₇ b 1 : ℚ) : ℝ) := by
    norm_num [a,b,t₁,t₂,t₃,t₄,t₅,t₆,t₇,
      cellMass,logSeriesLower,logParameter,Finset.sum_range_succ]
  have hRatCast :
      (cellMass a t₁ (40000/31997) : ℝ) +
      (cellMass t₁ t₂ (800/659) : ℝ) +
      (cellMass t₂ t₃ (1960000/1662447) : ℝ) +
      (cellMass t₃ t₄ (40000/34931) : ℝ) +
      (cellMass t₄ t₅ (1880000/1690223) : ℝ) +
      (cellMass t₅ t₆ (460000/425763) : ℝ) +
      (cellMass t₆ t₇ (8000/7623) : ℝ) +
      (cellMass t₇ b 1 : ℝ) =
      ((cellMass a t₁ (40000/31997) +
        cellMass t₁ t₂ (800/659) +
        cellMass t₂ t₃ (1960000/1662447) +
        cellMass t₃ t₄ (40000/34931) +
        cellMass t₄ t₅ (1880000/1690223) +
        cellMass t₅ t₆ (460000/425763) +
        cellMass t₆ t₇ (8000/7623) +
        cellMass t₇ b 1 : ℚ) : ℝ) := by
    simp only [Rat.cast_add]
  have hbnd : supportStart ≤ boundaryCut := by
    norm_num [supportStart,boundaryCut]
  have hFinal : boundaryCut ≤ uHi := by
    norm_num [boundaryCut,uHi]
  have hInte : IntervalIntegrable outerSlice volume supportStart boundaryCut :=
    P2EnhancedSeedPairD7AffinePieces.first_intervalIntegrable
  have hIL : 0 ≤ ∫ u in supportStart..boundaryCut,outerSlice u := by
    have hh := intervalIntegral.integral_mono_on hbnd
      intervalIntegrable_const hInte
      (fun u hu =>
        Part5OriginalH430D5D7PositiveRationalLower.actual_d7_outer_nonneg
          ⟨hu.1,hu.2.trans hFinal⟩)
    simpa only [intervalIntegral.integral_const,smul_zero] using hh
  have hInt₁ := interval_integrable (a : ℝ) (t₁ : ℝ)
    (by norm_num [a,supportStart]) (by norm_num [a,t₁])
    (by norm_num [t₁,uHi])
  have hInt₂ := interval_integrable (t₁ : ℝ) (t₂ : ℝ)
    (by norm_num [t₁,supportStart]) (by norm_num [t₁,t₂])
    (by norm_num [t₂,uHi])
  have hInt₃ := interval_integrable (t₂ : ℝ) (t₃ : ℝ)
    (by norm_num [t₂,supportStart]) (by norm_num [t₂,t₃])
    (by norm_num [t₃,uHi])
  have hInt₄ := interval_integrable (t₃ : ℝ) (t₄ : ℝ)
    (by norm_num [t₃,supportStart]) (by norm_num [t₃,t₄])
    (by norm_num [t₄,uHi])
  have hInt₅ := interval_integrable (t₄ : ℝ) (t₅ : ℝ)
    (by norm_num [t₄,supportStart]) (by norm_num [t₄,t₅])
    (by norm_num [t₅,uHi])
  have hInt₆ := interval_integrable (t₅ : ℝ) (t₆ : ℝ)
    (by norm_num [t₅,supportStart]) (by norm_num [t₅,t₆])
    (by norm_num [t₆,uHi])
  have hInt₇ := interval_integrable (t₆ : ℝ) (t₇ : ℝ)
    (by norm_num [t₆,supportStart]) (by norm_num [t₆,t₇])
    (by norm_num [t₇,uHi])
  have hInt₈ := interval_integrable (t₇ : ℝ) (b : ℝ)
    (by norm_num [t₇,supportStart]) (by norm_num [t₇,b])
    (by norm_num [b,uHi])
  have hP₂ := interval_integrable (a : ℝ) (t₂ : ℝ)
    (by norm_num [a,supportStart]) (by norm_num [a,t₂])
    (by norm_num [t₂,uHi])
  have hP₃ := interval_integrable (a : ℝ) (t₃ : ℝ)
    (by norm_num [a,supportStart]) (by norm_num [a,t₃])
    (by norm_num [t₃,uHi])
  have hP₄ := interval_integrable (a : ℝ) (t₄ : ℝ)
    (by norm_num [a,supportStart]) (by norm_num [a,t₄])
    (by norm_num [t₄,uHi])
  have hP₅ := interval_integrable (a : ℝ) (t₅ : ℝ)
    (by norm_num [a,supportStart]) (by norm_num [a,t₅])
    (by norm_num [t₅,uHi])
  have hP₆ := interval_integrable (a : ℝ) (t₆ : ℝ)
    (by norm_num [a,supportStart]) (by norm_num [a,t₆])
    (by norm_num [t₆,uHi])
  have hP₇ := interval_integrable (a : ℝ) (t₇ : ℝ)
    (by norm_num [a,supportStart]) (by norm_num [a,t₇])
    (by norm_num [t₇,uHi])
  have s₂ := intervalIntegral.integral_add_adjacent_intervals hInt₁ hInt₂
  have s₃ := intervalIntegral.integral_add_adjacent_intervals hP₂ hInt₃
  have s₄ := intervalIntegral.integral_add_adjacent_intervals hP₃ hInt₄
  have s₅ := intervalIntegral.integral_add_adjacent_intervals hP₄ hInt₅
  have s₆ := intervalIntegral.integral_add_adjacent_intervals hP₅ hInt₆
  have s₇ := intervalIntegral.integral_add_adjacent_intervals hP₆ hInt₇
  have s₈ := intervalIntegral.integral_add_adjacent_intervals hP₇ hInt₈
  have hInner : (27/1000 : ℝ) ≤
      ∫ u in boundaryCut..uHi,outerSlice u := by
    have hA : (a : ℝ) = boundaryCut := by norm_num [a,boundaryCut]
    have hB : (b : ℝ) = uHi := by norm_num [b,uHi]
    rw [← hA,← hB]
    linarith only [hRational,hRatCast,h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,
      s₂,s₃,s₄,s₅,s₆,s₇,s₈]
  have hFull : (∫ u in supportStart..uHi,outerSlice u) = d7Log := by
    unfold d7Log
    rw [integral_Ioo_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (hbnd.trans hFinal)]
    rfl
  have sFull := intervalIntegral.integral_add_adjacent_intervals hInte
    (interval_integrable boundaryCut uHi hbnd hFinal (le_refl uHi))
  rw [← hFull]
  linarith only [hIL,hInner,sFull]

/-- Actual seven-term /5 normalisation, improving the independent D7
source only; no interpolation of original analytical/count obligations. -/
theorem actual_lambda_ge_398_over_5000 :
    (398/5000 : ℝ) ≤ lambda := by
  have h0 := Part5OriginalH430ThreeSingletonRationalLower.original_singleton_zero_ge_57_per_1000
  have h1 := Part5OriginalH430ThreeSingletonRationalLower.original_singleton_one_ge_1_per_200
  have h2 := Part5OriginalH430ThreeSingletonRationalLower.original_singleton_two_ge_29_per_1000
  have h5 := Part5OriginalH430FourCellD5Darboux.genuine_four_cell_D5_ge_13_over_100
  have h6 := Part5OriginalH430ActualD6BisectedRational.actual_d6Log_ge_11_over_100
  have h7 := genuine_d7_eight_cell_ge_27_per_1000
  have h8 := Part5OriginalH430D8SecondAffineRationalLower.actual_d8Logs_ge_1_over_25
  rw [lambda_exact_seven_logs]
  linarith

end
end ImbalancedChen.Part5OriginalH430D7EightCellRationalLower
