import ImbalancedChen.Part5OriginalH430D7EightCellRationalLower

/-!
P5.6 / h34: independent four-cell lower certificates for EACH of the
three genuine short-support singleton integrals.  The first cell begins
at the literal support threshold 67/227, where its certified log lower
bound is zero. The four cells cover the ENTIRE interval up to each true
cap. No cells, endpoint contributions or /5 normalisations are omitted.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
The original count intercept, closed-cell induction and feedback-to-count
licence remain manuscript-internal obligations, not hypotheses here.
-/

namespace ImbalancedChen.Part5OriginalH430ThreeSingletonFourCell
noncomputable section

open Set MeasureTheory Certificates
open scoped Interval
open P2EnhancedSeedSingletonPrimitive
open P2EnhancedSeedActualSevenLogIdentity
open P2EnhancedSeedActualFeedbackAssembly

/-- Exact rational Darboux cell: 2 odd-series terms; the denominator
is taken at the cell's RIGHT endpoint and the logarithm at its LEFT. -/
def cellMass (l r : ℚ) : ℚ := (r-l) * cellLower 2 l r

private theorem cell_integrable (l r : ℚ)
    (hl : (67/227 : ℚ) ≤ l) (hlr : l ≤ r)
    (hr : r ≤ (5/11 : ℚ)) :
    IntervalIntegrable singletonLogKernel volume (l : ℝ) (r : ℝ) := by
  have hlR : (67/227 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hlrR : (l : ℝ) ≤ (r : ℝ) := by exact_mod_cast hlr
  have hrR : (r : ℝ) ≤ (5/11 : ℝ) := by exact_mod_cast hr
  have hlPos : (0 : ℝ) < (l : ℝ) :=
    lt_of_lt_of_le (by norm_num) hlR
  exact (continuousOn_singletonLogKernel hlPos hrR).intervalIntegrable_of_Icc hlrR

/-- Soundness for FOUR actual rational cells from 67/227 to the original
j-specific cap, using three interval-integral joins and no replacement
count identity. The first cell has zero or positive certified mass. -/
theorem four_cell_supplier (j : Fin 3) (a b c d : ℚ)
    (ha : (67/227 : ℚ) ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hd : d ≤ (5/11 : ℚ))
    (hcap : cap j = (d : ℝ)) :
    ((cellMass (67/227) a + cellMass a b +
      cellMass b c + cellMass c d : ℚ) : ℝ) ≤
        singletonCoefficient j := by
  have haTop : a ≤ (5/11 : ℚ) := hab.trans (hbc.trans (hcd.trans hd))
  have hbTop : b ≤ (5/11 : ℚ) := hbc.trans (hcd.trans hd)
  have hcTop : c ≤ (5/11 : ℚ) := hcd.trans hd
  have hm₁ := rational_cell_integral_lower 2 (67/227) a
    (le_refl _) ha haTop
  have hm₂ := rational_cell_integral_lower 2 a b ha hab hbTop
  have hm₃ := rational_cell_integral_lower 2 b c (ha.trans hab) hbc hcTop
  have hm₄ := rational_cell_integral_lower 2 c d
    ((ha.trans hab).trans hbc) hcd hd
  change (cellMass (67/227) a : ℝ) ≤
    ∫ u in ((67/227 : ℚ) : ℝ)..(a : ℝ), singletonLogKernel u at hm₁
  change (cellMass a b : ℝ) ≤
    ∫ u in (a : ℝ)..(b : ℝ), singletonLogKernel u at hm₂
  change (cellMass b c : ℝ) ≤
    ∫ u in (b : ℝ)..(c : ℝ), singletonLogKernel u at hm₃
  change (cellMass c d : ℝ) ≤
    ∫ u in (c : ℝ)..(d : ℝ), singletonLogKernel u at hm₄
  have hs₁₂ := intervalIntegral.integral_add_adjacent_intervals
    (cell_integrable (67/227) a (le_refl _) ha haTop)
    (cell_integrable a b ha hab hbTop)
  have hs₁₂₃ := intervalIntegral.integral_add_adjacent_intervals
    (cell_integrable (67/227) b (le_refl _) (ha.trans hab) hbTop)
    (cell_integrable b c (ha.trans hab) hbc hcTop)
  have hs₁₂₃₄ := intervalIntegral.integral_add_adjacent_intervals
    (cell_integrable (67/227) c (le_refl _)
      ((ha.trans hab).trans hbc) hcTop)
    (cell_integrable c d ((ha.trans hab).trans hbc) hcd hd)
  have hFull :
      (∫ u in ((67/227 : ℚ) : ℝ)..(d : ℝ), singletonLogKernel u) =
        singletonCoefficient j := by
    unfold singletonCoefficient
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (literal_bounds j).2.2.1.le]
    simp only [uStar, hcap, Rat.cast_div, Rat.cast_ofNat]
  have hCast :
      (cellMass (67/227) a : ℝ) + (cellMass a b : ℝ) +
        (cellMass b c : ℝ) + (cellMass c d : ℝ) =
      ((cellMass (67/227) a + cellMass a b +
        cellMass b c + cellMass c d : ℚ) : ℝ) := by
    simp only [Rat.cast_add]
  linarith only [hm₁,hm₂,hm₃,hm₄,hs₁₂,hs₁₂₃,hs₁₂₃₄,hFull,hCast]

/-- Complete original singleton 0 support [67/227,5/11]. The exact
four-cell rational sum exceeds 89/1000. -/
theorem original_singleton_zero_ge_89_per_1000 :
    (89/1000 : ℝ) ≤ singletonCoefficient (0 : Fin 3) := by
  have hExact : (89/1000 : ℝ) ≤
      ((cellMass (67/227) (1/3) + cellMass (1/3) (3/8) +
        cellMass (3/8) (5/12) + cellMass (5/12) (5/11) : ℚ) : ℝ) := by
    norm_num [cellMass,cellLower,rationalArgument,
      logSeriesLower,logParameter,Finset.sum_range_succ]
  exact hExact.trans (four_cell_supplier 0 (1/3) (3/8) (5/12) (5/11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [cap]))

/-- Complete original singleton 1 support [67/227,10/29]. -/
theorem original_singleton_one_ge_8_per_1000 :
    (8/1000 : ℝ) ≤ singletonCoefficient (1 : Fin 3) := by
  have hExact : (8/1000 : ℝ) ≤
      ((cellMass (67/227) (31/100) + cellMass (31/100) (8/25) +
        cellMass (8/25) (33/100) + cellMass (33/100) (10/29) : ℚ) : ℝ) := by
    norm_num [cellMass,cellLower,rationalArgument,
      logSeriesLower,logParameter,Finset.sum_range_succ]
  exact hExact.trans (four_cell_supplier 1 (31/100) (8/25) (33/100) (10/29)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [cap]))

/-- Complete original singleton 2 support [67/227,25/61]. -/
theorem original_singleton_two_ge_45_per_1000 :
    (45/1000 : ℝ) ≤ singletonCoefficient (2 : Fin 3) := by
  have hExact : (45/1000 : ℝ) ≤
      ((cellMass (67/227) (13/40) + cellMass (13/40) (7/20) +
        cellMass (7/20) (3/8) + cellMass (3/8) (25/61) : ℚ) : ℝ) := by
    norm_num [cellMass,cellLower,rationalArgument,
      logSeriesLower,logParameter,Finset.sum_range_succ]
  exact hExact.trans (four_cell_supplier 2 (13/40) (7/20) (3/8) (25/61)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [cap]))

/-- All seven ACTUAL coefficient sources and their original /5 factor.
The numerical gain is only PARTIAL and does not establish lambda >= .13. -/
theorem actual_lambda_ge_449_over_5000 :
    (449/5000 : ℝ) ≤ lambda := by
  have h0 := original_singleton_zero_ge_89_per_1000
  have h1 := original_singleton_one_ge_8_per_1000
  have h2 := original_singleton_two_ge_45_per_1000
  have h5 := Part5OriginalH430FourCellD5Darboux.genuine_four_cell_D5_ge_13_over_100
  have h6 := Part5OriginalH430ActualD6BisectedRational.actual_d6Log_ge_11_over_100
  have h7 := Part5OriginalH430D7EightCellRationalLower.genuine_d7_eight_cell_ge_27_per_1000
  have h8 := Part5OriginalH430D8SecondAffineRationalLower.actual_d8Logs_ge_1_over_25
  rw [lambda_exact_seven_logs]
  linarith

end
end ImbalancedChen.Part5OriginalH430ThreeSingletonFourCell
