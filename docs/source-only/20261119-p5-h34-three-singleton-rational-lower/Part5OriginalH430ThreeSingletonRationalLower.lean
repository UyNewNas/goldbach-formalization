import ImbalancedChen.Part5OriginalH430ActualD6BisectedRational
import ImbalancedChen.P2EnhancedSeedSingletonPrimitive
import ImbalancedChen.P2EnhancedSeedActualSevenLogIdentity

/-!
P5.6 / h34: rational lower certificates for EACH of the three ORIGINAL
short-support W2 singleton coefficients (not one generic proxy domain).
The source is the genuine short-support singletonLogKernel, with its
original j-dependent cap. RationalLogCertificate.check_sound is reused;
no analytic intercept, enhanced-count licence or lambda >= 13/100 is assumed.

The first Darboux cell begins at the exact support onset 67/227 and its
lower logarithmic bound is ZERO. The second cell has a nonzero rational
left endpoint. This avoids attributing mass outside the true support.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ThreeSingletonRationalLower

noncomputable section
open Set MeasureTheory
open scoped Interval
open P2EnhancedSeedSingletonPrimitive
open P2EnhancedSeedActualFeedbackAssembly
open P2EnhancedSeedActualSevenLogIdentity

/-- Set integral of the original closed singleton support, with endpoint
nullity paid before using interval-integral additivity. -/
private theorem singletonCoefficient_as_interval (j : Fin 3) :
    singletonCoefficient j =
      ∫ u in uStar..(cap j), singletonLogKernel u := by
  unfold singletonCoefficient
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (literal_bounds j).2.2.1.le]

/-- Two-cell Darboux supplier for any ORIGINAL singleton cap.
Only the actual second cell has nonzero log mass; the first is retained
in the integral partition and shown to have exactly zero lower bound. -/
theorem literal_singleton_right_cell_lower (j : Fin 3) (m r : ℚ)
    (hlo : (67 / 227 : ℚ) ≤ m) (hmid : m ≤ r)
    (hr : r ≤ (5 / 11 : ℚ)) (hcap : cap j = (r : ℝ)) :
    (((r - m) * cellLower 2 m r : ℚ) : ℝ) ≤ singletonCoefficient j := by
  have hL := rational_cell_integral_lower
    2 (67 / 227 : ℚ) m (le_refl _) hlo (hmid.trans hr)
  have hR := rational_cell_integral_lower 2 m r hlo hmid hr
  have hmLR : (67 / 227 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlo
  have hmRR : (m : ℝ) ≤ (r : ℝ) := by exact_mod_cast hmid
  have hrRR : (r : ℝ) ≤ (5 / 11 : ℝ) := by exact_mod_cast hr
  have hCont : ContinuousOn singletonLogKernel
      (Icc (67 / 227 : ℝ) (r : ℝ)) :=
    continuousOn_singletonLogKernel (by norm_num) hrRR
  have hContL : ContinuousOn singletonLogKernel
      (Icc (67 / 227 : ℝ) (m : ℝ)) :=
    hCont.mono (by
      intro u hu
      exact ⟨hu.1, hu.2.trans hmRR⟩)
  have hContR : ContinuousOn singletonLogKernel
      (Icc (m : ℝ) (r : ℝ)) :=
    hCont.mono (by
      intro u hu
      exact ⟨hmLR.trans hu.1, hu.2⟩)
  have hIntL : IntervalIntegrable singletonLogKernel volume
      (67 / 227 : ℝ) (m : ℝ) :=
    hContL.intervalIntegrable_of_Icc hmLR
  have hIntR : IntervalIntegrable singletonLogKernel volume
      (m : ℝ) (r : ℝ) :=
    hContR.intervalIntegrable_of_Icc hmRR
  have hSplit :
      (∫ u in (67 / 227 : ℝ)..(m : ℝ), singletonLogKernel u) +
        (∫ u in (m : ℝ)..(r : ℝ), singletonLogKernel u) =
      (∫ u in (67 / 227 : ℝ)..(r : ℝ), singletonLogKernel u) :=
    intervalIntegral.integral_add_adjacent_intervals hIntL hIntR
  have hFull :
      (∫ u in (67 / 227 : ℝ)..(r : ℝ), singletonLogKernel u) =
      singletonCoefficient j := by
    calc
      _ = ∫ u in uStar..(cap j), singletonLogKernel u := by
        rw [uStar, hcap]
      _ = singletonCoefficient j := (singletonCoefficient_as_interval j).symm
  have hAdd :
      (((((m - (67 / 227 : ℚ)) * cellLower 2 (67 / 227) m) +
          ((r - m) * cellLower 2 m r) : ℚ) : ℝ) ≤ singletonCoefficient j := by
    calc
      _ = ((((m - (67 / 227 : ℚ)) * cellLower 2 (67 / 227) m : ℚ) : ℝ) +
          (((r - m) * cellLower 2 m r : ℚ) : ℝ) := by
        exact Rat.cast_add _ _
      _ ≤ (∫ u in (67 / 227 : ℝ)..(m : ℝ), singletonLogKernel u) +
          (∫ u in (m : ℝ)..(r : ℝ), singletonLogKernel u) :=
        add_le_add hL hR
      _ = singletonCoefficient j := hSplit.trans hFull
  have hZero : cellLower 2 (67 / 227 : ℚ) m = 0 := by
    norm_num [cellLower, rationalArgument,
      ImbalancedChen.Certificates.logSeriesLower,
      ImbalancedChen.Certificates.logParameter, Finset.sum_range_succ]
  simpa only [hZero, mul_zero, zero_add] using hAdd

/-- Each rational inequality below is independent exact arithmetic.
The selected midpoints stay within their respective TRUE caps. -/
private theorem first_rational :
    (57 / 1000 : ℝ) ≤
      (((((5 / 11 : ℚ) - (379 / 1000 : ℚ)) *
          cellLower 2 (379 / 1000) (5 / 11)) : ℚ) : ℝ) := by
  norm_num [cellLower, rationalArgument,
    ImbalancedChen.Certificates.logSeriesLower,
    ImbalancedChen.Certificates.logParameter, Finset.sum_range_succ]

private theorem second_rational :
    (1 / 200 : ℝ) ≤
      (((((10 / 29 : ℚ) - (8 / 25 : ℚ)) *
          cellLower 2 (8 / 25) (10 / 29)) : ℚ) : ℝ) := by
  norm_num [cellLower, rationalArgument,
    ImbalancedChen.Certificates.logSeriesLower,
    ImbalancedChen.Certificates.logParameter, Finset.sum_range_succ]

private theorem third_rational :
    (29 / 1000 : ℝ) ≤
      (((((25 / 61 : ℚ) - (177 / 500 : ℚ)) *
          cellLower 2 (177 / 500) (25 / 61)) : ℚ) : ℝ) := by
  norm_num [cellLower, rationalArgument,
    ImbalancedChen.Certificates.logSeriesLower,
    ImbalancedChen.Certificates.logParameter, Finset.sum_range_succ]

theorem original_singleton_zero_ge_57_per_1000 :
    (57 / 1000 : ℝ) ≤ singletonCoefficient (0 : Fin 3) := by
  exact first_rational.trans
    (literal_singleton_right_cell_lower 0 (379 / 1000) (5 / 11)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cap]))

theorem original_singleton_one_ge_1_per_200 :
    (1 / 200 : ℝ) ≤ singletonCoefficient (1 : Fin 3) := by
  exact second_rational.trans
    (literal_singleton_right_cell_lower 1 (8 / 25) (10 / 29)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cap]))

theorem original_singleton_two_ge_29_per_1000 :
    (29 / 1000 : ℝ) ≤ singletonCoefficient (2 : Fin 3) := by
  exact third_rational.trans
    (literal_singleton_right_cell_lower 2 (177 / 500) (25 / 61)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cap]))

/-- Exact source-specific partial gain: all three original singleton
integrals and D6 are now paid by distinct rational cells, while D5/D7/D8
remain nonnegative (not falsely evaluated). This is far short of 0.13. -/
theorem actual_lambda_ge_201_over_5000 :
    (201 / 5000 : ℝ) ≤ lambda := by
  have hs0 := original_singleton_zero_ge_57_per_1000
  have hs1 := original_singleton_one_ge_1_per_200
  have hs2 := original_singleton_two_ge_29_per_1000
  have hd6 :=
    Part5OriginalH430ActualD6BisectedRational.actual_d6Log_ge_11_over_100
  obtain ⟨hd5, hd7, hd8⟩ :=
    Part5OriginalH430ActualD6RationalLower.other_pair_log_terms_nonneg
  rw [lambda_exact_seven_logs]
  linarith

theorem actual_feedback_one_fiftieth_ge_201_over_250000 :
    (201 / 250000 : ℝ) ≤ actualFeedback (1 / 50) := by
  rw [actualFeedback_one_fiftieth]
  have h := actual_lambda_ge_201_over_5000
  linarith

end
end ImbalancedChen.Part5OriginalH430ThreeSingletonRationalLower
