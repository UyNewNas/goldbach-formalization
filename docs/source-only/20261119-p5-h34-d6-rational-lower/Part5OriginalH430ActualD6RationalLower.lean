import ImbalancedChen.Part5OriginalH430ActualW2FourStepSeedAudit
import ImbalancedChen.P2EnhancedSeedActualSevenLogIdentity
import ImbalancedChen.P2EnhancedSeedInheritedCellBounds

/-!
P5.6 h34: a genuine rational, source-level lower certificate for one
UNCHANGED component of the seven-domain W2 feedback coefficient.

The original D6 untruncated domain and exact same-Q logarithmic outer
slice are reused. A two-term rational log series and a single Darboux
cell prove a strict positive lower bound for the ACTUAL D6 integral.
The other six domain terms are shown nonnegative using their literal
geometries. This proves only a PARTIAL lower bound on the real lambda:
it does NOT prove lambda >= 13/100, the analytic intercept, seed
soundness, CLOSED-CELL induction, or the original U3/U4 count source.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualD6RationalLower

noncomputable section
open Set MeasureTheory
open scoped Interval
open P2EnhancedSeedActualFeedbackAssembly
open P2EnhancedSeedActualSevenLogIdentity

/-- This is an *evaluated rational inequality*, not a numerical assumption
about a real integral. The lower polynomial is the actual two-term
RationalLogCertificate series for the unchanged full D6 cell. -/
theorem d6_full_cell_rational_arithmetic :
    (103 / 1000 : ℝ) ≤
      (((((100 / 353 - 50 / 227 : ℚ) *
          P2EnhancedSeedInheritedCellBounds.d6CellLower
            2 (50 / 227) (100 / 353)) : ℚ)) : ℝ) := by
  norm_num [P2EnhancedSeedInheritedCellBounds.d6CellLower,
    P2EnhancedSeedInheritedCellBounds.d6RationalArgument,
    ImbalancedChen.Certificates.logSeriesLower,
    ImbalancedChen.Certificates.logParameter,
    Finset.sum_range_succ]

/-- An ACTUAL, support-preserving analytic component bound. The
D6 cell theorem derives the real integral estimate from a rational
log certificate, not from a stored floating-point coefficient. -/
theorem actual_d6Log_ge_103_over_1000 :
    (103 / 1000 : ℝ) ≤ d6Log := by
  have hcell :=
    P2EnhancedSeedInheritedCellBounds.d6_rational_cell_integral_lower
      2 (50 / 227 : ℚ) (100 / 353 : ℚ)
      (by norm_num) (by norm_num) (by norm_num)
  have heq :
      (∫ u in (50 / 227 : ℝ)..(100 / 353 : ℝ),
        P2EnhancedSeedInheritedCellBounds.d6OuterSlice u) = d6Log := by
    unfold d6Log
    rw [integral_Ioo_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le
        (by norm_num : (50 / 227 : ℝ) ≤ 100 / 353)]
    rfl
  calc
    (103 / 1000 : ℝ) ≤
        (((((100 / 353 - 50 / 227 : ℚ) *
          P2EnhancedSeedInheritedCellBounds.d6CellLower
            2 (50 / 227) (100 / 353)) : ℚ)) : ℝ) :=
      d6_full_cell_rational_arithmetic
    _ ≤ (∫ u in (50 / 227 : ℝ)..(100 / 353 : ℝ),
          P2EnhancedSeedInheritedCellBounds.d6OuterSlice u) := hcell
    _ = d6Log := heq

/-- All THREE original singleton terms are nonnegative on their
unchanged short-support intervals. -/
theorem original_singleton_coefficient_nonneg (j : Fin 3) :
    0 ≤ singletonCoefficient j := by
  unfold singletonCoefficient
  apply MeasureTheory.setIntegral_nonneg
  intro u hu
  have hcap := P2EnhancedSeedSingletonPrimitive.literal_bounds j
  exact P2EnhancedSeedSingletonPrimitive.singletonLogKernel_nonneg
    ⟨hu.1, hu.2.trans hcap.2.2.2.1⟩

/-- All FOUR original pair terms are nonnegative on the literal
supported subsets of their own physical domains, including rho < 2.
There is no replacement of a supported domain by a larger rectangle. -/
theorem original_pair_coefficient_nonneg (j : Fin 4) :
    0 ≤ pairCoefficient j := by
  unfold pairCoefficient
  apply MeasureTheory.setIntegral_nonneg
  intro x hx
  have hg := P5OriginalFeedbackDomains.W2PairDomain_geometry
    P2EnhancedSeedSingletonPrimitive.parameters_geometry j hx.1
  have hu : 0 < x 0 :=
    lt_of_lt_of_le (by norm_num) (hg.1.1 0)
  have hv : 0 < x 1 :=
    lt_of_lt_of_le (by norm_num) (hg.1.1 1)
  have hr : 0 < 1 - x 0 - x 1 :=
    lt_of_lt_of_le (by norm_num) hg.2
  have hden : 0 < x 0 * x 1 * (1 - x 0 - x 1) :=
    mul_pos (mul_pos hu hv) hr
  change (0 : ℝ) ≤ 1 / (x 0 * x 1 * (1 - x 0 - x 1))
  exact (div_pos (by norm_num) hden).le

/-- The three remaining pair log domains keep their actual D5,
D7 and D8 support cuts. These nonnegative terms cannot be silently
discarded from an EXACT identity; they may be dropped only for a
one-sided lower estimate. -/
theorem other_pair_log_terms_nonneg :
    0 ≤ d5Logs ∧ 0 ≤ d7Log ∧ 0 ≤ d8Logs := by
  constructor
  · rw [← pairCoefficient_D5_logs]
    exact original_pair_coefficient_nonneg 0
  constructor
  · rw [← pairCoefficient_D7_log]
    exact original_pair_coefficient_nonneg 2
  · rw [← pairCoefficient_D8_logs]
    exact original_pair_coefficient_nonneg 3

/-- The original 3+4 integral normalization is used exactly once. -/
theorem actual_lambda_ge_d6_over_five :
    d6Log / 5 ≤ lambda := by
  have hs0 := original_singleton_coefficient_nonneg (0 : Fin 3)
  have hs1 := original_singleton_coefficient_nonneg (1 : Fin 3)
  have hs2 := original_singleton_coefficient_nonneg (2 : Fin 3)
  obtain ⟨hd5, hd7, hd8⟩ := other_pair_log_terms_nonneg
  rw [lambda_exact_seven_logs]
  linarith

/-- A genuine positive bound on the ACTUAL feedback coefficient,
not the desired 0.13 and not a claim that the analytic seed is paid. -/
theorem actual_lambda_ge_103_over_5000 :
    (103 / 5000 : ℝ) ≤ lambda := by
  have hd := actual_d6Log_ge_103_over_1000
  have hs := actual_lambda_ge_d6_over_five
  linarith

/-- This is the exact original J=1/50 feedback *model value*.
No fixed intercept or full analytic F lower bound is deduced. -/
theorem actual_feedback_model_partial_lower :
    (103 / 250000 : ℝ) ≤ actualFeedback (1 / 50) := by
  rw [actualFeedback_one_fiftieth]
  have h := actual_lambda_ge_103_over_5000
  linarith

end
end ImbalancedChen.Part5OriginalH430ActualD6RationalLower
