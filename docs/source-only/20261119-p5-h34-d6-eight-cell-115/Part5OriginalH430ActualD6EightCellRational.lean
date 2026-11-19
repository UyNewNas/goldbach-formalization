import ImbalancedChen.Part5OriginalH430D5TwentyFourCellRational
import ImbalancedChen.P2EnhancedSeedInheritedCellBounds

/-!
P5.6 / h34, fixed frozen manuscript ba6ec11d.
Eight consecutive exact rational cells on the original untruncated D6 interval.
The existing sound two-term RationalLogCertificate and original d6OuterSlice
are reused. No alternative support, count permission, or feedback normalization.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualD6EightCellRational

noncomputable section

open Set MeasureTheory
open scoped Interval
open P2EnhancedSeedInheritedCellBounds
open P2EnhancedSeedActualSevenLogIdentity
open P2EnhancedSeedActualFeedbackAssembly

/-- Exact rational sum of the original eight ordered D6 subintervals.
No floating-point constant enters the definition. -/
private def eightCellMass : ℚ :=
  ((73125/320524 - 50/227 : ℚ) * d6CellLower 2 (50/227) (73125/320524)) +
  ((37825/160262 - 73125/320524 : ℚ) * d6CellLower 2 (73125/320524) (37825/160262)) +
  ((78175/320524 - 37825/160262 : ℚ) * d6CellLower 2 (37825/160262) (78175/320524)) +
  ((20175/80131 - 78175/320524 : ℚ) * d6CellLower 2 (78175/320524) (20175/80131)) +
  ((83225/320524 - 20175/80131 : ℚ) * d6CellLower 2 (20175/80131) (83225/320524)) +
  ((42875/160262 - 83225/320524 : ℚ) * d6CellLower 2 (83225/320524) (42875/160262)) +
  ((88275/320524 - 42875/160262 : ℚ) * d6CellLower 2 (42875/160262) (88275/320524)) +
  ((100/353 - 88275/320524 : ℚ) * d6CellLower 2 (88275/320524) (100/353))

/-- The original outer logarithmic kernel is integrable on each
physical subinterval. This only applies existing integrability. -/
private theorem join_actual (a b c : ℚ)
    (ha : (50/227 : ℚ) ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hc : c ≤ (100/353 : ℚ)) :
    (∫ u in (a : ℝ)..(b : ℝ), d6OuterSlice u) +
    (∫ u in (b : ℝ)..(c : ℝ), d6OuterSlice u) =
    (∫ u in (a : ℝ)..(c : ℝ), d6OuterSlice u) := by
  have haR : (50/227 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hbcR : (b : ℝ) ≤ (c : ℝ) := by exact_mod_cast hbc
  have hcR : (c : ℝ) ≤ (100/353 : ℝ) := by exact_mod_cast hc
  have hIntAB : IntervalIntegrable d6OuterSlice volume (a : ℝ) (b : ℝ) :=
    (continuousOn_d6OuterSlice.mono (by
      intro u hu
      exact ⟨haR.trans hu.1, hu.2.trans (hbcR.trans hcR)⟩)).intervalIntegrable_of_Icc habR
  have hIntBC : IntervalIntegrable d6OuterSlice volume (b : ℝ) (c : ℝ) :=
    (continuousOn_d6OuterSlice.mono (by
      intro u hu
      exact ⟨(haR.trans habR).trans hu.1, hu.2.trans hcR⟩)).intervalIntegrable_of_Icc hbcR
  exact intervalIntegral.integral_add_adjacent_intervals hIntAB hIntBC

/-- Eight genuine D6 source integrals dominate the finite rational
Darboux mass; each term is charged exactly once. -/
theorem eight_cell_mass_le_actual_D6 :
    (eightCellMass : ℝ) ≤ d6Log := by
  have h0 := d6_rational_cell_integral_lower
    2 (50/227 : ℚ) (73125/320524 : ℚ)
    (by norm_num) (by norm_num) (by norm_num)
  have h1 := d6_rational_cell_integral_lower
    2 (73125/320524 : ℚ) (37825/160262 : ℚ)
    (by norm_num) (by norm_num) (by norm_num)
  have h2 := d6_rational_cell_integral_lower
    2 (37825/160262 : ℚ) (78175/320524 : ℚ)
    (by norm_num) (by norm_num) (by norm_num)
  have h3 := d6_rational_cell_integral_lower
    2 (78175/320524 : ℚ) (20175/80131 : ℚ)
    (by norm_num) (by norm_num) (by norm_num)
  have h4 := d6_rational_cell_integral_lower
    2 (20175/80131 : ℚ) (83225/320524 : ℚ)
    (by norm_num) (by norm_num) (by norm_num)
  have h5 := d6_rational_cell_integral_lower
    2 (83225/320524 : ℚ) (42875/160262 : ℚ)
    (by norm_num) (by norm_num) (by norm_num)
  have h6 := d6_rational_cell_integral_lower
    2 (42875/160262 : ℚ) (88275/320524 : ℚ)
    (by norm_num) (by norm_num) (by norm_num)
  have h7 := d6_rational_cell_integral_lower
    2 (88275/320524 : ℚ) (100/353 : ℚ)
    (by norm_num) (by norm_num) (by norm_num)
  have j1 := join_actual (50/227) (73125/320524) (37825/160262)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have j2 := join_actual (50/227) (37825/160262) (78175/320524)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have j3 := join_actual (50/227) (78175/320524) (20175/80131)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have j4 := join_actual (50/227) (20175/80131) (83225/320524)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have j5 := join_actual (50/227) (83225/320524) (42875/160262)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have j6 := join_actual (50/227) (42875/160262) (88275/320524)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have j7 := join_actual (50/227) (88275/320524) (100/353)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hFull :
      (∫ u in ((50/227 : ℚ) : ℝ)..((100/353 : ℚ) : ℝ), d6OuterSlice u) = d6Log := by
    unfold d6Log
    rw [integral_Ioo_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le
        (by norm_num : (50/227 : ℝ) ≤ 100/353)]
    rfl
  calc
    (eightCellMass : ℝ) =
      ((((73125/320524 - 50/227 : ℚ) * d6CellLower 2 (50/227) (73125/320524)) : ℚ) : ℝ) +
      ((((37825/160262 - 73125/320524 : ℚ) * d6CellLower 2 (73125/320524) (37825/160262)) : ℚ) : ℝ) +
      ((((78175/320524 - 37825/160262 : ℚ) * d6CellLower 2 (37825/160262) (78175/320524)) : ℚ) : ℝ) +
      ((((20175/80131 - 78175/320524 : ℚ) * d6CellLower 2 (78175/320524) (20175/80131)) : ℚ) : ℝ) +
      ((((83225/320524 - 20175/80131 : ℚ) * d6CellLower 2 (20175/80131) (83225/320524)) : ℚ) : ℝ) +
      ((((42875/160262 - 83225/320524 : ℚ) * d6CellLower 2 (83225/320524) (42875/160262)) : ℚ) : ℝ) +
      ((((88275/320524 - 42875/160262 : ℚ) * d6CellLower 2 (42875/160262) (88275/320524)) : ℚ) : ℝ) +
      ((((100/353 - 88275/320524 : ℚ) * d6CellLower 2 (88275/320524) (100/353)) : ℚ) : ℝ) := by
        simp only [eightCellMass, Rat.cast_add]
    _ ≤ (∫ u in ((50/227 : ℚ) : ℝ)..((100/353 : ℚ) : ℝ), d6OuterSlice u) := by
        linarith only [h0, h1, h2, h3, h4, h5, h6, h7, j1, j2, j3, j4, j5, j6, j7]
    _ = d6Log := hFull

/-- Arithmetic certificate for the original D6 support. The exact
rational diagnostic is about 0.115195589311, above 115/1000. -/
theorem eight_cell_rational_arithmetic :
    (115/1000 : ℝ) ≤ (eightCellMass : ℝ) := by
  norm_num [eightCellMass, d6CellLower, d6RationalArgument,
    ImbalancedChen.Certificates.logSeriesLower,
    ImbalancedChen.Certificates.logParameter, Finset.sum_range_succ]

/-- Literal original D6 coefficient bound, conditional only on the
candidate source being successfully elaborated and checked by Lean. -/
theorem actual_d6Log_ge_115_per_1000 :
    (115/1000 : ℝ) ≤ d6Log :=
  eight_cell_rational_arithmetic.trans eight_cell_mass_le_actual_D6

/-- Seven genuine source integrals with the existing /5 normalization.
This is weaker than the required 13/100 and not a seed certificate. -/
theorem partial_lambda_ge_118_per_1000 :
    (118/1000 : ℝ) ≤ lambda := by
  have h0 := Part5OriginalH430EightCellSingletonChain.original_singleton_zero_ge_106_per_1000
  have h1 := Part5OriginalH430EightCellSingletonChain.original_singleton_one_ge_10_per_1000
  have h2 := Part5OriginalH430EightCellSingletonChain.original_singleton_two_ge_53_per_1000
  have h5 := Part5OriginalH430D5TwentyFourCellRational.genuine_twentyfour_cell_D5_ge_171_per_1000
  have h6 := actual_d6Log_ge_115_per_1000
  have h7 := Part5OriginalH430D7EightCellRationalLower.genuine_d7_eight_cell_ge_27_per_1000
  have h8 := Part5OriginalH430D8TwoAffineAdditive.genuine_d8_two_affine_ge_108_per_1000
  rw [lambda_exact_seven_logs]
  linarith

end
end ImbalancedChen.Part5OriginalH430ActualD6EightCellRational
