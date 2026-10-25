import ImbalancedChen.P5U7OriginalScalarCoefficientWidth
import ImbalancedChen.P5U7OriginalStaircaseGeometry

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The actual two-regime rational numerator gap is controlled on every
generated inner cell. The seam-straddling max/min coefficients are
explicitly paid using the common s=2 value, not by kernel continuity alone.
-/

namespace ImbalancedChen.P5U7OriginalInnerNumeratorWidth

noncomputable section

open P2ContinuousSieveRational P5U7OriginalUniformLogTail
open P5U7OriginalScalarCoefficientWidth
open P5U7OriginalStraddlingCells P5U7OriginalStaircaseGeometry

theorem logLower_two (n : ℕ) : logLower n 2 = 0 := by
  simp [logLower, pow_succ]

theorem straddling_width (n : ℕ) (L U : ℚ)
    (hL : 1 ≤ L) (hL2 : L ≤ 2) (hU2 : 2 ≤ U) (hU : U ≤ 132 / 59) :
    0 ≤ max (1 / L) ((1 + logUpper n U) / 2) -
        min (1 / 2) ((1 + logLower n 2) / U) ∧
      max (1 / L) ((1 + logUpper n U) / 2) -
        min (1 / 2) ((1 + logLower n 2) / U) ≤ U - L + rate n := by
  have hLU : L ≤ U := hL2.trans hU2
  have hInv : 1 / U ≤ (1 / 2 : ℚ) :=
    one_div_le_one_div_of_le (by norm_num) hU2
  rw [logLower_two, add_zero, min_eq_right hInv]
  have hFirst := first_width L U hL hLU
  have hSecond := second_width n 2 U (by norm_num) hU2 hU
  rw [logLower_two, add_zero] at hSecond
  constructor
  · exact sub_nonneg.mpr ((sub_nonneg.mp hFirst.1).trans (le_max_left _ _))
  · apply sub_le_iff_le_add.mpr
    apply max_le
    · linarith only [hFirst.2, rate_nonneg n]
    · linarith only [hSecond.2, hL2]

theorem box_numerator_width (B : Box) (n : ℕ)
    (hLo : 1 ≤ B.argLo) (hLU : B.argLo ≤ B.argHi)
    (hHi : B.argHi ≤ 132 / 59) :
    0 ≤ B.numeratorUpper n - B.numeratorLower n ∧
      B.numeratorUpper n - B.numeratorLower n ≤ B.argHi - B.argLo + rate n := by
  by_cases hF : B.argHi ≤ 2
  · have hL2 : B.argLo ≤ 2 := hLU.trans hF
    have hH1 : 1 ≤ B.argHi := hLo.trans hLU
    have hFL : B.firstLo = B.argLo := by
      simp only [Box.firstLo, max_eq_right hLo, min_eq_right hL2]
    have hFH : B.firstHi = B.argHi := by
      simp only [Box.firstHi, min_eq_right hF, max_eq_right hH1]
    simp only [Box.numeratorUpper, Box.numeratorLower, if_pos hF, hFL, hFH]
    have hh := first_width B.argLo B.argHi hLo hLU
    exact ⟨hh.1, by linarith only [hh.2, rate_nonneg n]⟩
  by_cases hS : 2 ≤ B.argLo
  · have hHM : B.argLo ≤ 132 / 59 := hLU.trans hHi
    have hH2 : 2 ≤ B.argHi := hS.trans hLU
    have hSL : B.secondLo = B.argLo := by
      simp only [Box.secondLo, max_eq_right hS, min_eq_right hHM]
    have hSH : B.secondHi = B.argHi := by
      simp only [Box.secondHi, min_eq_right hHi, max_eq_right hH2]
    simp only [Box.numeratorUpper, Box.numeratorLower, if_neg hF, if_pos hS, hSL, hSH]
    exact second_width n B.argLo B.argHi hS hLU hHi
  have hL2 : B.argLo ≤ 2 := (lt_of_not_ge hS).le
  have hH2 : 2 ≤ B.argHi := (lt_of_not_ge hF).le
  have hFL : B.firstLo = B.argLo := by
    simp only [Box.firstLo, max_eq_right hLo, min_eq_right hL2]
  have hFH : B.firstHi = 2 := by
    simp only [Box.firstHi, min_eq_left hH2, max_eq_right (by norm_num : (1 : ℚ) ≤ 2)]
  have hSL : B.secondLo = 2 := by
    simp only [Box.secondLo, max_eq_left hL2,
      min_eq_right (by norm_num : (2 : ℚ) ≤ 132 / 59)]
  have hSH : B.secondHi = B.argHi := by
    simp only [Box.secondHi, min_eq_right hHi, max_eq_right hH2]
  simp only [Box.numeratorUpper, Box.numeratorLower, if_neg hF, if_neg hS,
    hFL, hFH, hSL, hSH]
  exact straddling_width n B.argLo B.argHi hLo hL2 hH2 hHi

/-- Exact corner geometry of the REAL generated inner grid supplies all
argument assumptions of the scalar coefficient theorem. -/
theorem generated_inner_numerator_width (n m : ℕ) (hm : 0 < m)
    {i : Index m} (hi : i ∈ inner m) :
    0 ≤ (cell m i).numeratorUpper n - (cell m i).numeratorLower n ∧
      (cell m i).numeratorUpper n - (cell m i).numeratorLower n ≤
        (cell m i).argHi - (cell m i).argLo + rate n := by
  let B := cell m i
  have hv := cell_valid m hm i
  obtain ⟨ha, hab, hb, hc, hcd⟩ := Box.real_guards hv
  have hlo : ((B.a : ℝ), (B.c : ℝ)) ∈ B.closed :=
    ⟨⟨le_rfl, hab⟩, ⟨le_rfl, hcd⟩⟩
  have hhi : ((B.b : ℝ), (B.d : ℝ)) ∈ B.closed :=
    ⟨⟨hab, le_rfl⟩, ⟨hcd, le_rfl⟩⟩
  have hLoSupport := inner_cell_subset_triangle m hm hi hhi
  have hHiSupport := inner_cell_subset_triangle m hm hi hlo
  have hLoArg : (B.argLo : ℝ) = p5U7OmegaArgument (B.b : ℝ) (B.d : ℝ) := by
    simp only [Box.argLo, p5U7OmegaArgument, Rat.cast_div, Rat.cast_sub, Rat.cast_one]
  have hHiArg : (B.argHi : ℝ) = p5U7OmegaArgument (B.a : ℝ) (B.c : ℝ) := by
    simp only [Box.argHi, p5U7OmegaArgument, Rat.cast_div, Rat.cast_sub, Rat.cast_one]
  have hLoR : (1 : ℝ) ≤ B.argLo := by
    rw [hLoArg]
    exact (p5U7Omega_closed_geometry hLoSupport).2.2.2.2.1
  have hHiR : (B.argHi : ℝ) ≤ 132 / 59 := by
    rw [hHiArg]
    exact (p5U7Omega_closed_geometry hHiSupport).2.2.2.2.2
  have hLUR : (B.argLo : ℝ) ≤ B.argHi := by
    rw [hHiArg]
    exact (Box.argument_bounds hv hlo).1
  exact box_numerator_width B n (by exact_mod_cast hLoR)
    (by exact_mod_cast hLUR) (by exact_mod_cast hHiR)

end

end ImbalancedChen.P5U7OriginalInnerNumeratorWidth
