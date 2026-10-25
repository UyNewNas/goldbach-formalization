import ImbalancedChen.P5U7OriginalInnerNumeratorWidth
import ImbalancedChen.P5U7OriginalBoundaryCostRate
import ImbalancedChen.P5U7OriginalKernelOscillation

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual interval-coefficient width on every generated inner cell. This
combines the genuine clamped two-piece numerator gap, original corner
argument distortion, and the exact reciprocal product-denominator gap.
No cell oscillation or coefficient-width assumption is supplied.
-/

namespace ImbalancedChen.P5U7OriginalInnerCellWidth

noncomputable section

open P5U7OriginalStraddlingCells P5U7OriginalStaircaseGeometry
open P5U7OriginalGridBoundaryArea P5U7OriginalBoundaryCostRate
open P5U7OriginalInnerNumeratorWidth P5U7OriginalUniformLogTail

theorem generated_coordinate_guards (m : ℕ) (hm : 0 < m) (i : Index m) :
    (1 / 5 : ℚ) ≤ (cell m i).a ∧ (cell m i).a ≤ (cell m i).b ∧
      (cell m i).b ≤ 1 ∧ (1 / 5 : ℚ) ≤ (cell m i).c ∧
      (cell m i).c ≤ (cell m i).d ∧ (cell m i).d ≤ 1 := by
  have hv := cell_valid m hm i
  have ha := (mesh_bounds tlo thi (by norm_num [tlo, thi]) m hm i.1 i.1.isLt.le).1
  have hc := (mesh_bounds ulo uhi (by norm_num [ulo, uhi]) m hm i.2 i.2.isLt.le).1
  have hd := (mesh_bounds ulo uhi (by norm_num [ulo, uhi]) m hm
    (i.2.val + 1) (by omega)).2
  refine ⟨?_, hv.2.1, hv.2.2.1.trans (by norm_num), ?_, hv.2.2.2.2, ?_⟩
  · norm_num [tlo] at ha
    exact (by norm_num : (1 / 5 : ℚ) ≤ 59 / 250).trans ha
  · norm_num [ulo] at hc
    exact (by norm_num : (1 / 5 : ℚ) ≤ 59 / 250).trans hc
  · exact hd.trans (by norm_num [uhi])

theorem generated_reciprocal_denominator_gap (m : ℕ) (hm : 0 < m) (i : Index m) :
    0 ≤ 1 / ((cell m i).a * (cell m i).c ^ 2) -
        1 / ((cell m i).b * (cell m i).d ^ 2) ∧
      1 / ((cell m i).a * (cell m i).c ^ 2) -
        1 / ((cell m i).b * (cell m i).d ^ 2) ≤
        15625 * (tStep m + 2 * uStep m) := by
  let B := cell m i
  obtain ⟨ha5, hab, hb1, hc5, hcd, hd1⟩ := generated_coordinate_guards m hm i
  have ha0 : 0 < B.a := lt_of_lt_of_le (by norm_num) ha5
  have hc0 : 0 < B.c := lt_of_lt_of_le (by norm_num) hc5
  have hb0 : 0 < B.b := ha0.trans_le hab
  have hd0 : 0 < B.d := hc0.trans_le hcd
  have hA : (1 / 125 : ℚ) ≤ B.a * B.c ^ 2 := by
    calc
      _ = (1 / 5 : ℚ) * (1 / 5 : ℚ) ^ 2 := by norm_num
      _ ≤ _ := mul_le_mul ha5 (pow_le_pow_left₀ (by norm_num) hc5 2)
        (by positivity) ha0.le
  have hAD : B.a * B.c ^ 2 ≤ B.b * B.d ^ 2 :=
    mul_le_mul hab (pow_le_pow_left₀ hc0.le hcd 2) (by positivity) hb0.le
  have hA0 : 0 < B.a * B.c ^ 2 := by positivity
  have hD0 : 0 < B.b * B.d ^ 2 := by positivity
  have hGap : B.b * B.d ^ 2 - B.a * B.c ^ 2 ≤ tStep m + 2 * uStep m := by
    have hdSq : B.d ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hd0.le hd1 2
    have ha1 : B.a ≤ 1 := hab.trans hb1
    have hsum : B.d + B.c ≤ 2 := by linarith
    have hh1 := mul_le_mul_of_nonneg_left hdSq (sub_nonneg.mpr hab)
    have hh2 := mul_le_mul_of_nonneg_right ha1 (sub_nonneg.mpr hcd)
    have hh3 := mul_le_mul hh2 hsum (by positivity : 0 ≤ B.d + B.c)
      (sub_nonneg.mpr hcd)
    have hwidth := cell_widths m i
    change B.b - B.a = tStep m ∧ B.d - B.c = uStep m at hwidth
    nlinarith only [hh1, hh3, hwidth.1, hwidth.2]
  have hprod : (1 / 15625 : ℚ) ≤ (B.a * B.c ^ 2) * (B.b * B.d ^ 2) := by
    have hh := mul_le_mul hA (hA.trans hAD) (by norm_num : (0 : ℚ) ≤ 1 / 125) hA0.le
    norm_num only [show (1 / 125 : ℚ) * (1 / 125) = 1 / 15625 by norm_num] at hh
    exact hh
  have heq : 1 / (B.a * B.c ^ 2) - 1 / (B.b * B.d ^ 2) =
      (B.b * B.d ^ 2 - B.a * B.c ^ 2) / ((B.a * B.c ^ 2) * (B.b * B.d ^ 2)) := by
    field_simp [hA0.ne', hD0.ne']
    <;> ring
  change 0 ≤ 1 / (B.a * B.c ^ 2) - 1 / (B.b * B.d ^ 2) ∧ _
  rw [heq]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hAD) (mul_pos hA0 hD0).le
  · calc
      _ ≤ (B.b * B.d ^ 2 - B.a * B.c ^ 2) / (1 / 15625) :=
        div_le_div_of_nonneg_left (sub_nonneg.mpr hAD) (by norm_num) hprod
      _ = 15625 * (B.b * B.d ^ 2 - B.a * B.c ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hGap (by norm_num)

theorem generated_inner_argument_span (m : ℕ) (hm : 0 < m)
    {i : Index m} (hi : i ∈ inner m) :
    (cell m i).argHi - (cell m i).argLo ≤ 5 * tStep m + 25 * uStep m := by
  let B := cell m i
  have hv := cell_valid m hm i
  obtain ⟨ha, hab, hb, hc, hcd⟩ := Box.real_guards hv
  have hlo : ((B.a : ℝ), (B.c : ℝ)) ∈ B.closed := ⟨⟨le_rfl, hab⟩, ⟨le_rfl, hcd⟩⟩
  have hhi : ((B.b : ℝ), (B.d : ℝ)) ∈ B.closed := ⟨⟨hab, le_rfl⟩, ⟨hcd, le_rfl⟩⟩
  have hArg := p5U7OmegaArgument_abs_sub_le
    (inner_cell_subset_triangle m hm hi hlo) (inner_cell_subset_triangle m hm hi hhi)
  have hLUR := (Box.argument_bounds hv hlo).1
  have hLoArg : (B.argLo : ℝ) = p5U7OmegaArgument (B.b : ℝ) (B.d : ℝ) := by
    simp only [Box.argLo, p5U7OmegaArgument, Rat.cast_div, Rat.cast_sub, Rat.cast_one]
  have hHiArg : (B.argHi : ℝ) = p5U7OmegaArgument (B.a : ℝ) (B.c : ℝ) := by
    simp only [Box.argHi, p5U7OmegaArgument, Rat.cast_div, Rat.cast_sub, Rat.cast_one]
  rw [← hHiArg, ← hLoArg] at hArg
  rw [← hHiArg] at hLUR
  rw [abs_of_nonneg (sub_nonneg.mpr hLUR),
    abs_of_nonpos (sub_nonpos.mpr hab), abs_of_nonpos (sub_nonpos.mpr hcd)] at hArg
  have hwT : (B.b : ℝ) - B.a = (tStep m : ℝ) := by exact_mod_cast (cell_widths m i).1
  have hwU : (B.d : ℝ) - B.c = (uStep m : ℝ) := by exact_mod_cast (cell_widths m i).2
  have hh : (B.argHi : ℝ) - B.argLo ≤ 5 * (tStep m : ℝ) + 25 * (uStep m : ℝ) := by
    linarith only [hArg, hwT, hwU]
  exact_mod_cast hh

/-- Explicit actual interval coefficient-width rate, with the original
denominator correction and seam-straddling interval dependence paid. -/
theorem generated_inner_cell_width (n m : ℕ) (hm : 0 < m)
    {i : Index m} (hi : i ∈ inner m) :
    0 ≤ (cell m i).upper n - (cell m i).lower n ∧
      (cell m i).upper n - (cell m i).lower n ≤
        40000 * (tStep m + uStep m) + 125 * rate n := by
  let B := cell m i
  have hv := cell_valid m hm i
  have hNum := generated_inner_numerator_width n m hm hi
  have hSpan := generated_inner_argument_span m hm hi
  have hRec := generated_reciprocal_denominator_gap m hm i
  have hn0 := Box.numerators_nonneg B n
  have hn1 := numeratorUpper_le_one B n
  have hnLo1 : B.numeratorLower n ≤ 1 := by linarith only [hNum.1, hn1]
  have ha0 : 0 < B.a := hv.1
  have hc0 : 0 < B.c := hv.2.2.2.1
  have hA0 : 0 < B.a * B.c ^ 2 := by positivity
  have hD0 : 0 < B.b * B.d ^ 2 := by
    have hb0 := ha0.trans_le hv.2.1
    have hd0 := hc0.trans_le hv.2.2.2.2
    positivity
  have hA : (1 / 125 : ℚ) ≤ B.a * B.c ^ 2 := by
    obtain ⟨ha5, _, _, hc5, _, _⟩ := generated_coordinate_guards m hm i
    calc
      _ = (1 / 5 : ℚ) * (1 / 5 : ℚ) ^ 2 := by norm_num
      _ ≤ _ := mul_le_mul ha5 (pow_le_pow_left₀ (by norm_num) hc5 2)
        (by positivity) ha0.le
  have hTerm1 : (B.numeratorUpper n - B.numeratorLower n) / (B.a * B.c ^ 2) ≤
      125 * (B.argHi - B.argLo + rate n) := by
    calc
      _ ≤ (B.numeratorUpper n - B.numeratorLower n) / (1 / 125) :=
        div_le_div_of_nonneg_left hNum.1 (by norm_num) hA
      _ = 125 * (B.numeratorUpper n - B.numeratorLower n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hNum.2 (by norm_num)
  have hTerm2 : B.numeratorLower n *
      (1 / (B.a * B.c ^ 2) - 1 / (B.b * B.d ^ 2)) ≤
      15625 * (tStep m + 2 * uStep m) := by
    have hh := mul_le_mul hnLo1 hRec.2 hRec.1 zero_le_one
    simpa only [one_mul] using hh
  have heq : B.upper n - B.lower n =
      (B.numeratorUpper n - B.numeratorLower n) / (B.a * B.c ^ 2) +
        B.numeratorLower n * (1 / (B.a * B.c ^ 2) - 1 / (B.b * B.d ^ 2)) := by
    unfold Box.upper Box.lower
    field_simp [hA0.ne', hD0.ne']
    <;> ring
  change 0 ≤ B.upper n - B.lower n ∧ _
  rw [heq]
  constructor
  · exact add_nonneg (div_nonneg hNum.1 hA0.le) (mul_nonneg hn0.1 hRec.1)
  · have hSteps := step_nonneg m
    nlinarith only [hTerm1, hTerm2, hSpan, hSteps.1, hSteps.2]

end

end ImbalancedChen.P5U7OriginalInnerCellWidth
