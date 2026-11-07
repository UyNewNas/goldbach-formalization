import ImbalancedChen.P5ZU1011OriginalSixteenTightSwitchedBoxes

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual rational switched-box widths tend to zero with box side lengths
and the AUTOMATIC method-of-steps mesh error. The clipped argument width
is paid algebraically from genuine coordinate endpoint differences.
-/

namespace ImbalancedChen.P5Z.OriginalSixteenTightSwitchedRate

noncomputable section

open U1011OriginalSixteenPolicyBank.BoxCertificates
open OriginalSixteenSwitchedBoxBounds
open OriginalSixteenTightSwitchedBoxes

def Compact (B : Box) : Prop := ∀ i : Fin 4, a ≤ B.lo i ∧ B.hi i ≤ 59 / 250
def sideSum (B : Box) : ℚ :=
  (B.hi 0 - B.lo 0) + (B.hi 1 - B.lo 1) +
    (B.hi 2 - B.lo 2) + (B.hi 3 - B.lo 3)

theorem sideSum_nonneg (B : Box) (hB : B.Valid) : 0 ≤ sideSum B := by
  dsimp only [sideSum]
  linarith only [hB 0, hB 1, hB 2, hB 3]

theorem z_endpoints (B : Box) (hB : B.Valid) (hc : Compact B) :
    zLower B = B.lo 2 ∧ zUpper B = B.hi 2 := by
  exact ⟨max_eq_right (hc 2).1,
    max_eq_right ((hc 2).1.trans (hB 2))⟩

theorem numerator_endpoints (B : Box) (hB : B.Valid) (hc : Compact B) :
    numeratorLower B = 1 - (B.hi 0 + B.hi 1 + B.hi 2 + B.hi 3) ∧
      numeratorUpper B = 1 - (B.lo 0 + B.lo 1 + B.lo 2 + B.lo 3) ∧
      0 ≤ numeratorLower B ∧ numeratorLower B ≤ numeratorUpper B ∧
      numeratorUpper B ≤ 1 ∧ numeratorUpper B - numeratorLower B = sideSum B := by
  have hL : (0 : ℚ) ≤ 1 - (B.hi 0 + B.hi 1 + B.hi 2 + B.hi 3) := by
    linarith only [(hc 0).2, (hc 1).2, (hc 2).2, (hc 3).2]
  have hLU : 1 - (B.hi 0 + B.hi 1 + B.hi 2 + B.hi 3) ≤
      1 - (B.lo 0 + B.lo 1 + B.lo 2 + B.lo 3) := by
    linarith only [hB 0, hB 1, hB 2, hB 3]
  have hU1 : 1 - (B.lo 0 + B.lo 1 + B.lo 2 + B.lo 3) ≤ 1 := by
    have ha : (0 : ℚ) ≤ a := by norm_num [a]
    linarith only [(hc 0).1, (hc 1).1, (hc 2).1, (hc 3).1, ha]
  have heL : numeratorLower B = 1 - (B.hi 0 + B.hi 1 + B.hi 2 + B.hi 3) := max_eq_right hL
  have heU : numeratorUpper B = 1 - (B.lo 0 + B.lo 1 + B.lo 2 + B.lo 3) :=
    max_eq_right (hL.trans hLU)
  refine ⟨heL, heU, ?_, ?_, ?_, ?_⟩
  · simpa only [heL] using hL
  · simpa only [heL, heU] using hLU
  · simpa only [heU] using hU1
  · rw [heL, heU]
    dsimp only [sideSum]
    ring

private theorem clipped_query_width (B : Box)
    (hr : numeratorLower B / zUpper B ≤ numeratorUpper B / zLower B) :
    queryUpper B - queryLower B ≤ numeratorUpper B / zLower B - numeratorLower B / zUpper B := by
  have hAbs := abs_min_sub_min_le_max (8 : ℚ) (numeratorUpper B / zLower B)
    8 (numeratorLower B / zUpper B)
  have hSpan0 : 0 ≤ numeratorUpper B / zLower B - numeratorLower B / zUpper B :=
    sub_nonneg.mpr hr
  simp only [sub_self, abs_zero, abs_of_nonneg hSpan0, max_eq_right hSpan0] at hAbs
  have hDiff := (le_abs_self (min 8 (numeratorUpper B / zLower B) -
    min 8 (numeratorLower B / zUpper B))).trans hAbs
  have hLo : min 8 (numeratorLower B / zUpper B) ≤ queryLower B := le_max_right _ _
  by_cases hh : min 8 (numeratorUpper B / zLower B) ≤ queryLower B
  · rw [queryUpper, max_eq_left hh, sub_self]
    exact hSpan0
  · rw [queryUpper, max_eq_right (le_of_lt (lt_of_not_ge hh))]
    linarith only [hDiff, hLo]

/-- Explicit true argument-span bound. The compact rational guards are
coordinate endpoint guards, not an assumed argument oscillation. -/
theorem query_width (B : Box) (hB : B.Valid) (hc : Compact B) :
    0 ≤ queryUpper B - queryLower B ∧
      queryUpper B - queryLower B ≤ (1 / a + 1 / a ^ 2) * sideSum B := by
  have ha : (0 : ℚ) < a := by norm_num [a]
  have hz := z_endpoints B hB hc
  have hzL : a ≤ zLower B := le_max_left _ _
  have hzU : a ≤ zUpper B := le_max_left _ _
  have hzL0 : 0 < zLower B := ha.trans_le hzL
  have hzU0 : 0 < zUpper B := ha.trans_le hzU
  have hzLU : zLower B ≤ zUpper B := max_le_max le_rfl (hB 2)
  have hn := numerator_endpoints B hB hc
  have hNL0 := hn.2.2.1
  have hNLU := hn.2.2.2.1
  have hNU1 := hn.2.2.2.2.1
  have hNdiff := hn.2.2.2.2.2
  have hNL1 : numeratorLower B ≤ 1 := hNLU.trans hNU1
  have hr : numeratorLower B / zUpper B ≤ numeratorUpper B / zLower B :=
    (div_le_div_of_nonneg_left hNL0 hzL0 hzLU).trans
      (div_le_div_of_nonneg_right hNLU hzL0.le)
  have hFirst : (numeratorUpper B - numeratorLower B) / zLower B ≤ sideSum B / a := by
    rw [hNdiff]
    exact div_le_div_of_nonneg_left (sideSum_nonneg B hB) ha hzL
  have hInv0 : 0 ≤ 1 / zLower B - 1 / zUpper B :=
    sub_nonneg.mpr (one_div_le_one_div_of_le hzL0 hzLU)
  have hSide2 : zUpper B - zLower B ≤ sideSum B := by
    rw [hz.1, hz.2]
    dsimp only [sideSum]
    linarith only [hB 0, hB 1, hB 3]
  have hSecond : numeratorLower B * (1 / zLower B - 1 / zUpper B) ≤ sideSum B / a ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hNL1 hInv0
    simp only [one_mul] at hh
    have heq : 1 / zLower B - 1 / zUpper B =
        (zUpper B - zLower B) / (zLower B * zUpper B) := by
      field_simp [hzL0.ne', hzU0.ne']
      <;> ring
    rw [heq] at hh
    have hProd : a ^ 2 ≤ zLower B * zUpper B := by
      simpa only [pow_two] using mul_le_mul hzL hzU ha.le hzL0.le
    exact hh.trans ((div_le_div_of_nonneg_left (sub_nonneg.mpr hzLU) (pow_pos ha 2) hProd).trans
      (div_le_div_of_nonneg_right hSide2 (pow_nonneg ha.le 2)))
  have hRaw : numeratorUpper B / zLower B - numeratorLower B / zUpper B =
      (numeratorUpper B - numeratorLower B) / zLower B +
        numeratorLower B * (1 / zLower B - 1 / zUpper B) := by ring
  refine ⟨sub_nonneg.mpr (query_valid B).2.1, ?_⟩
  have hBound := (clipped_query_width B hr).trans (by rw [hRaw]; exact add_le_add hFirst hSecond)
  convert hBound using 1 <;> ring

/-- Both automatic rational switched endpoints converge together on
shrinking compact boxes. All constants are explicit rational expressions. -/
theorem switched_width_rate (m : ℕ) (hm : 0 < m) (B : Box)
    (hB : B.Valid) (hc : Compact B) :
    0 ≤ switchedUpper m B - switchedLower m B ∧
      switchedUpper m B - switchedLower m B ≤
        ((k / a) * ((1 / a + 1 / a ^ 2) / 2) + k / a ^ 2) * sideSum B +
          (3000 * k / a) / (m : ℚ) := by
  have hw := switched_width m hm B hB
  have hq := (query_width B hB hc).2
  have hz := z_endpoints B hB hc
  have hZ : zUpper B - zLower B ≤ sideSum B := by
    rw [hz.1, hz.2]
    dsimp only [sideSum]
    linarith only [hB 0, hB 1, hB 3]
  have hka : (0 : ℚ) ≤ k / a := by norm_num [k, a]
  have hkaa : (0 : ℚ) ≤ k / a ^ 2 := by norm_num [k, a]
  have hQ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hq (by norm_num : (0 : ℚ) ≤ 2)) hka
  have hD := mul_le_mul_of_nonneg_left hZ hkaa
  refine ⟨hw.1, ?_⟩
  have hh : (k / a) * ((queryUpper B - queryLower B) / 2 + 3000 / (m : ℚ)) +
      (k / a ^ 2) * (zUpper B - zLower B) ≤
      (k / a) * (((1 / a + 1 / a ^ 2) * sideSum B) / 2 + 3000 / (m : ℚ)) +
        (k / a ^ 2) * sideSum B := by
    nlinarith only [hQ, hD]
  have hFinal := hw.2.trans hh
  convert hFinal using 1 <;> ring

end

end ImbalancedChen.P5Z.OriginalSixteenTightSwitchedRate
