import ImbalancedChen.P5ZU1011OriginalSixteenOrdinaryBoxRate

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual ordinary coefficient widths on finitely certified literal H248
single-state intervals. Guards explicitly retain clamp50, every knot,
open atoms and zero exterior. No floor value or kernel bound is supplied.
-/

namespace ImbalancedChen.P5Z.OriginalSixteenOrdinarySingleState

noncomputable section

open U1011OriginalSixteenPolicyBank U1011OriginalSixteenPolicyBank.BoxCertificates
open OriginalSixteenOrdinaryBoxBounds OriginalSixteenOrdinaryBoxRate
open OriginalSixteenTightSwitchedRate
open LiteralH248IntervalBounds LiteralH248IntervalRefinement

theorem ratio_order (p : Policy) (B : Box) (hB : B.Valid) (hg : PositiveGuards p B) :
    ratioLower p B ≤ ratioUpper p B := by
  have hr := (residual_width p B hB).1
  have hwU : 0 < B.hi 3 := hg.1.trans_le (hB 3)
  exact (div_le_div_of_nonneg_left hg.2.le hg.1 (hB 3)).trans
    (div_le_div_of_nonneg_right (sub_nonneg.mp hr) hg.1.le)

/-- Literal finite rational geometry test. This is not an assumed
lookup-value equality or analytic cell-bound conclusion. -/
def SingleState (p : Policy) (B : Box) : Prop :=
  ratioUpper p B ≤ 2 ∨ 5 < ratioLower p B ∨
    (∃ i : Fin 200, grid i.val < lowerQuery (ratioLower p B) ∧
      upperQuery (ratioUpper p B) < grid (i.val + 1)) ∨
    (∃ j : Fin 201, lowerQuery (ratioLower p B) = grid j.val ∧
      upperQuery (ratioUpper p B) = grid j.val)

instance (p : Policy) (B : Box) : Decidable (SingleState p B) := by
  unfold SingleState
  infer_instance

theorem singleState_floor_equal (p : Policy) (B : Box) (hB : B.Valid)
    (hg : PositiveGuards p B) (hs : SingleState p B) : floorLower p B = floorUpper p B := by
  have hord := ratio_order p B hB hg
  rcases hs with hclamp | hext | ⟨i, hL, hU⟩ | ⟨j, hL, hU⟩
  · have hh := exact_clamp_interval hord hclamp
    exact hh.1.trans hh.2.symm
  · have hh := exact_exterior_interval hord hext
    exact hh.1.trans hh.2.symm
  · have hh := exact_open_interval hord i hL hU
    exact hh.1.trans hh.2.symm
  · have hh := exact_knot_interval hord j hL hU
    exact hh.1.trans hh.2.symm

/-- Exact same-state ordinary width. The residual lower guard c is a
literal rational positivity margin; no actual function bound is an input.
The whole actual residual interval is paid, including cap-ridge boxes. -/
theorem ordinary_width (p : Policy) (B : Box) (hB : B.Valid) (hg : PositiveGuards p B)
    (c : ℚ) (hc : 0 < c) (hRc : c ≤ residualLower p B) (hs : SingleState p B) :
    0 ≤ ordinaryUpper p B - ordinaryLower p B ∧
      ordinaryUpper p B - ordinaryLower p B ≤ (10 / c ^ 2) * sideSum B := by
  have hr := residual_width p B hB
  have hRU : residualLower p B ≤ residualUpper p B := sub_nonneg.mp hr.1
  have hRU0 : 0 < residualUpper p B := hg.2.trans_le hRU
  have hF := singleState_floor_equal p B hB hg hs
  have hRange := profileInterval_range (ratio_order p B hB hg)
  have hF0 : 0 ≤ floorLower p B := hRange.1
  have hF1 : floorLower p B ≤ 1 := hRange.2.1.trans hRange.2.2
  have hNum0 : 0 ≤ 4 * (1 - floorLower p B) := by linarith only [hF1]
  have hNum4 : 4 * (1 - floorLower p B) ≤ 4 := by linarith only [hF0]
  have hProd : c ^ 2 ≤ residualLower p B * residualUpper p B := by
    simpa only [pow_two] using mul_le_mul hRc (hRc.trans hRU) hc.le hg.2.le
  have heq : ordinaryUpper p B - ordinaryLower p B =
      (4 * (1 - floorLower p B)) * (residualUpper p B - residualLower p B) /
        (residualLower p B * residualUpper p B) := by
    dsimp only [ordinaryUpper, ordinaryLower]
    rw [← hF]
    field_simp [hg.2.ne', hRU0.ne']
    <;> ring
  rw [heq]
  refine ⟨div_nonneg (mul_nonneg hNum0 hr.1) (mul_nonneg hg.2.le hRU0.le), ?_⟩
  have h1 := div_le_div_of_nonneg_left (mul_nonneg hNum0 hr.1) (pow_pos hc 2) hProd
  have h2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hNum4 hr.1) (pow_nonneg hc.le 2)
  have h3 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hr.2 (by norm_num : (0 : ℚ) ≤ 4)) (pow_nonneg hc.le 2)
  have hh := h1.trans (h2.trans h3)
  convert hh using 1 <;> ring

end

end ImbalancedChen.P5Z.OriginalSixteenOrdinarySingleState
