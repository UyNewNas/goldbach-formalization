import ImbalancedChen.P5ZU1011OriginalSixteenTightSwitchedRate
import ImbalancedChen.P5ZU1011LiteralH248IntervalRefinement

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual ORIGINAL16 correlated residual endpoints and ratio interval widths.
These are the concrete crossed cap endpoints, including the distinct W
policy, not a supplied Lipschitz envelope or desired cell-bound premise.
-/

namespace ImbalancedChen.P5Z.OriginalSixteenOrdinaryBoxRate

noncomputable section

open scoped BigOperators
open P2OriginalFourthCapProducerInterface
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenPolicyBank.BoxCertificates
open OriginalSixteenOrdinaryBoxBounds OriginalSixteenSwitchedBoxBounds
open OriginalSixteenTightSwitchedRate
open LiteralH248IntervalBounds

theorem selected_width (p : Policy) (B : Box) (hB : B.Valid) :
    0 ≤ selectedMassQ p B.hi - selectedMassQ p B.lo ∧
      selectedMassQ p B.hi - selectedMassQ p B.lo ≤ sideSum B := by
  have heq : selectedMassQ p B.hi - selectedMassQ p B.lo =
      ∑ i : Fin 4, if Selected p i then B.hi i - B.lo i else 0 := by
    simp only [selectedMassQ, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hs : Selected p i <;> simp only [hs, if_true, if_false, sub_self]
  rw [heq]
  constructor
  · exact Finset.sum_nonneg (fun i _ => by
      by_cases hs : Selected p i <;> simp only [hs, if_true, if_false]
      · exact sub_nonneg.mpr (hB i)
      · exact le_rfl)
  · have hh : (∑ i : Fin 4, if Selected p i then B.hi i - B.lo i else 0) ≤
        ∑ i : Fin 4, (B.hi i - B.lo i) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hs : Selected p i <;> simp only [hs, if_true, if_false]
      · exact le_rfl
      · exact sub_nonneg.mpr (hB i)
    convert hh using 1
    simp only [sideSum, Fin.sum_univ_succ]
    <;> ring

theorem cap_width (p : Policy) (B : Box) (hB : B.Valid) :
    0 ≤ capUpper p B - capLower p B ∧
      capUpper p B - capLower p B ≤ (3 / 2 : ℚ) * sideSum B := by
  have hs := selected_width p B hB
  have hsmono : selectedMassQ p B.lo ≤ selectedMassQ p B.hi := sub_nonneg.mp hs.1
  by_cases hp : p.val < 15
  · simp only [capUpper, capLower, if_pos hp]
    have hA : (1 + selectedMassQ p B.lo) / 2 ≤ (1 + selectedMassQ p B.hi) / 2 := by
      linarith only [hsmono]
    have hC : (57 / 64 : ℚ) - (3 / 2 : ℚ) * selectedMassQ p B.hi ≤
        57 / 64 - (3 / 2 : ℚ) * selectedMassQ p B.lo := by linarith only [hsmono]
    have hMono := min_le_min hA hC
    have hAbs := abs_min_sub_min_le_max
      ((1 + selectedMassQ p B.hi) / 2) ((57 / 64 : ℚ) - (3 / 2 : ℚ) * selectedMassQ p B.lo)
      ((1 + selectedMassQ p B.lo) / 2) ((57 / 64 : ℚ) - (3 / 2 : ℚ) * selectedMassQ p B.hi)
    have hAdiff : (1 + selectedMassQ p B.hi) / 2 - (1 + selectedMassQ p B.lo) / 2 =
        (selectedMassQ p B.hi - selectedMassQ p B.lo) / 2 := by ring
    have hCdiff : (57 / 64 : ℚ) - (3 / 2 : ℚ) * selectedMassQ p B.lo -
        (57 / 64 - (3 / 2 : ℚ) * selectedMassQ p B.hi) =
        (3 / 2 : ℚ) * (selectedMassQ p B.hi - selectedMassQ p B.lo) := by ring
    rw [abs_of_nonneg (sub_nonneg.mpr hMono), hAdiff, hCdiff,
      abs_of_nonneg (div_nonneg hs.1 (by norm_num : (0 : ℚ) ≤ 2)),
      abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℚ) ≤ 3 / 2) hs.1)] at hAbs
    have hMax : max ((selectedMassQ p B.hi - selectedMassQ p B.lo) / 2)
        ((3 / 2 : ℚ) * (selectedMassQ p B.hi - selectedMassQ p B.lo)) ≤
        (3 / 2 : ℚ) * sideSum B := by
      apply max_le <;> linarith only [hs.1, hs.2]
    exact ⟨sub_nonneg.mpr hMono, hAbs.trans hMax⟩
  · simp only [capUpper, capLower, if_neg hp]
    have h2 : B.hi 2 - B.lo 2 ≤ sideSum B := by
      dsimp only [sideSum]
      linarith only [hB 0, hB 1, hB 3]
    have h0 := sideSum_nonneg B hB
    constructor <;> linarith only [hB 2, h2, h0]

theorem prefix_endpoints (B : Box) :
    prefixPiece.lower B.lo B.hi = B.lo 0 + B.lo 1 + B.lo 2 + B.lo 3 ∧
      prefixPiece.upper B.lo B.hi = B.hi 0 + B.hi 1 + B.hi 2 + B.hi 3 := by
  constructor <;>
    norm_num [prefixPiece, Affine.lower, Affine.upper, Affine.neg, Fin.sum_univ_succ] <;> ring

/-- The genuine original16 residual interval has width at most 5/2
times the coordinate side sum, including both branches of every min. -/
theorem residual_width (p : Policy) (B : Box) (hB : B.Valid) :
    0 ≤ residualUpper p B - residualLower p B ∧
      residualUpper p B - residualLower p B ≤ (5 / 2 : ℚ) * sideSum B := by
  have hc := cap_width p B hB
  have hp := prefix_endpoints B
  have hs := sideSum_nonneg B hB
  have heq : residualUpper p B - residualLower p B =
      capUpper p B - capLower p B + sideSum B := by
    simp only [residualUpper, residualLower, hp.1, hp.2, sideSum]
    ring
  rw [heq]
  constructor <;> linarith only [hc.1, hc.2, hs]

theorem residualUpper_le_one (p : Policy) (B : Box) (hB : B.Valid) (hc : Compact B) :
    residualUpper p B ≤ 1 := by
  have ha : (0 : ℚ) ≤ a := by norm_num [a]
  have hLo : ∀ i : Fin 4, 0 ≤ B.lo i := fun i => ha.trans (hc i).1
  have hSel : 0 ≤ selectedMassQ p B.lo := by
    unfold selectedMassQ
    apply Finset.sum_nonneg
    intro i _
    by_cases hs : Selected p i <;> simp only [hs, if_true, if_false]
    · exact hLo i
    · exact le_rfl
  have hCap : capUpper p B ≤ 1 := by
    by_cases hp : p.val < 15
    · simp only [capUpper, if_pos hp]
      exact (min_le_right _ _).trans (by linarith only [hSel])
    · simp only [capUpper, if_neg hp]
      linarith only [hLo 2]
  have hp := (prefix_endpoints B).1
  simp only [residualUpper, hp]
  linarith only [hCap, hLo 0, hLo 1, hLo 2, hLo 3]

/-- Actual ratio endpoint width from the concrete original cap circuit.
Only finite coordinate/positive residual guards are inputs. -/
theorem ratio_width (p : Policy) (B : Box) (hB : B.Valid) (hc : Compact B)
    (hg : PositiveGuards p B) :
    0 ≤ ratioUpper p B - ratioLower p B ∧
      ratioUpper p B - ratioLower p B ≤ (5 / (2 * a) + 1 / a ^ 2) * sideSum B := by
  have ha : (0 : ℚ) < a := by norm_num [a]
  have hwL := (hc 3).1
  have hwU : a ≤ B.hi 3 := hwL.trans (hB 3)
  have hwL0 : 0 < B.lo 3 := ha.trans_le hwL
  have hwU0 : 0 < B.hi 3 := ha.trans_le hwU
  have hr := residual_width p B hB
  have hrOrd : residualLower p B ≤ residualUpper p B := sub_nonneg.mp hr.1
  have hrU1 := residualUpper_le_one p B hB hc
  have hrL1 := hrOrd.trans hrU1
  have hInv : 0 ≤ 1 / B.lo 3 - 1 / B.hi 3 :=
    sub_nonneg.mpr (one_div_le_one_div_of_le hwL0 (hB 3))
  have hFirst : (residualUpper p B - residualLower p B) / B.lo 3 ≤
      ((5 / 2 : ℚ) * sideSum B) / a :=
    (div_le_div_of_nonneg_left hr.1 ha hwL).trans (div_le_div_of_nonneg_right hr.2 ha.le)
  have hSide : B.hi 3 - B.lo 3 ≤ sideSum B := by
    dsimp only [sideSum]
    linarith only [hB 0, hB 1, hB 2]
  have hSecond : residualLower p B * (1 / B.lo 3 - 1 / B.hi 3) ≤ sideSum B / a ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hrL1 hInv
    simp only [one_mul] at hh
    have heq : 1 / B.lo 3 - 1 / B.hi 3 =
        (B.hi 3 - B.lo 3) / (B.lo 3 * B.hi 3) := by
      field_simp [hwL0.ne', hwU0.ne']
      <;> ring
    rw [heq] at hh
    have hProd : a ^ 2 ≤ B.lo 3 * B.hi 3 := by
      simpa only [pow_two] using mul_le_mul hwL hwU ha.le hwL0.le
    exact hh.trans ((div_le_div_of_nonneg_left (sub_nonneg.mpr (hB 3)) (pow_pos ha 2) hProd).trans
      (div_le_div_of_nonneg_right hSide (pow_nonneg ha.le 2)))
  have heq : ratioUpper p B - ratioLower p B =
      (residualUpper p B - residualLower p B) / B.lo 3 +
        residualLower p B * (1 / B.lo 3 - 1 / B.hi 3) := by
    dsimp only [ratioUpper, ratioLower]
    ring
  have hRatio : ratioLower p B ≤ ratioUpper p B :=
    (div_le_div_of_nonneg_left hg.2.le hwL0 (hB 3)).trans
      (div_le_div_of_nonneg_right hrOrd hwL0.le)
  refine ⟨sub_nonneg.mpr hRatio, ?_⟩
  have hh : ratioUpper p B - ratioLower p B ≤
      ((5 / 2 : ℚ) * sideSum B) / a + sideSum B / a ^ 2 := by
    rw [heq]
    exact add_le_add hFirst hSecond
  convert hh using 1 <;> ring

end

end ImbalancedChen.P5Z.OriginalSixteenOrdinaryBoxRate
