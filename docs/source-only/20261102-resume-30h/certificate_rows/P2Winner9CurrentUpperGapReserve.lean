import ImbalancedChen.P2Winner9CompleteSeedRetainedFloors
import ImbalancedChen.P4AAll22OriginalKLedger
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Attach the actual whole-seed gap loss to the current production reserve.
The third-functional u/4 expenditure is retained. The new inward gap crop
uses less than u/8, leaving 5u/8 for all other density approximation work.
This allocation does not pay those other errors or the compiler, nor does
it identify the quoted all22 ledger with the physical coefficient.
-/

namespace ImbalancedChen.P2Winner9CurrentUpperGapReserve

noncomputable section

open scoped BigOperators
open ImbalancedChen.P2Winner9CompleteSeedData
open ImbalancedChen.P2Winner9CompleteSeedAnalyticPorts
open ImbalancedChen.P2Winner9CompleteSeedGapReserve
open ImbalancedChen.P2Winner9CompleteSeedRetainedFloors
open ImbalancedChen.P4AAll22OriginalKLedger20261024zSourceOnly

def seedGapShare : ℝ := densityReserve / 8

def seedGapCutoff : ℝ := reserveCutoff seedGapShare

theorem seedGapShare_pos : 0 < seedGapShare := div_pos densityReserve_pos (by norm_num)

theorem seedGapCutoff_pos : 0 < seedGapCutoff := reserveCutoff_pos seedGapShare_pos

/-- Genuine full11026 analytic density loss, now in the original u units. -/
theorem all_actual_seed_gap_loss_paid : familyLoss seedGapCutoff < seedGapShare :=
  common_gap_reserve seedGapShare_pos seedGapCutoff_pos.le le_rfl

theorem actual_seed_retained_mass :
    (∑ i : RowIndex, fullMass i) - seedGapShare <
      ∑ i : RowIndex, retainedMass i seedGapCutoff :=
  complete_family_retained_mass seedGapShare_pos seedGapCutoff_pos.le le_rfl

theorem actual_two_original_floors_retained :
    (((entry row21Index).mixedSelected : ℝ) / 79228162514264337593543950336 +
      ((entry row22Index).mixedSelected : ℝ) / 79228162514264337593543950336) -
        seedGapShare < retainedMass row21Index seedGapCutoff +
          retainedMass row22Index seedGapCutoff :=
  two_original_floors_after_common_crop seedGapShare_pos seedGapCutoff_pos.le le_rfl

/-- The original third u/4 payment is not overwritten or charged again. -/
theorem exact_remaining_density_allocation :
    densityReserve / 4 + seedGapShare + 5 * densityReserve / 8 = densityReserve := by
  unfold seedGapShare
  ring

theorem remaining_density_share_pos : 0 < 5 * densityReserve / 8 := by
  exact div_pos (mul_pos (by norm_num) densityReserve_pos) (by norm_num)

/-- The named actual loss replaces only its allocation, while the remaining
allowance and separate compiler reserve stay visible. The raw ledger remains
the existing quoted production expression, not an asserted physical density. -/
theorem quoted_budget_with_actual_gap_loss :
    quotedAll22Raw + densityReserve / 4 + familyLoss seedGapCutoff +
      5 * densityReserve / 8 + compilerReserve + exactSlack < currentK := by
  have h := all_actual_seed_gap_loss_paid
  have he := exact_original_budget_identity
  have ha := exact_remaining_density_allocation
  linarith

end

end ImbalancedChen.P2Winner9CurrentUpperGapReserve
