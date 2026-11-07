import ImbalancedChen.P4AOrdinaryRootAll22Dictionary
import ImbalancedChen.Part4ActualThirdFiniteDensityReserve

/-!
SOURCEONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The ordinary root / full first-integral identity and its actual compact
physical-rho attachment are already sourced by P4AOrdinaryRootFirstIntegral,
P4AOrdinaryRootAll22Dictionary and P4AOriginalRootPhysicalSeriesLedger.
This file does not duplicate those proofs.  It consumes their exact root
dictionary and binds the next actual positive analytic object: the original
compact third integral.  The original all22 gain list, actual tail and
two-chart slot-5 saving are retained, with replacements made once each.

There is no sharp compact-third endpoint premise.  Its full difference
from the quoted endpoint remains explicit on the right of the K ledger.
-/

namespace ImbalancedChen.P4AAll22ActualCompactPositiveBindingSourceOnly

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P4AAll22OriginalKLedger20261024zSourceOnly
open P4AAll22AdditionalActualSuppliers20261024zSourceOnly
open P4AOrdinaryRootAll22Dictionary20261024zSourceOnly

/-- The actual original compact third integral, retaining its original
old-cube gate and the complementary face z=1/100. -/
def actualCompactThird : ℝ :=
  OriginalThirdFiniteReserveSourceOnly.originalCompactThirdCorrection

def quotedCompactThird : ℝ := 144590669409566793572719 / 2^80

/-- The complete actual four-positive-term expression now exposed by the
root/U1 dictionary and the original actual compact and tail suppliers. -/
def actualPositiveFour : ℝ :=
  4 / thirdPrefixTheta + actualFirstIntegral + actualCompactThird +
    actualOriginalThirdTail

theorem actualCompactThird_literal :
    actualCompactThird =
      ∫ t in actualExtendedThirdClosedOrderRegion thirdPrefixRho \
          actualExtendedThirdClosedOrderRegion (1 / 100),
        actualExtendedThirdGatedKernel 0 (t 0) (t 1) (t 2) := rfl

/-- The actual full U1 belongs to the same ordinary root; it is counted
once and has the manuscript's 4/Theta normalization. -/
theorem actualPositiveFour_eq_root_compact_tail :
    actualPositiveFour =
      P4ASameRhoCompact.originalOrdinaryRoot + actualCompactThird +
        actualOriginalThirdTail := by
  rw [originalOrdinaryRoot_eq_constant_add_all22_actualFirstIntegral]
  unfold actualPositiveFour
  ring

/-- The additional actual compact term replaces only the quoted compact
term; no sign for their difference is asserted. -/
def compactThirdExcess : ℝ := actualCompactThird - quotedCompactThird

def fourSupplierLedger : ℝ :=
  threeSupplierLedger - quotedCompactThird + actualCompactThird

theorem fourSupplierLedger_exact_replacement :
    fourSupplierLedger = threeSupplierLedger + compactThirdExcess := by
  unfold fourSupplierLedger compactThirdExcess
  ring

/-- The exact all22 positive-minus-saving expression after the currently
available actual substitutions.  Other saving entries remain quoted. -/
theorem fourSupplierLedger_eq_actual_positive_minus_remaining_savings :
    fourSupplierLedger =
      actualPositiveFour - (∑ i, currentUpperEighteenGains i) -
        (∑ i, finalFourGains i) +
          640339 / 15210735000 - actualCoarseSecondSaving := by
  unfold fourSupplierLedger threeSupplierLedger twoSupplierLedger
    quotedCompactThird actualPositiveFour
  ring

/-- This exact root-correction form identifies both actual positive
replacements against the frozen original K expression. -/
theorem fourSupplierLedger_eq_twoSupplierLedger_add_actual_corrections :
    fourSupplierLedger = twoSupplierLedger +
      (P4ASameRhoCompact.originalOrdinaryRoot - 4 / thirdPrefixTheta -
        7179974843999672947 / 2^73) + compactThirdExcess := by
  rw [fourSupplierLedger_exact_replacement,
    threeSupplierLedger_eq_twoSupplierLedger_add_root_correction]

/-- The two unproved sharp positive enclosures remain on the right in
full.  This is a bounded algebraic ledger, not a final K inequality. -/
theorem fourSupplierLedger_reserved_le_K_plus_unpaid_excesses :
    fourSupplierLedger + densityReserve + compilerReserve + exactSlack ≤
      currentK + firstIntegralCoarseExcess + compactThirdExcess := by
  rw [fourSupplierLedger_exact_replacement]
  linarith only [threeSupplierLedger_reserved_le_K_plus_explicit_excess]

end
end ImbalancedChen.P4AAll22ActualCompactPositiveBindingSourceOnly
