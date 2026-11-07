import ImbalancedChen.P4AAll22AdditionalActualSuppliers
import ImbalancedChen.P2OriginalFirstIntegralEndpoint

/-!
SOURCE_ONLY / UNCOMPILED. This consumes the actual original first-integral
analytic enclosure and its selected exact rational comparison. It replaces
only the first-integral slot in the original all-22 K ledger. Other quoted
slots and physical-policy identifications remain open.
-/

namespace ImbalancedChen.P4AActualFirstIntegralSelectedK

noncomputable section

open P4AAll22OriginalKLedger20261024zSourceOnly
open P4AAll22AdditionalActualSuppliers20261024zSourceOnly

private theorem selected_upper_real_eq_original_slot :
    (P2OriginalFirstIntegralEndpointSourceOnly.selectedUpperQ : ℝ) =
      7179974843999672947 / 2^73 := by
  norm_num [P2OriginalFirstIntegralEndpointSourceOnly.selectedUpperQ]

/-- The actual source integral pays exactly the frozen first-integral slot. -/
theorem actual_first_integral_le_original_slot :
    actualFirstIntegral ≤ (7179974843999672947 / 2^73 : ℝ) := by
  change P2FirstIntegralSeriesSourceOnly.originalFirstIntegral ≤
    (7179974843999672947 / 2^73 : ℝ)
  rw [← selected_upper_real_eq_original_slot]
  exact P2OriginalFirstIntegralEndpointSourceOnly.originalFirstIntegral_le_selected

/-- Three genuine suppliers now fit their corresponding three original slots. -/
theorem three_supplier_ledger_le_quoted :
    threeSupplierLedger ≤ quotedAll22Raw := by
  rw [threeSupplierLedger_exact_replacement]
  linarith only [twoSupplierLedger_le_quotedAll22Raw,
    actual_first_integral_le_original_slot]

/-- Original rational K budget after replacing the actual first integral once. -/
theorem three_supplier_with_reserves_and_slack_le_K :
    threeSupplierLedger + densityReserve + compilerReserve + exactSlack ≤ currentK := by
  linarith only [three_supplier_ledger_le_quoted, exact_original_budget_identity]

theorem three_supplier_with_reserves_lt_K :
    threeSupplierLedger + densityReserve + compilerReserve < currentK := by
  linarith only [three_supplier_with_reserves_and_slack_le_K, exactSlack_pos]

end

end ImbalancedChen.P4AActualFirstIntegralSelectedK
