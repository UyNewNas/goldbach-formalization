import ImbalancedChen.P4AOrdinaryRootFirstIntegral
import ImbalancedChen.P4AAll22AdditionalActualSuppliers

/-!
SOURCE ONLY / UNCOMPILED.

Proposed module ImbalancedChen.P4AAll22AdditionalActualSuppliers is
all22_k_ledger/All22AdditionalActualSuppliers.lean. This bridge identifies its
actualFirstIntegral with the nonconstant part of the ordinary canonical root.
No selected decimal endpoint or gain certificate is consumed or recreated.
-/

namespace ImbalancedChen.P4AOrdinaryRootAll22Dictionary20261024zSourceOnly

noncomputable section

open P4AAll22AdditionalActualSuppliers20261024zSourceOnly
open P4AAll22OriginalKLedger20261024zSourceOnly
open P4AOrdinaryRootFirstIntegral20261024zSourceOnly

/-- The actual U1 dictionary and the ordinary root refer to the same integral. -/
theorem originalOrdinaryRoot_eq_constant_add_all22_actualFirstIntegral :
    P4ASameRhoCompact.originalOrdinaryRoot =
      4 / thirdPrefixTheta + actualFirstIntegral := by
  exact originalOrdinaryRoot_eq_constant_add_originalFirstIntegral

theorem all22_actualFirstIntegral_eq_originalOrdinaryRoot_sub_constant :
    actualFirstIntegral = P4ASameRhoCompact.originalOrdinaryRoot - 4 / thirdPrefixTheta := by
  linarith only [originalOrdinaryRoot_eq_constant_add_all22_actualFirstIntegral]

/-- Substituting the actual ordinary root exactly replaces the quoted U1 term.
This equality does not supply the remaining all22 analytic gains or a K bound. -/
theorem threeSupplierLedger_eq_twoSupplierLedger_add_root_correction :
    threeSupplierLedger = twoSupplierLedger +
      (P4ASameRhoCompact.originalOrdinaryRoot - 4 / thirdPrefixTheta -
        7179974843999672947 / 2 ^ 73) := by
  rw [threeSupplierLedger_exact_replacement,
    all22_actualFirstIntegral_eq_originalOrdinaryRoot_sub_constant]

end

end ImbalancedChen.P4AOrdinaryRootAll22Dictionary20261024zSourceOnly
