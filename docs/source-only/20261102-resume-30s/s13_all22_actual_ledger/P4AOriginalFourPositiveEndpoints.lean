import ImbalancedChen.P4AAll22ActualCompactPositiveBinding
import ImbalancedChen.P4AActualFirstIntegralSelectedK
import ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

All four positive entries are the actual original analytic quantities.
The previously supplied selected first-integral endpoint and the complete
original compact-forest endpoint replace the stale excesses in the older
All22 binding. No numerical endpoint is recomputed in this file.

The compact supplier imports the frozen cached two-million-split candidate.
That inherited finite proof body remains UNEVALUATED. These declarations
therefore give exact proof-source bindings, not a kernel receipt.

The twenty-two signed current-parent savings, their common final policy,
and the two actual total reserves are separate obligations. No theorem
below identifies a scalar expression with that missing physical policy.
-/

namespace ImbalancedChen.P4AOriginalFourPositiveEndpoints

noncomputable section
open scoped BigOperators
open P4AAll22OriginalKLedger20261024zSourceOnly
open P4AAll22AdditionalActualSuppliers20261024zSourceOnly
open P4AAll22ActualCompactPositiveBindingSourceOnly

/-- The complete original Q80 compact endpoint, converted to the unchanged
All22 slot. Every source-forest leaf, including zero-error leaves, is paid
by the imported supplier. No local-charge or total-charge premise occurs. -/
theorem actual_compact_third_le_original_slot :
    actualCompactThird ≤ quotedCompactThird := by
  have h :=
    P2OriginalCompactWholeFunctionalEndpointSourceOnly.original_compact_le_historical_upper
  have heq :
      P2OriginalCompactQ80EncloserSourceOnly.val
          P2OriginalCompactConcreteLoopSourceOnly.historicalUpper = quotedCompactThird := by
    norm_num [P2OriginalCompactQ80EncloserSourceOnly.val,
      P2OriginalCompactQ80EncloserSourceOnly.scale,
      P2OriginalCompactConcreteLoopSourceOnly.historicalUpper, quotedCompactThird]
  rw [heq] at h
  exact h

/-- Literal ordered positive entries: ordinary constant, full U1, complete
compact third, and complete noncompact third tail. -/
def actualPositiveEntries : Fin 4 → ℝ :=
  ![4 / thirdPrefixTheta, actualFirstIntegral, actualCompactThird, actualOriginalThirdTail]

/-- Each actual entry has its original directed upper endpoint. No endpoint
field, estimate hypothesis, integral-value premise or changed constant. -/
theorem actual_positive_entry_le_original (i : Fin 4) :
    actualPositiveEntries i ≤ currentUpperEighteenPositive i := by
  fin_cases i
  · change 4 / thirdPrefixTheta ≤ (2000 / 299 : ℝ)
    exact ordinary_root_normalization.le
  · change actualFirstIntegral ≤ (7179974843999672947 / 2^73 : ℝ)
    exact P4AActualFirstIntegralSelectedK.actual_first_integral_le_original_slot
  · change actualCompactThird ≤ quotedCompactThird
    exact actual_compact_third_le_original_slot
  · change actualOriginalThirdTail ≤ (319683857488126290909150567 / 2^111 : ℝ)
    exact actualOriginalThirdTail_le

theorem actual_positive_entries_sum :
    (∑ i, actualPositiveEntries i) = actualPositiveFour := by
  simp [actualPositiveEntries, actualPositiveFour, Fin.sum_univ_succ, add_assoc]

/-- All four positive terms are supplied together, with the tail used once.
This is the analytic positive side of the ledger, not the full All22 bound. -/
theorem actual_positive_four_le_original :
    actualPositiveFour ≤ ∑ i, currentUpperEighteenPositive i := by
  rw [← actual_positive_entries_sum]
  exact Finset.sum_le_sum fun i _ => actual_positive_entry_le_original i

/-- The same actual positive expression is the ordinary root plus the
original entire third functional. This uses the original compact/tail split
and does not attach an unrelated positive estimate to a different root. -/
theorem actual_positive_four_eq_original_root_add_third :
    actualPositiveFour =
      P4ASameRhoCompact.originalOrdinaryRoot + actualExtendedThirdIdealFunctional := by
  rw [actualPositiveFour_eq_root_compact_tail,
    OriginalThirdFiniteReserveSourceOnly.idealFunctional_eq_compact_add_original_tail]
  unfold actualCompactThird actualOriginalThirdTail
  ring

/-- Equivalent endpoint on the precise original root and entire original
third functional. The selected P112 tail appears once in the positive
endpoint, through its existing actual manuscript-tail upper supplier. -/
theorem original_root_add_third_le_original_positive_sum :
    P4ASameRhoCompact.originalOrdinaryRoot + actualExtendedThirdIdealFunctional ≤
      ∑ i, currentUpperEighteenPositive i := by
  rw [← actual_positive_four_eq_original_root_add_third]
  exact actual_positive_four_le_original

end
end ImbalancedChen.P4AOriginalFourPositiveEndpoints
