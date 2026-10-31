import ImbalancedChen.P2HistoricalSavedFloorStoredTotalFinite
import Mathlib.Tactic.NormNum

/-! UNCOMPILED DRAFT. The unchanged savedQ80 stream, decoded at its original
Q80 scale and divided by four once, fits the adopted replacement payment.
This bounds the discarded saved estimator, not the true removed count.
No source-output equality or analytic bank licence is inferred here. -/

namespace ImbalancedChen.P2HistoricalSavedFloorStoredTotal

open P2HistoricalSavedFloorRowsBinder
open Certificates.PairedV2.FullMask
open Certificates.P2HistoricQ80DefectLookup (Q)
open scoped BigOperators

/-- Exact Chen-quarter value of the complete original saved estimator. -/
theorem saved_quarter_sum_eq :
    (∑ r : Row, ((frozenSavedRow r).savedQ80 : ℚ) / (Q : ℚ) / 4) =
      (5645403422587826010135 / 2417851639229258349412352 : ℚ) := by
  rw [← Finset.sum_div, ← Finset.sum_div, ← Int.cast_sum, frozen_saved_total]
  norm_num [Q]

/-- The exact stream is below the literal adopted replacement loss allowance.
There is no K factor, extra permutation, or additional Chen division. -/
theorem saved_quarter_sum_le_replacement_payment :
    (∑ r : Row, ((frozenSavedRow r).savedQ80 : ℚ) / (Q : ℚ) / 4) ≤
      (466977 / 200000000 : ℚ) := by
  rw [saved_quarter_sum_eq]
  norm_num

set_option maxRecDepth 100000 in
/-- The same inequality in real arithmetic, without an analytic premise. -/
theorem saved_quarter_sum_le_replacement_payment_real :
    (∑ r : Row, ((frozenSavedRow r).savedQ80 : ℝ) / (Q : ℝ) / 4) ≤
      (466977 / 200000000 : ℝ) := by
  rw [← Finset.sum_div, ← Finset.sum_div, ← Int.cast_sum, frozen_saved_total]
  norm_num [Q]

end ImbalancedChen.P2HistoricalSavedFloorStoredTotal
