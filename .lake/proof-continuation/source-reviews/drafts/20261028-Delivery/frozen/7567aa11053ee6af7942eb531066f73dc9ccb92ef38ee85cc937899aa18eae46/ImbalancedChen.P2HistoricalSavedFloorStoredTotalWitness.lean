import ImbalancedChen.P2HistoricalSavedFloorRowsBinder

/-!
Closed source candidate for the literal historical saved-floor integer total.
This only sums the frozen Q80 fields. Those fields include positive defect
credits, so this theorem supplies no ordinary-only or analytic lower bound.
The source has not been compiled or evaluated in this author task.
-/

namespace ImbalancedChen.P2HistoricalSavedFloorStoredTotalWitness

open scoped BigOperators
open Certificates.PairedV2.FullMask
open P2HistoricalSavedFloorRowsBinder

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The kernel reduces the existing 17,572 literal row fields, the existing
dependent `Row` enumeration, and the existing stated aggregate. No extra
numeric table or external equality hypothesis is introduced here. -/
theorem frozen_saved_integer_total :
    (∑ r : Row, (frozenSavedRow r).savedQ80) = sourceSavedFloorTotal := by
  decide +kernel

/-- Discharge the Boolean premise of the existing decoded-total theorem. -/
theorem storedTotalCheck_true : storedTotalCheck = true := by
  unfold storedTotalCheck
  exact decide_eq_true frozen_saved_integer_total

theorem frozen_saved_total_decoded :
    (∑ r : Row, decodeQ80 (frozenSavedRow r).savedQ80) =
      decodeQ80 sourceSavedFloorTotal := by
  exact checked_stored_total_decode storedTotalCheck_true

end ImbalancedChen.P2HistoricalSavedFloorStoredTotalWitness
