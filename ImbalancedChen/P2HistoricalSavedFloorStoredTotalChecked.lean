import ImbalancedChen.P2HistoricalSavedFloorStoredTotalFinite
import ImbalancedChen.P2HistoricalSavedFloorStoredTotalCheckCore

namespace ImbalancedChen.P2HistoricalSavedFloorStoredTotal
open P2HistoricalSavedFloorRowsBinder

/-- The original Boolean goal, with no changed data, domain, or assumptions. -/
theorem stored_total_checked : storedTotalCheck = true := by
  unfold storedTotalCheck
  exact decide_eq_true frozen_saved_total

end ImbalancedChen.P2HistoricalSavedFloorStoredTotal
