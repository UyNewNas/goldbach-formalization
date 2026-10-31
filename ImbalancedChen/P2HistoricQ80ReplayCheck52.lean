import ImbalancedChen.P2HistoricQ80ReplayData

namespace ImbalancedChen.P2HistoricQ80ReplayData
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
/-- Exact recurrence equality, checked by the ordinary kernel. -/
theorem chunk52_checked : ChunkChecked ⟨52, by decide⟩ := by
  decide +kernel
end ImbalancedChen.P2HistoricQ80ReplayData
