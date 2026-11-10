import ImbalancedChen.Part5OriginalH430W2UpperWeights

namespace ImbalancedChen.Part5OriginalH430W2UpperCheck29

open Part5OriginalH430W2UpperWeights
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem gamma5 : laneCheck 29 0 = true := by decide

theorem gamma6 : laneCheck 29 1 = true := by decide

theorem gamma7 : laneCheck 29 2 = true := by decide

theorem gamma8 : laneCheck 29 3 = true := by decide

theorem checked (k : Fin 4) : laneCheck 29 k = true := by
  fin_cases k <;> first | exact gamma5 | exact gamma6 | exact gamma7 | exact gamma8

end ImbalancedChen.Part5OriginalH430W2UpperCheck29
