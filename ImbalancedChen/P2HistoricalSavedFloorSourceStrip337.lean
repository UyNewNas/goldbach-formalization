import ImbalancedChen.P2HistoricalSavedFloorFastSource

namespace ImbalancedChen.P2HistoricalSavedFloorSourceChecks
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open P2HistoricalSavedFloorFullBinder P2HistoricalSavedFloorFastSource
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
/-- Original source-output check, with all source indices and the full
ordinary-plus-defect integer preserved. No stored output is used as an input. -/
theorem strip337_checked :
    ∀ j : Fin (512 - firstU (⟨11, by decide⟩ : Fin 186)),
      fullSourceRowCheck (⟨(⟨11, by decide⟩ : Fin 186), j⟩ : Row) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  decide +kernel
end ImbalancedChen.P2HistoricalSavedFloorSourceChecks
