import ImbalancedChen.P2HistoricalSavedFloorBoundedSource

namespace ImbalancedChen.P2HistoricalSavedFloorSourceChecks
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open P2HistoricalSavedFloorFullBinder P2HistoricalSavedFloorFastSource
open P2HistoricalSavedFloorBoundedSource
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original source predicate on local rows 12..15. -/
theorem strip347_chunk03_checked : ∀ j : Fin 4,
    fullSourceRowCheck (chunkRow ⟨21, by decide⟩ 21 (by decide)
      12 4 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  decide +kernel

/-- Exact original source predicate on local rows 16..19. -/
theorem strip347_chunk04_checked : ∀ j : Fin 4,
    fullSourceRowCheck (chunkRow ⟨21, by decide⟩ 21 (by decide)
      16 4 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  decide +kernel

/-- Exact original source predicate on local rows 20..20. -/
theorem strip347_chunk05_checked : ∀ j : Fin 1,
    fullSourceRowCheck (chunkRow ⟨21, by decide⟩ 21 (by decide)
      20 1 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  decide +kernel

end ImbalancedChen.P2HistoricalSavedFloorSourceChecks
