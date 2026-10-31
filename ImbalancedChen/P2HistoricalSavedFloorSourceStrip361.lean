import ImbalancedChen.P2HistoricalSavedFloorBoundedSource
import ImbalancedChen.P2HistoricalLogCacheBlocked

namespace ImbalancedChen.P2HistoricalSavedFloorSourceChecks
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open P2HistoricalSavedFloorFullBinder P2HistoricalSavedFloorFastSource
open P2HistoricalSavedFloorBoundedSource
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original source predicate on local rows 0..15. -/
theorem strip361_chunk00_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨35, by decide⟩ 35 (by decide)
      0 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 16..31. -/
theorem strip361_chunk01_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨35, by decide⟩ 35 (by decide)
      16 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 32..34. -/
theorem strip361_chunk02_checked : ∀ j : Fin 3,
    fullSourceRowCheck (chunkRow ⟨35, by decide⟩ 35 (by decide)
      32 3 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Original public full-strip goal, without numerical evaluation of all rows at once. -/
theorem strip361_checked :
    ∀ j : Fin (512 - firstU (⟨35, by decide⟩ : Fin 186)),
      fullSourceRowCheck (⟨(⟨35, by decide⟩ : Fin 186), j⟩ : Row) = true := by
  have hall : ∀ j : Fin 35,
      fullSourceRowCheck (rowAt ⟨35, by decide⟩ 35 (by decide) j) = true := by
    intro j
    by_cases h0 : j.val < 16
    · exact chunk_covers ⟨35, by decide⟩ 35 (by decide) 0 16 (by decide)
        strip361_chunk00_checked j (by omega) h0
    by_cases h1 : j.val < 32
    · exact chunk_covers ⟨35, by decide⟩ 35 (by decide) 16 16 (by decide)
        strip361_chunk01_checked j (by omega) h1
    exact chunk_covers ⟨35, by decide⟩ 35 (by decide) 32 3 (by decide)
      strip361_chunk02_checked j (by omega) (by omega)
  exact StripAssembly.forallFinCast
    (by decide : 512 - firstU (⟨35, by decide⟩ : Fin 186) = 35)
    (fun j => fullSourceRowCheck (⟨(⟨35, by decide⟩ : Fin 186), j⟩ : Row) = true)
    hall

end ImbalancedChen.P2HistoricalSavedFloorSourceChecks
