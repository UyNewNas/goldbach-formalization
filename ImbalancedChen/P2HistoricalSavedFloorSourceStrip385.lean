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
theorem strip385_chunk00_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨59, by decide⟩ 60 (by decide)
      0 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 16..31. -/
theorem strip385_chunk01_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨59, by decide⟩ 60 (by decide)
      16 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 32..47. -/
theorem strip385_chunk02_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨59, by decide⟩ 60 (by decide)
      32 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 48..59. -/
theorem strip385_chunk03_checked : ∀ j : Fin 12,
    fullSourceRowCheck (chunkRow ⟨59, by decide⟩ 60 (by decide)
      48 12 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Original public full-strip goal, without numerical evaluation of all rows at once. -/
theorem strip385_checked :
    ∀ j : Fin (512 - firstU (⟨59, by decide⟩ : Fin 186)),
      fullSourceRowCheck (⟨(⟨59, by decide⟩ : Fin 186), j⟩ : Row) = true := by
  have hall : ∀ j : Fin 60,
      fullSourceRowCheck (rowAt ⟨59, by decide⟩ 60 (by decide) j) = true := by
    intro j
    by_cases h0 : j.val < 16
    · exact chunk_covers ⟨59, by decide⟩ 60 (by decide) 0 16 (by decide)
        strip385_chunk00_checked j (by omega) h0
    by_cases h1 : j.val < 32
    · exact chunk_covers ⟨59, by decide⟩ 60 (by decide) 16 16 (by decide)
        strip385_chunk01_checked j (by omega) h1
    by_cases h2 : j.val < 48
    · exact chunk_covers ⟨59, by decide⟩ 60 (by decide) 32 16 (by decide)
        strip385_chunk02_checked j (by omega) h2
    exact chunk_covers ⟨59, by decide⟩ 60 (by decide) 48 12 (by decide)
      strip385_chunk03_checked j (by omega) (by omega)
  exact StripAssembly.forallFinCast
    (by decide : 512 - firstU (⟨59, by decide⟩ : Fin 186) = 60)
    (fun j => fullSourceRowCheck (⟨(⟨59, by decide⟩ : Fin 186), j⟩ : Row) = true)
    hall

end ImbalancedChen.P2HistoricalSavedFloorSourceChecks
