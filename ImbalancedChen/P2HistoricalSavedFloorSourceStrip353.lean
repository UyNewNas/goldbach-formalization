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
theorem strip353_chunk00_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨27, by decide⟩ 27 (by decide)
      0 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 16..26. -/
theorem strip353_chunk01_checked : ∀ j : Fin 11,
    fullSourceRowCheck (chunkRow ⟨27, by decide⟩ 27 (by decide)
      16 11 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Original public full-strip goal, without numerical evaluation of all rows at once. -/
theorem strip353_checked :
    ∀ j : Fin (512 - firstU (⟨27, by decide⟩ : Fin 186)),
      fullSourceRowCheck (⟨(⟨27, by decide⟩ : Fin 186), j⟩ : Row) = true := by
  have hall : ∀ j : Fin 27,
      fullSourceRowCheck (rowAt ⟨27, by decide⟩ 27 (by decide) j) = true := by
    intro j
    by_cases h0 : j.val < 16
    · exact chunk_covers ⟨27, by decide⟩ 27 (by decide) 0 16 (by decide)
        strip353_chunk00_checked j (by omega) h0
    exact chunk_covers ⟨27, by decide⟩ 27 (by decide) 16 11 (by decide)
      strip353_chunk01_checked j (by omega) (by omega)
  exact StripAssembly.forallFinCast
    (by decide : 512 - firstU (⟨27, by decide⟩ : Fin 186) = 27)
    (fun j => fullSourceRowCheck (⟨(⟨27, by decide⟩ : Fin 186), j⟩ : Row) = true)
    hall

end ImbalancedChen.P2HistoricalSavedFloorSourceChecks
