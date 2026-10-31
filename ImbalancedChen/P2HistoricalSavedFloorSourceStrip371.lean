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
theorem strip371_chunk00_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨45, by decide⟩ 45 (by decide)
      0 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 16..31. -/
theorem strip371_chunk01_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨45, by decide⟩ 45 (by decide)
      16 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 32..44. -/
theorem strip371_chunk02_checked : ∀ j : Fin 13,
    fullSourceRowCheck (chunkRow ⟨45, by decide⟩ 45 (by decide)
      32 13 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Original public full-strip goal, without numerical evaluation of all rows at once. -/
theorem strip371_checked :
    ∀ j : Fin (512 - firstU (⟨45, by decide⟩ : Fin 186)),
      fullSourceRowCheck (⟨(⟨45, by decide⟩ : Fin 186), j⟩ : Row) = true := by
  have hall : ∀ j : Fin 45,
      fullSourceRowCheck (rowAt ⟨45, by decide⟩ 45 (by decide) j) = true := by
    intro j
    by_cases h0 : j.val < 16
    · exact chunk_covers ⟨45, by decide⟩ 45 (by decide) 0 16 (by decide)
        strip371_chunk00_checked j (by omega) h0
    by_cases h1 : j.val < 32
    · exact chunk_covers ⟨45, by decide⟩ 45 (by decide) 16 16 (by decide)
        strip371_chunk01_checked j (by omega) h1
    exact chunk_covers ⟨45, by decide⟩ 45 (by decide) 32 13 (by decide)
      strip371_chunk02_checked j (by omega) (by omega)
  exact StripAssembly.forallFinCast
    (by decide : 512 - firstU (⟨45, by decide⟩ : Fin 186) = 45)
    (fun j => fullSourceRowCheck (⟨(⟨45, by decide⟩ : Fin 186), j⟩ : Row) = true)
    hall

end ImbalancedChen.P2HistoricalSavedFloorSourceChecks
