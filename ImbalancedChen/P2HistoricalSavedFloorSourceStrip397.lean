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
theorem strip397_chunk00_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨71, by decide⟩ 72 (by decide)
      0 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 16..31. -/
theorem strip397_chunk01_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨71, by decide⟩ 72 (by decide)
      16 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 32..47. -/
theorem strip397_chunk02_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨71, by decide⟩ 72 (by decide)
      32 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 48..63. -/
theorem strip397_chunk03_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨71, by decide⟩ 72 (by decide)
      48 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 64..71. -/
theorem strip397_chunk04_checked : ∀ j : Fin 8,
    fullSourceRowCheck (chunkRow ⟨71, by decide⟩ 72 (by decide)
      64 8 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Original public full-strip goal, without numerical evaluation of all rows at once. -/
theorem strip397_checked :
    ∀ j : Fin (512 - firstU (⟨71, by decide⟩ : Fin 186)),
      fullSourceRowCheck (⟨(⟨71, by decide⟩ : Fin 186), j⟩ : Row) = true := by
  have hall : ∀ j : Fin 72,
      fullSourceRowCheck (rowAt ⟨71, by decide⟩ 72 (by decide) j) = true := by
    intro j
    by_cases h0 : j.val < 16
    · exact chunk_covers ⟨71, by decide⟩ 72 (by decide) 0 16 (by decide)
        strip397_chunk00_checked j (by omega) h0
    by_cases h1 : j.val < 32
    · exact chunk_covers ⟨71, by decide⟩ 72 (by decide) 16 16 (by decide)
        strip397_chunk01_checked j (by omega) h1
    by_cases h2 : j.val < 48
    · exact chunk_covers ⟨71, by decide⟩ 72 (by decide) 32 16 (by decide)
        strip397_chunk02_checked j (by omega) h2
    by_cases h3 : j.val < 64
    · exact chunk_covers ⟨71, by decide⟩ 72 (by decide) 48 16 (by decide)
        strip397_chunk03_checked j (by omega) h3
    exact chunk_covers ⟨71, by decide⟩ 72 (by decide) 64 8 (by decide)
      strip397_chunk04_checked j (by omega) (by omega)
  exact StripAssembly.forallFinCast
    (by decide : 512 - firstU (⟨71, by decide⟩ : Fin 186) = 72)
    (fun j => fullSourceRowCheck (⟨(⟨71, by decide⟩ : Fin 186), j⟩ : Row) = true)
    hall

end ImbalancedChen.P2HistoricalSavedFloorSourceChecks
