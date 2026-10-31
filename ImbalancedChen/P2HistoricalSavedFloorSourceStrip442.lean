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
theorem strip442_chunk00_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨116, by decide⟩ 118 (by decide)
      0 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 16..31. -/
theorem strip442_chunk01_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨116, by decide⟩ 118 (by decide)
      16 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 32..47. -/
theorem strip442_chunk02_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨116, by decide⟩ 118 (by decide)
      32 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 48..63. -/
theorem strip442_chunk03_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨116, by decide⟩ 118 (by decide)
      48 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 64..79. -/
theorem strip442_chunk04_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨116, by decide⟩ 118 (by decide)
      64 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 80..95. -/
theorem strip442_chunk05_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨116, by decide⟩ 118 (by decide)
      80 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 96..111. -/
theorem strip442_chunk06_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨116, by decide⟩ 118 (by decide)
      96 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 112..117. -/
theorem strip442_chunk07_checked : ∀ j : Fin 6,
    fullSourceRowCheck (chunkRow ⟨116, by decide⟩ 118 (by decide)
      112 6 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Original public full-strip goal, without numerical evaluation of all rows at once. -/
theorem strip442_checked :
    ∀ j : Fin (512 - firstU (⟨116, by decide⟩ : Fin 186)),
      fullSourceRowCheck (⟨(⟨116, by decide⟩ : Fin 186), j⟩ : Row) = true := by
  have hall : ∀ j : Fin 118,
      fullSourceRowCheck (rowAt ⟨116, by decide⟩ 118 (by decide) j) = true := by
    intro j
    by_cases h0 : j.val < 16
    · exact chunk_covers ⟨116, by decide⟩ 118 (by decide) 0 16 (by decide)
        strip442_chunk00_checked j (by omega) h0
    by_cases h1 : j.val < 32
    · exact chunk_covers ⟨116, by decide⟩ 118 (by decide) 16 16 (by decide)
        strip442_chunk01_checked j (by omega) h1
    by_cases h2 : j.val < 48
    · exact chunk_covers ⟨116, by decide⟩ 118 (by decide) 32 16 (by decide)
        strip442_chunk02_checked j (by omega) h2
    by_cases h3 : j.val < 64
    · exact chunk_covers ⟨116, by decide⟩ 118 (by decide) 48 16 (by decide)
        strip442_chunk03_checked j (by omega) h3
    by_cases h4 : j.val < 80
    · exact chunk_covers ⟨116, by decide⟩ 118 (by decide) 64 16 (by decide)
        strip442_chunk04_checked j (by omega) h4
    by_cases h5 : j.val < 96
    · exact chunk_covers ⟨116, by decide⟩ 118 (by decide) 80 16 (by decide)
        strip442_chunk05_checked j (by omega) h5
    by_cases h6 : j.val < 112
    · exact chunk_covers ⟨116, by decide⟩ 118 (by decide) 96 16 (by decide)
        strip442_chunk06_checked j (by omega) h6
    exact chunk_covers ⟨116, by decide⟩ 118 (by decide) 112 6 (by decide)
      strip442_chunk07_checked j (by omega) (by omega)
  exact StripAssembly.forallFinCast
    (by decide : 512 - firstU (⟨116, by decide⟩ : Fin 186) = 118)
    (fun j => fullSourceRowCheck (⟨(⟨116, by decide⟩ : Fin 186), j⟩ : Row) = true)
    hall

end ImbalancedChen.P2HistoricalSavedFloorSourceChecks
