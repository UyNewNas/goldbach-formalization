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
theorem strip459_chunk00_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨133, by decide⟩ 136 (by decide)
      0 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 16..31. -/
theorem strip459_chunk01_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨133, by decide⟩ 136 (by decide)
      16 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 32..47. -/
theorem strip459_chunk02_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨133, by decide⟩ 136 (by decide)
      32 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 48..63. -/
theorem strip459_chunk03_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨133, by decide⟩ 136 (by decide)
      48 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 64..79. -/
theorem strip459_chunk04_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨133, by decide⟩ 136 (by decide)
      64 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 80..95. -/
theorem strip459_chunk05_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨133, by decide⟩ 136 (by decide)
      80 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 96..111. -/
theorem strip459_chunk06_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨133, by decide⟩ 136 (by decide)
      96 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 112..127. -/
theorem strip459_chunk07_checked : ∀ j : Fin 16,
    fullSourceRowCheck (chunkRow ⟨133, by decide⟩ 136 (by decide)
      112 16 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Exact original source predicate on local rows 128..135. -/
theorem strip459_chunk08_checked : ∀ j : Fin 8,
    fullSourceRowCheck (chunkRow ⟨133, by decide⟩ 136 (by decide)
      128 8 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  rw [← P2HistoricalLogCache.fastLogBlocked_eq_actualLog]
  decide +kernel

/-- Original public full-strip goal, without numerical evaluation of all rows at once. -/
theorem strip459_checked :
    ∀ j : Fin (512 - firstU (⟨133, by decide⟩ : Fin 186)),
      fullSourceRowCheck (⟨(⟨133, by decide⟩ : Fin 186), j⟩ : Row) = true := by
  have hall : ∀ j : Fin 136,
      fullSourceRowCheck (rowAt ⟨133, by decide⟩ 136 (by decide) j) = true := by
    intro j
    by_cases h0 : j.val < 16
    · exact chunk_covers ⟨133, by decide⟩ 136 (by decide) 0 16 (by decide)
        strip459_chunk00_checked j (by omega) h0
    by_cases h1 : j.val < 32
    · exact chunk_covers ⟨133, by decide⟩ 136 (by decide) 16 16 (by decide)
        strip459_chunk01_checked j (by omega) h1
    by_cases h2 : j.val < 48
    · exact chunk_covers ⟨133, by decide⟩ 136 (by decide) 32 16 (by decide)
        strip459_chunk02_checked j (by omega) h2
    by_cases h3 : j.val < 64
    · exact chunk_covers ⟨133, by decide⟩ 136 (by decide) 48 16 (by decide)
        strip459_chunk03_checked j (by omega) h3
    by_cases h4 : j.val < 80
    · exact chunk_covers ⟨133, by decide⟩ 136 (by decide) 64 16 (by decide)
        strip459_chunk04_checked j (by omega) h4
    by_cases h5 : j.val < 96
    · exact chunk_covers ⟨133, by decide⟩ 136 (by decide) 80 16 (by decide)
        strip459_chunk05_checked j (by omega) h5
    by_cases h6 : j.val < 112
    · exact chunk_covers ⟨133, by decide⟩ 136 (by decide) 96 16 (by decide)
        strip459_chunk06_checked j (by omega) h6
    by_cases h7 : j.val < 128
    · exact chunk_covers ⟨133, by decide⟩ 136 (by decide) 112 16 (by decide)
        strip459_chunk07_checked j (by omega) h7
    exact chunk_covers ⟨133, by decide⟩ 136 (by decide) 128 8 (by decide)
      strip459_chunk08_checked j (by omega) (by omega)
  exact StripAssembly.forallFinCast
    (by decide : 512 - firstU (⟨133, by decide⟩ : Fin 186) = 136)
    (fun j => fullSourceRowCheck (⟨(⟨133, by decide⟩ : Fin 186), j⟩ : Row) = true)
    hall

end ImbalancedChen.P2HistoricalSavedFloorSourceChecks
