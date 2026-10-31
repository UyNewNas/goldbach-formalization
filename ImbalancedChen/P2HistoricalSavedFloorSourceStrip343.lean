import ImbalancedChen.P2HistoricalSavedFloorBoundedSource

namespace ImbalancedChen.P2HistoricalSavedFloorSourceChecks
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open P2HistoricalSavedFloorFullBinder P2HistoricalSavedFloorFastSource
open P2HistoricalSavedFloorBoundedSource
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original source predicate on local rows 0..3. -/
theorem strip343_chunk00_checked : ∀ j : Fin 4,
    fullSourceRowCheck (chunkRow ⟨17, by decide⟩ 17 (by decide)
      0 4 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  decide +kernel

/-- Exact original source predicate on local rows 4..7. -/
theorem strip343_chunk01_checked : ∀ j : Fin 4,
    fullSourceRowCheck (chunkRow ⟨17, by decide⟩ 17 (by decide)
      4 4 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  decide +kernel

/-- Exact original source predicate on local rows 8..11. -/
theorem strip343_chunk02_checked : ∀ j : Fin 4,
    fullSourceRowCheck (chunkRow ⟨17, by decide⟩ 17 (by decide)
      8 4 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  decide +kernel

/-- Exact original source predicate on local rows 12..15. -/
theorem strip343_chunk03_checked : ∀ j : Fin 4,
    fullSourceRowCheck (chunkRow ⟨17, by decide⟩ 17 (by decide)
      12 4 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  decide +kernel

/-- Exact original source predicate on local rows 16..16. -/
theorem strip343_chunk04_checked : ∀ j : Fin 1,
    fullSourceRowCheck (chunkRow ⟨17, by decide⟩ 17 (by decide)
      16 1 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  decide +kernel

/-- Original public full-strip goal, without numerical evaluation of all rows at once. -/
theorem strip343_checked :
    ∀ j : Fin (512 - firstU (⟨17, by decide⟩ : Fin 186)),
      fullSourceRowCheck (⟨(⟨17, by decide⟩ : Fin 186), j⟩ : Row) = true := by
  have hall : ∀ j : Fin 17,
      fullSourceRowCheck (rowAt ⟨17, by decide⟩ 17 (by decide) j) = true := by
    intro j
    by_cases h0 : j.val < 4
    · exact chunk_covers ⟨17, by decide⟩ 17 (by decide) 0 4 (by decide)
        strip343_chunk00_checked j (by omega) h0
    by_cases h1 : j.val < 8
    · exact chunk_covers ⟨17, by decide⟩ 17 (by decide) 4 4 (by decide)
        strip343_chunk01_checked j (by omega) h1
    by_cases h2 : j.val < 12
    · exact chunk_covers ⟨17, by decide⟩ 17 (by decide) 8 4 (by decide)
        strip343_chunk02_checked j (by omega) h2
    by_cases h3 : j.val < 16
    · exact chunk_covers ⟨17, by decide⟩ 17 (by decide) 12 4 (by decide)
        strip343_chunk03_checked j (by omega) h3
    exact chunk_covers ⟨17, by decide⟩ 17 (by decide) 16 1 (by decide)
      strip343_chunk04_checked j (by omega) (by omega)
  exact StripAssembly.forallFinCast
    (by decide : 512 - firstU (⟨17, by decide⟩ : Fin 186) = 17)
    (fun j => fullSourceRowCheck (⟨(⟨17, by decide⟩ : Fin 186), j⟩ : Row) = true)
    hall

end ImbalancedChen.P2HistoricalSavedFloorSourceChecks
