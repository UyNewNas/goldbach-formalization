import ImbalancedChen.P2HistoricalSavedFloorBoundedSource

namespace ImbalancedChen.P2HistoricalSavedFloorSourceChecks
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open P2HistoricalSavedFloorFullBinder P2HistoricalSavedFloorFastSource
open P2HistoricalSavedFloorBoundedSource
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original source predicate on local rows 0..3. -/
theorem strip341_chunk00_checked : ∀ j : Fin 4,
    fullSourceRowCheck (chunkRow ⟨15, by decide⟩ 15 (by decide)
      0 4 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  decide +kernel

/-- Exact original source predicate on local rows 4..7. -/
theorem strip341_chunk01_checked : ∀ j : Fin 4,
    fullSourceRowCheck (chunkRow ⟨15, by decide⟩ 15 (by decide)
      4 4 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  decide +kernel

/-- Exact original source predicate on local rows 8..11. -/
theorem strip341_chunk02_checked : ∀ j : Fin 4,
    fullSourceRowCheck (chunkRow ⟨15, by decide⟩ 15 (by decide)
      8 4 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  decide +kernel

/-- Exact original source predicate on local rows 12..14. -/
theorem strip341_chunk03_checked : ∀ j : Fin 3,
    fullSourceRowCheck (chunkRow ⟨15, by decide⟩ 15 (by decide)
      12 3 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  decide +kernel

/-- Original public full-strip goal, without numerical evaluation of all rows at once. -/
theorem strip341_checked :
    ∀ j : Fin (512 - firstU (⟨15, by decide⟩ : Fin 186)),
      fullSourceRowCheck (⟨(⟨15, by decide⟩ : Fin 186), j⟩ : Row) = true := by
  have hall : ∀ j : Fin 15,
      fullSourceRowCheck (rowAt ⟨15, by decide⟩ 15 (by decide) j) = true := by
    intro j
    by_cases h0 : j.val < 4
    · exact chunk_covers ⟨15, by decide⟩ 15 (by decide) 0 4 (by decide)
        strip341_chunk00_checked j (by omega) h0
    by_cases h1 : j.val < 8
    · exact chunk_covers ⟨15, by decide⟩ 15 (by decide) 4 4 (by decide)
        strip341_chunk01_checked j (by omega) h1
    by_cases h2 : j.val < 12
    · exact chunk_covers ⟨15, by decide⟩ 15 (by decide) 8 4 (by decide)
        strip341_chunk02_checked j (by omega) h2
    exact chunk_covers ⟨15, by decide⟩ 15 (by decide) 12 3 (by decide)
      strip341_chunk03_checked j (by omega) (by omega)
  exact StripAssembly.forallFinCast
    (by decide : 512 - firstU (⟨15, by decide⟩ : Fin 186) = 15)
    (fun j => fullSourceRowCheck (⟨(⟨15, by decide⟩ : Fin 186), j⟩ : Row) = true)
    hall

end ImbalancedChen.P2HistoricalSavedFloorSourceChecks
