import ImbalancedChen.P2HistoricalSavedFloorBoundedSource

namespace ImbalancedChen.P2HistoricalSavedFloorSourceChecks
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open P2HistoricalSavedFloorFullBinder P2HistoricalSavedFloorFastSource
open P2HistoricalSavedFloorBoundedSource
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Exact original source predicate on local rows 0..3. -/
theorem strip348_chunk00_checked : ∀ j : Fin 4,
    fullSourceRowCheck (chunkRow ⟨22, by decide⟩ 22 (by decide)
      0 4 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  decide +kernel

/-- Exact original source predicate on local rows 4..7. -/
theorem strip348_chunk01_checked : ∀ j : Fin 4,
    fullSourceRowCheck (chunkRow ⟨22, by decide⟩ 22 (by decide)
      4 4 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  decide +kernel

/-- Exact original source predicate on local rows 8..11. -/
theorem strip348_chunk02_checked : ∀ j : Fin 4,
    fullSourceRowCheck (chunkRow ⟨22, by decide⟩ 22 (by decide)
      8 4 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  decide +kernel

/-- Exact original source predicate on local rows 12..15. -/
theorem strip348_chunk03_checked : ∀ j : Fin 4,
    fullSourceRowCheck (chunkRow ⟨22, by decide⟩ 22 (by decide)
      12 4 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  decide +kernel

/-- Exact original source predicate on local rows 16..19. -/
theorem strip348_chunk04_checked : ∀ j : Fin 4,
    fullSourceRowCheck (chunkRow ⟨22, by decide⟩ 22 (by decide)
      16 4 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  decide +kernel

/-- Exact original source predicate on local rows 20..21. -/
theorem strip348_chunk05_checked : ∀ j : Fin 2,
    fullSourceRowCheck (chunkRow ⟨22, by decide⟩ 22 (by decide)
      20 2 (by decide) j) = true := by
  unfold fullSourceRowCheck
  rw [← fastSf_eq_actualSf]
  decide +kernel

/-- Original public full-strip goal, without numerical evaluation of all rows at once. -/
theorem strip348_checked :
    ∀ j : Fin (512 - firstU (⟨22, by decide⟩ : Fin 186)),
      fullSourceRowCheck (⟨(⟨22, by decide⟩ : Fin 186), j⟩ : Row) = true := by
  have hall : ∀ j : Fin 22,
      fullSourceRowCheck (rowAt ⟨22, by decide⟩ 22 (by decide) j) = true := by
    intro j
    by_cases h0 : j.val < 4
    · exact chunk_covers ⟨22, by decide⟩ 22 (by decide) 0 4 (by decide)
        strip348_chunk00_checked j (by omega) h0
    by_cases h1 : j.val < 8
    · exact chunk_covers ⟨22, by decide⟩ 22 (by decide) 4 4 (by decide)
        strip348_chunk01_checked j (by omega) h1
    by_cases h2 : j.val < 12
    · exact chunk_covers ⟨22, by decide⟩ 22 (by decide) 8 4 (by decide)
        strip348_chunk02_checked j (by omega) h2
    by_cases h3 : j.val < 16
    · exact chunk_covers ⟨22, by decide⟩ 22 (by decide) 12 4 (by decide)
        strip348_chunk03_checked j (by omega) h3
    by_cases h4 : j.val < 20
    · exact chunk_covers ⟨22, by decide⟩ 22 (by decide) 16 4 (by decide)
        strip348_chunk04_checked j (by omega) h4
    exact chunk_covers ⟨22, by decide⟩ 22 (by decide) 20 2 (by decide)
      strip348_chunk05_checked j (by omega) (by omega)
  exact StripAssembly.forallFinCast
    (by decide : 512 - firstU (⟨22, by decide⟩ : Fin 186) = 22)
    (fun j => fullSourceRowCheck (⟨(⟨22, by decide⟩ : Fin 186), j⟩ : Row) = true)
    hall

end ImbalancedChen.P2HistoricalSavedFloorSourceChecks
