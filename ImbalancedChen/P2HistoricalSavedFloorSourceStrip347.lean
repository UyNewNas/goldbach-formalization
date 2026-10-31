import ImbalancedChen.P2HistoricalSavedFloorSource347Part0
import ImbalancedChen.P2HistoricalSavedFloorSource347Part1

namespace ImbalancedChen.P2HistoricalSavedFloorSourceChecks
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open P2HistoricalSavedFloorFullBinder P2HistoricalSavedFloorFastSource
open P2HistoricalSavedFloorBoundedSource
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Original public full-strip goal, without numerical evaluation of all rows at once. -/
theorem strip347_checked :
    ∀ j : Fin (512 - firstU (⟨21, by decide⟩ : Fin 186)),
      fullSourceRowCheck (⟨(⟨21, by decide⟩ : Fin 186), j⟩ : Row) = true := by
  have hall : ∀ j : Fin 21,
      fullSourceRowCheck (rowAt ⟨21, by decide⟩ 21 (by decide) j) = true := by
    intro j
    by_cases h0 : j.val < 4
    · exact chunk_covers ⟨21, by decide⟩ 21 (by decide) 0 4 (by decide)
        strip347_chunk00_checked j (by omega) h0
    by_cases h1 : j.val < 8
    · exact chunk_covers ⟨21, by decide⟩ 21 (by decide) 4 4 (by decide)
        strip347_chunk01_checked j (by omega) h1
    by_cases h2 : j.val < 12
    · exact chunk_covers ⟨21, by decide⟩ 21 (by decide) 8 4 (by decide)
        strip347_chunk02_checked j (by omega) h2
    by_cases h3 : j.val < 16
    · exact chunk_covers ⟨21, by decide⟩ 21 (by decide) 12 4 (by decide)
        strip347_chunk03_checked j (by omega) h3
    by_cases h4 : j.val < 20
    · exact chunk_covers ⟨21, by decide⟩ 21 (by decide) 16 4 (by decide)
        strip347_chunk04_checked j (by omega) h4
    exact chunk_covers ⟨21, by decide⟩ 21 (by decide) 20 1 (by decide)
      strip347_chunk05_checked j (by omega) (by omega)
  exact StripAssembly.forallFinCast
    (by decide : 512 - firstU (⟨21, by decide⟩ : Fin 186) = 21)
    (fun j => fullSourceRowCheck (⟨(⟨21, by decide⟩ : Fin 186), j⟩ : Row) = true)
    hall

end ImbalancedChen.P2HistoricalSavedFloorSourceChecks
