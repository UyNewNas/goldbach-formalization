import ImbalancedChen.P2HistoricalSavedFloorFastSource
import ImbalancedChen.Certificates.PairedV2StripFiniteAssembly

namespace ImbalancedChen.P2HistoricalSavedFloorBoundedSource
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open P2HistoricalSavedFloorFullBinder

def rowAt (i : Fin 186) (n : ℕ) (hn : n = 512 - firstU i) (j : Fin n) : Row :=
  ⟨i, Fin.cast hn j⟩

def chunkRow (i : Fin 186) (n : ℕ) (hn : n = 512 - firstU i)
    (offset width : ℕ) (h : offset + width ≤ n) (j : Fin width) : Row :=
  rowAt i n hn ⟨offset + j.val, (Nat.add_lt_add_left j.isLt offset).trans_le h⟩

/-- Exact transport from a bounded contiguous block, retaining the original Row. -/
theorem chunk_covers (i : Fin 186) (n : ℕ) (hn : n = 512 - firstU i)
    (offset width : ℕ) (h : offset + width ≤ n)
    (hc : ∀ k : Fin width, fullSourceRowCheck (chunkRow i n hn offset width h k) = true)
    (j : Fin n) (hlo : offset ≤ j.val) (hhi : j.val < offset + width) :
    fullSourceRowCheck (rowAt i n hn j) = true := by
  let k : Fin width := ⟨j.val - offset, by omega⟩
  have he : chunkRow i n hn offset width h k = rowAt i n hn j := by
    apply congrArg (rowAt i n hn)
    apply Fin.ext
    change offset + (j.val - offset) = j.val
    omega
  have hh := hc k
  rw [he] at hh
  exact hh

end ImbalancedChen.P2HistoricalSavedFloorBoundedSource
