-- SOURCE_ONLY / UNCOMPILED / NOT PASS / OPEN30.
-- Proposed installation: ImbalancedChen.Certificates.OriginalNodeArraysV1.All40FiniteIndexAPI
-- The All40CheckedTable import denotes the source-only V2 table candidate.
-- No kernel check, numerical replay, or final original-C closure is claimed.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.All40CheckedTable

namespace P0All40FiniteIndexAPI

open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalU2All40CheckedTable20261024wSourceOnly

/-- A natural physical slot enters the checked table only with its domain proof. -/
def natBlockIndex (b : Nat) (hb : b < 40) : Fin 40 := ⟨b, hb⟩

@[simp] theorem natBlockIndex_val (b : Nat) (hb : b < 40) :
    (natBlockIndex b hb).val = b := rfl

@[simp] theorem natBlockIndex_roundtrip (b : Fin 40) :
    natBlockIndex b.val b.isLt = b := by
  apply Fin.ext
  rfl

/-- Different proofs of the same natural bound select the same physical slot. -/
theorem natBlockIndex_proof_irrel (b : Nat) (h₁ h₂ : b < 40) :
    natBlockIndex b h₁ = natBlockIndex b h₂ := by
  apply Fin.ext
  rfl

/-- The original block origin; this definition retains both original constants. -/
def blockStart (b : Fin 40) : Nat := 32769 + 4096 * b.val

@[simp] theorem blockStart_natBlockIndex (b : Nat) (hb : b < 40) :
    blockStart (natBlockIndex b hb) = 32769 + 4096 * b := rfl

/-- Public bridge from a natural slot to the concrete finite table certificate. -/
theorem literalBlocks_nat_checked (b : Nat) (hb : b < 40) :
    readCheckBlock (assembledRead literalBlocks) (32769 + 4096 * b) 4096 = true := by
  exact literalBlocks_all40_checked (natBlockIndex b hb)

/-- The inclusive natural-index convention used by block callers. -/
theorem literalBlocks_nat_le39_checked (b : Nat) (hb : b ≤ 39) :
    readCheckBlock (assembledRead literalBlocks) (32769 + 4096 * b) 4096 = true := by
  exact literalBlocks_nat_checked b (by omega)

/-- A `Finset.range` caller need not manufacture a finite-index proof. -/
theorem literalBlocks_range_checked (b : Nat) (hb : b ∈ Finset.range 40) :
    readCheckBlock (assembledRead literalBlocks) (32769 + 4096 * b) 4096 = true := by
  exact literalBlocks_nat_checked b (Finset.mem_range.mp hb)

/-- The same interface for a list-range traversal of the forty physical blocks. -/
theorem literalBlocks_list_range_checked (b : Nat) (hb : b ∈ List.range 40) :
    readCheckBlock (assembledRead literalBlocks) (32769 + 4096 * b) 4096 = true := by
  exact literalBlocks_nat_checked b (List.mem_range.mp hb)

/-- Decode a row in the original update interval to its checked physical slot. -/
def rowBlockIndex (i : Nat) (hi : 32769 ≤ i) (hmax : i ≤ 196608) : Fin 40 :=
  ⟨(i - 32769) / 4096, by omega⟩

/-- The row's position in its physical block, with the original width. -/
def rowOffset (i : Nat) : Nat := (i - 32769) % 4096

@[simp] theorem rowBlockIndex_val (i : Nat) (hi : 32769 ≤ i) (hmax : i ≤ 196608) :
    (rowBlockIndex i hi hmax).val = (i - 32769) / 4096 := rfl

theorem rowOffset_lt (i : Nat) : rowOffset i < 4096 := by
  dsimp [rowOffset]
  omega

/-- Quotient and remainder recover the exact row, without a fallback table slot. -/
theorem rowBlockIndex_decomposition (i : Nat)
    (hi : 32769 ≤ i) (hmax : i ≤ 196608) :
    blockStart (rowBlockIndex i hi hmax) + rowOffset i = i := by
  dsimp [blockStart, rowBlockIndex, rowOffset]
  omega

/-- Row decoding is inverse to natural block/offset addressing throughout the table. -/
theorem rowBlockIndex_of_block_offset (b k : Nat) (hb : b < 40) (hk : k < 4096) :
    rowBlockIndex (32769 + 4096 * b + k) (by omega) (by omega) =
      natBlockIndex b hb := by
  apply Fin.ext
  dsimp [rowBlockIndex, natBlockIndex]
  omega

theorem rowOffset_of_block_offset (b k : Nat) (hk : k < 4096) :
    rowOffset (32769 + 4096 * b + k) = k := by
  dsimp [rowOffset]
  omega

/-- The original Boolean step is available directly at every bounded natural row. -/
theorem literalBlocks_interval_step_checked (i : Nat)
    (hi : 32769 ≤ i) (hmax : i ≤ 196608) :
    readCheckStep (assembledRead literalBlocks) i = true := by
  have h := readCheckBlock_step
    (literalBlocks_all40_checked (rowBlockIndex i hi hmax)) (rowOffset_lt i)
  change readCheckStep (assembledRead literalBlocks)
    (blockStart (rowBlockIndex i hi hmax) + rowOffset i) = true at h
  rw [rowBlockIndex_decomposition i hi hmax] at h
  exact h

/-- Every half-open subinterval of the original update interval is checked.
The upper endpoint is exclusive, so this also handles an empty terminal range. -/
theorem literalBlocks_interval_checked (lo count : Nat)
    (hlow : 32769 ≤ lo) (hhigh : lo + count ≤ 196609) :
    readCheckBlock (assembledRead literalBlocks) lo count = true := by
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < count := List.mem_range.mp hk
  exact literalBlocks_interval_step_checked (lo + k) (by omega) (by omega)

/-- All forty adjacent blocks form one checked original update range. -/
theorem literalBlocks_full_update_range_checked :
    readCheckBlock (assembledRead literalBlocks) 32769 163840 = true := by
  exact literalBlocks_interval_checked 32769 163840 (by omega) (by omega)

end P0All40FiniteIndexAPI
