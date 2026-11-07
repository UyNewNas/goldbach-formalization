-- SOURCE_ONLY / UNCOMPILED / NOT PASS / OPEN30.
-- Proposed installation: ImbalancedChen.Certificates.OriginalNodeArraysV1.All40ReaderBoundaryAPI
import ImbalancedChen.Certificates.OriginalNodeArraysV1.All40CheckedTable
import ImbalancedChen.Certificates.OriginalNodeArraysV1.InitialPrefix
import ImbalancedChen.Certificates.OriginalNodeArraysV1.PageTransfer

namespace P0All40ReaderBoundaryAPI

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
open ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly
open ImbalancedChen.OriginalU2InitialPrefix20261024uSourceOnly
open ImbalancedChen.OriginalU2All40CheckedTable20261024wSourceOnly

/-- Both guarded branches of the total raw reader have the same initializer. -/
theorem rawRead_default (blocks : Nat → Block) (i : Nat)
    (hi : i ≤ 32768 ∨ 196608 < i) :
    assembledRawRead blocks i = rawInitial := by
  rcases hi with hp | ht
  · simp only [assembledRawRead, if_pos hp]
  · have hp : ¬ i ≤ 32768 := by omega
    have ht' : ¬ i ≤ 196608 := by omega
    simp only [assembledRawRead, if_neg hp, if_neg ht']

/-- An out-of-update-domain call cannot access any supplied physical block. -/
theorem read_default (blocks : Nat → Block) (i : Nat)
    (hi : i ≤ 32768 ∨ 196608 < i) :
    assembledRead blocks i = integerInitial := by
  unfold assembledRead
  rw [rawRead_default blocks i hi]
  rfl

/-- Changing all blocks still preserves both guarded branches of the total reader. -/
theorem read_blocks_irrel_outside (left right : Nat → Block) (i : Nat)
    (hi : i ≤ 32768 ∨ 196608 < i) :
    assembledRead left i = assembledRead right i := by
  rw [read_default left i hi, read_default right i hi]

/-- Membership-based callers retain the inclusive prefix endpoint. -/
theorem read_prefix_list_range (blocks : Nat → Block) (i : Nat)
    (hi : i ∈ List.range 32769) :
    assembledRead blocks i = integerInitial := by
  exact assembledRead_prefix blocks i (by have := List.mem_range.mp hi; omega)

theorem read_prefix_fin (blocks : Nat → Block) (i : Fin 32769) :
    assembledRead blocks i.val = integerInitial := by
  exact assembledRead_prefix blocks i.val (by have := i.isLt; omega)

/-- Natural callers outside the closed update range get the actual default. -/
theorem read_not_mem_update_range (blocks : Nat → Block) (i : Nat)
    (hi : i ∉ Finset.Icc 32769 196608) :
    assembledRead blocks i = integerInitial := by
  apply read_default
  by_cases hp : i ≤ 32768
  · exact Or.inl hp
  · right
    by_contra ht
    apply hi
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

/-- Signed callers use Nat.toNat's saturation on negative indices explicitly. -/
theorem read_int_toNat_prefix (blocks : Nat → Block) (i : Int)
    (hi : i ≤ 32768) :
    assembledRead blocks i.toNat = integerInitial := by
  apply assembledRead_prefix
  omega

theorem read_int_toNat_tail (blocks : Nat → Block) (i : Int)
    (hi : 196608 < i) :
    assembledRead blocks i.toNat = integerInitial := by
  apply read_default
  right
  omega

/-- An interior row uses exactly its physical slot and legal offset. -/
theorem rawRead_block_offset (blocks : Nat → Block) (b k : Nat)
    (hb : b < 40) (hk : k < 4096) :
    assembledRawRead blocks (32769 + 4096 * b + k) = (blocks b).read k := by
  have hp : ¬ 32769 + 4096 * b + k ≤ 32768 := by omega
  have hm : 32769 + 4096 * b + k ≤ 196608 := by omega
  have hq : (32769 + 4096 * b + k - 32769) / 4096 = b := by omega
  have hr : (32769 + 4096 * b + k - 32769) % 4096 = k := by omega
  simp only [assembledRawRead, if_neg hp, if_pos hm, hq, hr]

theorem read_block_offset (blocks : Nat → Block) (b k : Nat)
    (hb : b < 40) (hk : k < 4096) :
    assembledRead blocks (32769 + 4096 * b + k) = toOriginal ((blocks b).read k) := by
  unfold assembledRead
  rw [rawRead_block_offset blocks b k hb hk]

/-- Left side of a positive block boundary is offset4095 of the preceding block. -/
theorem read_block_predecessor (blocks : Nat → Block) (b : Nat)
    (hb : 1 ≤ b) (hbmax : b < 40) :
    assembledRead blocks (32769 + 4096 * b - 1) =
      toOriginal ((blocks (b - 1)).read 4095) := by
  have he : 32769 + 4096 * b - 1 = 32769 + 4096 * (b - 1) + 4095 := by omega
  rw [he]
  exact read_block_offset blocks (b - 1) 4095 (by omega) (by omega)

/-- Right side of the same block boundary is offset0 of its new block. -/
theorem read_block_start (blocks : Nat → Block) (b : Nat) (hb : b < 40) :
    assembledRead blocks (32769 + 4096 * b) = toOriginal ((blocks b).read 0) := by
  simpa only [Nat.add_zero] using read_block_offset blocks b 0 hb (by omega)

theorem read_block_end (blocks : Nat → Block) (b : Nat) (hb : b < 40) :
    assembledRead blocks (32769 + 4096 * b + 4095) =
      toOriginal ((blocks b).read 4095) := by
  exact read_block_offset blocks b 4095 hb (by omega)

/-- The successor of the final row of a nonfinal block enters its next block. -/
theorem read_next_block_start (blocks : Nat → Block) (b : Nat) (hb : b < 39) :
    assembledRead blocks (32769 + 4096 * b + 4096) =
      toOriginal ((blocks (b + 1)).read 0) := by
  have he : 32769 + 4096 * b + 4096 = 32769 + 4096 * (b + 1) := by omega
  rw [he]
  exact read_block_start blocks (b + 1) (by omega)

/-- Prefix decoding can be consumed directly at the semantic node carrier. -/
theorem prefix_decoder_toOriginal (blocks : Nat → Block) (i : Nat)
    (hi : i ≤ 32768) :
    Option.map toOriginal (decodeRowAt canonicalPrefix i) =
      some (assembledRead blocks i) := by
  have h := congrArg (Option.map toOriginal)
    (assembledRawRead_prefix_correspondence blocks i hi)
  simpa only [Option.map_some, assembledRead] using h

/-- Both ends of the concrete table retain their guards and actual boundary rows. -/
theorem literal_reader_outer_boundaries :
    assembledRead literalBlocks 32768 = integerInitial ∧
    assembledRead literalBlocks 32769 = toOriginal ((literalBlocks 0).read 0) ∧
    assembledRead literalBlocks 196608 = toOriginal ((literalBlocks 39).read 4095) ∧
    assembledRead literalBlocks 196609 = integerInitial := by
  refine ⟨assembledRead_prefix literalBlocks 32768 (by omega), ?_, ?_, ?_⟩
  · exact read_block_start literalBlocks 0 (by omega)
  · exact read_block_end literalBlocks 39 (by omega)
  · exact read_default literalBlocks 196609 (Or.inr (by omega))

end P0All40ReaderBoundaryAPI
