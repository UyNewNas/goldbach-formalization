import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check

/-!
SOURCEONLY 20261024s. UNCOMPILED / NOT PASS. ROOT owns strict compilation.
No Lean/lake/helper/numerical/Git/Sites/usage-limit command was run.
No actual source, accepted theorem or resource limit was changed.

Read-only actual anchors (SHA256):
 DataCore.lean ec88f692be60266026428c7a00e5a45a0b0e99da5937181c42be2505e1a2c92d
 CheckerCore.lean 2eddf3387a91fb0d4195433a20189d5a8d98709e45cd5be4f5880b7b7ef47a81
 Block00Window.lean aeb52f77451dd1c7bfa6af1e200d63baa9a9109c99063125b4a3178a9c5be07d
 Block00FullCheck.lean 31b37cf2d75d1c836cae9d497a735a3947c542875ab4f5559c248de71d71e663
 Part4ActualThirdOriginalStoredNodeLocalChecker.lean
  647b5c2c2fe5bc718c5caf5512f7a5e731716b7903627daab89e81ba5f774128

All congruences concern equality of full OriginalNode records and the
actual readCheckStep / checkedUpdate. The two-point specialization is
restricted to i<=49152. Later original branches also read j=i-16385 and
j+1; their congruence retains those full-node equality requirements.

referencePairBlocks chooses current at slot b and prev at every other
slot. Its actual assembled reader agrees with the arbitrary-tail window
on [32769+4096*b-1,32769+4096*b+4095]. This local geometry alone does not
prove the later delayed-read equalities. No closed check is performed
here. ROOT may instantiate the finite reference-page Boolean premises
by exact kernel reduction using actual data in a later module.
-/

namespace ImbalancedChen.OriginalStoredPageTransferSourceOnly

open ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly
open ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly

/-- Full original update: all prior nodes that any original branch may read. -/
theorem checkedUpdate_congr_allReads (read reference : Nat → OriginalNode) (i : Nat)
    (hprev : read (i-1) = reference (i-1))
    (hdelayed : read (i-16385) = reference (i-16385))
    (hdelayedNext : read (i-16385+1) = reference (i-16385+1)) :
    checkedUpdate i read = checkedUpdate i reference := by
  simp only [checkedUpdate, hprev, hdelayed, hdelayedNext]

/-- No branch is weakened: current node plus every possible update input. -/
theorem readCheckStep_congr_allReads (read reference : Nat → OriginalNode) (i : Nat)
    (hcurrent : read i = reference i)
    (hprev : read (i-1) = reference (i-1))
    (hdelayed : read (i-16385) = reference (i-16385))
    (hdelayedNext : read (i-16385+1) = reference (i-16385+1)) :
    readCheckStep read i = readCheckStep reference i := by
  unfold readCheckStep
  rw [hcurrent, checkedUpdate_congr_allReads read reference i hprev hdelayed hdelayedNext]

/-- Only the original early branches depend on just i and i-1. -/
theorem readCheckStep_congr_twoReads (read reference : Nat → OriginalNode) (i : Nat)
    (hi : i ≤ 49152)
    (hcurrent : read i = reference i)
    (hprev : read (i-1) = reference (i-1)) :
    readCheckStep read i = readCheckStep reference i := by
  by_cases hp : i ≤ 32768
  · simp only [readCheckStep, checkedUpdate, if_pos hp, hcurrent]
  · have hL : i ≤ 65536 := by omega
    simp only [readCheckStep, checkedUpdate, if_neg hp, if_pos hL, if_pos hi,
      hcurrent, hprev]

/-- Generic strict page transfer, including every delayed-read equality. -/
theorem readCheckBlock_transfer_allReads
    (read reference : Nat → OriginalNode) (lo count : Nat)
    (hreads : ∀ k : Nat, k < count →
      read (lo+k) = reference (lo+k) ∧
      read (lo+k-1) = reference (lo+k-1) ∧
      read (lo+k-16385) = reference (lo+k-16385) ∧
      read (lo+k-16385+1) = reference (lo+k-16385+1))
    (hclosed : readCheckBlock reference lo count = true) :
    readCheckBlock read lo count = true := by
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < count := List.mem_range.mp hk
  obtain ⟨hcurrent,hprev,hdelayed,hdelayedNext⟩ := hreads k hk'
  rw [readCheckStep_congr_allReads read reference (lo+k)
    hcurrent hprev hdelayed hdelayedNext]
  exact readCheckBlock_step hclosed hk'

/-- Reuse a reference page using two actual full-node equalities per row. -/
theorem readCheckBlock_transfer_twoReads
    (read reference : Nat → OriginalNode) (lo count : Nat)
    (hupper : lo+count ≤ 49153)
    (hreads : ∀ k : Nat, k < count →
      read (lo+k) = reference (lo+k) ∧
      read (lo+k-1) = reference (lo+k-1))
    (hclosed : readCheckBlock reference lo count = true) :
    readCheckBlock read lo count = true := by
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < count := List.mem_range.mp hk
  obtain ⟨hcurrent,hprev⟩ := hreads k hk'
  have hi : lo+k ≤ 49152 := by omega
  rw [readCheckStep_congr_twoReads read reference (lo+k) hi hcurrent hprev]
  exact readCheckBlock_step hclosed hk'

/-- Freeze two distinct physical block slots; every other slot is the same tail. -/
def windowPrevCurrent (b : Nat) (prev current : Block) (tail : Nat → Block)
    (slot : Nat) : Block :=
  if slot = b then current else if slot = b-1 then prev else tail slot

/-- Closed reference once b, prev and current are concrete: no arbitrary tail. -/
def referencePairBlocks (b : Nat) (prev current : Block) (slot : Nat) : Block :=
  if slot = b then current else prev

theorem windowPrevCurrent_current (b : Nat) (prev current : Block)
    (tail : Nat → Block) : windowPrevCurrent b prev current tail b = current := by
  simp [windowPrevCurrent]

theorem windowPrevCurrent_previous (b : Nat) (hb : 1 ≤ b) (prev current : Block)
    (tail : Nat → Block) : windowPrevCurrent b prev current tail (b-1) = prev := by
  have hne : b-1 ≠ b := by omega
  simp [windowPrevCurrent, hne]

/-- The frozen window is the original table if these exact slots already match. -/
theorem windowPrevCurrent_eq_self (b : Nat) (prev current : Block)
    (tail : Nat → Block) (hprev : tail (b-1) = prev) (hcurrent : tail b = current) :
    windowPrevCurrent b prev current tail = tail := by
  funext slot
  by_cases hc : slot = b
  · subst slot
    simpa [windowPrevCurrent] using hcurrent.symm
  · by_cases hp : slot = b-1
    · subst slot
      simpa [windowPrevCurrent, hc] using hprev.symm
    · simp only [windowPrevCurrent, if_neg hc, if_neg hp]

/-- Exact physical slot arithmetic, retaining origin32769 and width4096. -/
theorem pair_window_slots (b i : Nat)
    (hlow : 32769+4096*b-1 ≤ i) (hhigh : i ≤ 32769+4096*b+4095) :
    (i-32769)/4096 = b-1 ∨ (i-32769)/4096 = b := by
  omega

/-- True assembled-reader equality on the predecessor row and current block.
Both original prefix and out-of-domain branches are explicitly retained. -/
theorem assembledRead_windowPrevCurrent_eq_referencePair
    (b : Nat) (hb : 1 ≤ b) (prev current : Block) (tail : Nat → Block)
    (i : Nat) (hlow : 32769+4096*b-1 ≤ i)
    (hhigh : i ≤ 32769+4096*b+4095) :
    assembledRead (windowPrevCurrent b prev current tail) i =
      assembledRead (referencePairBlocks b prev current) i := by
  by_cases hp : i ≤ 32768
  · simp only [assembledRead, assembledRawRead, if_pos hp]
  · by_cases hmax : i ≤ 196608
    · have hslot := pair_window_slots b i hlow hhigh
      simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax]
      rcases hslot with hprevious | hcurrent
      · have hne : b-1 ≠ b := by omega
        simp [hprevious, windowPrevCurrent, referencePairBlocks, hne]
      · simp [hcurrent, windowPrevCurrent, referencePairBlocks]
    · simp only [assembledRead, assembledRawRead, if_neg hp, if_neg hmax]

/-- The first update really reads offset4095 of the previous physical block. -/
theorem assembledRead_windowPrevCurrent_boundary
    (b : Nat) (hb : 1 ≤ b) (hbmax : b < 40)
    (prev current : Block) (tail : Nat → Block) :
    assembledRead (windowPrevCurrent b prev current tail) (32769+4096*b-1) =
      toOriginal (prev.read 4095) := by
  have hp : ¬32769+4096*b-1 ≤ 32768 := by omega
  have hmax : 32769+4096*b-1 ≤ 196608 := by omega
  have hslot : (32769+4096*b-1-32769)/4096 = b-1 := by omega
  have hoffset : (32769+4096*b-1-32769)%4096 = 4095 := by omega
  simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
    hslot, hoffset, windowPrevCurrent_previous b hb prev current tail]

/-- In particular, the predecessor at the Block01 first step36865 is36864. -/
theorem block01_first_step_previous (prev current : Block) (tail : Nat → Block) :
    assembledRead (windowPrevCurrent 1 prev current tail) 36864 =
      toOriginal (prev.read 4095) := by
  simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] using
    assembledRead_windowPrevCurrent_boundary 1 (by omega) (by omega)
      prev current tail

/-- Transfer a bounded early segment from its specific two-block reference. -/
theorem windowPrevCurrent_segment_transfer_early
    (b : Nat) (hb : 1 ≤ b) (prev current : Block) (tail : Nat → Block)
    (lo count : Nat) (hlow : 32769+4096*b ≤ lo)
    (hhigh : lo+count ≤ 32769+4096*b+4096) (hearly : lo+count ≤ 49153)
    (hclosed : readCheckBlock (assembledRead (referencePairBlocks b prev current))
      lo count = true) :
    readCheckBlock (assembledRead (windowPrevCurrent b prev current tail))
      lo count = true := by
  apply readCheckBlock_transfer_twoReads
    (assembledRead (windowPrevCurrent b prev current tail))
    (assembledRead (referencePairBlocks b prev current)) lo count hearly _ hclosed
  intro k hk
  constructor
  · apply assembledRead_windowPrevCurrent_eq_referencePair b hb prev current tail (lo+k)
    · omega
    · omega
  · apply assembledRead_windowPrevCurrent_eq_referencePair b hb prev current tail (lo+k-1)
    · omega
    · omega

/-- Reusable original64-row page transfer for blocks01,02,03 only.
The finite reference-page check is the exact future ROOT kernel obligation. -/
theorem windowPrevCurrent_page_transfer_blocks01to03
    (b : Nat) (hb : 1 ≤ b) (hbmax : b ≤ 3)
    (prev current : Block) (tail : Nat → Block) (p : Nat) (hp : p < 64)
    (hclosed : readCheckBlock (assembledRead (referencePairBlocks b prev current))
      (32769+4096*b+64*p) 64 = true) :
    readCheckBlock (assembledRead (windowPrevCurrent b prev current tail))
      (32769+4096*b+64*p) 64 = true := by
  apply windowPrevCurrent_segment_transfer_early b hb prev current tail
    (32769+4096*b+64*p) 64 _ _ _ hclosed
  · omega
  · omega
  · omega

end ImbalancedChen.OriginalStoredPageTransferSourceOnly

/-
EXACT LIMIT:
No concrete Block01 check is proved here. All64 page checks still require
ROOT's actual closed Boolean kernel proofs on the specific reference reader.

Blocks04..39 cannot use the two-point rule. With i=32769+4096*b+k,
0<=k<4096 and b>=4, delayed j=i-16385 lies at the end of slot b-5 when
k=0 and b>=5 (at prefix row32768 when b=4), and otherwise in slot b-4.
j+1 always lies in slot b-4. Thus a later full-block transfer must cover
b-1,b,b-4 plus boundary slot b-5 (or the prefix for b=4), or directly
prove the complete local node equalities required by allReads above.
The present pair-reader equality claims only its stated physical interval.
No checker branch, integer round, max, denominator, P112 or cap is changed.
-/
