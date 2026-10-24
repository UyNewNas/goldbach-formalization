import ImbalancedChen.Certificates.OriginalNodeArraysV1.CheckerCore
import ImbalancedChen.Certificates.OriginalNodeArraysV1.Block00Page00Check

/-!
SOURCEONLY 20261024u. UNCOMPILED / NOT PASS / MAIN OPEN30.
CP: proposed bounded original stored-node page-transfer extension.
ROOT owns compiler, helper, Git, actual-source installation and acceptance.
This source was prepared only by file reads and this draft-file write.
No new axiom, sorry, native_decide, compiler invocation or closed numerical
check is supplied. The exact original checkedUpdate is retained unchanged.

CP exactsha dependencies supplied by ROOT / prior source record:
 CheckerCore.lean
  2eddf3387a91fb0d4195433a20189d5a8d98709e45cd5be4f5880b7b7ef47a81
 DataCore.lean
  ec88f692be60266026428c7a00e5a45a0b0e99da5937181c42be2505e1a2c92d
 Part4ActualThirdOriginalStoredNodeLocalChecker.lean
  647b5c2c2fe5bc718c5caf5512f7a5e731716b7903627daab89e81ba5f774128
 Prior 20261024s-original-stored-page-transfer-SOURCEONLY.lean.txt
  479b0f43f66b0a866c3fd7193317e3ad8079245afbba488c6e19dc5f49b05ba2
The prior draft is a read dependency, not an import or installation premise.
ROOT must bind this output file's exact SHA independently before compilation.

For blocks04..39 every page reads current slot b, previous slot b-1,
delayed slot b-4, and possibly the last row of slot b-5. At b=4 the
first delayed row is prefix row32768, which the real assembled reader
dispatches to integerInitial before selecting a physical block. The finite
reference below has no arbitrary tail; its fallback repeats boundary.
Its only Boolean premise is the actual original 64-row integer check.
-/

namespace ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

open ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly
open ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly

/-- Full original update congruence, including both delayed full-node inputs. -/
theorem checkedUpdate_congr_allReads (read reference : Nat → OriginalNode) (i : Nat)
    (hprev : read (i-1) = reference (i-1))
    (hdelayed : read (i-16385) = reference (i-16385))
    (hdelayedNext : read (i-16385+1) = reference (i-16385+1)) :
    checkedUpdate i read = checkedUpdate i reference := by
  simp only [checkedUpdate, hprev, hdelayed, hdelayedNext]

theorem readCheckStep_congr_allReads (read reference : Nat → OriginalNode) (i : Nat)
    (hcurrent : read i = reference i)
    (hprev : read (i-1) = reference (i-1))
    (hdelayed : read (i-16385) = reference (i-16385))
    (hdelayedNext : read (i-16385+1) = reference (i-16385+1)) :
    readCheckStep read i = readCheckStep reference i := by
  unfold readCheckStep
  rw [hcurrent, checkedUpdate_congr_allReads read reference i hprev hdelayed hdelayedNext]

/-- The caller below proves these equalities from physical slot geometry. -/
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

/-- Four frozen physical slots. Delayed precedes boundary so that at b=4
the two saturated indices b-4=b-5=0 select the delayed block. -/
def windowBlocks (b : Nat) (boundary delayed prev current : Block)
    (tail : Nat → Block) (slot : Nat) : Block :=
  if slot = b then current else
  if slot = b-1 then prev else
  if slot = b-4 then delayed else
  if slot = b-5 then boundary else tail slot

/-- A closed four-block reference once these four blocks and b are concrete. -/
def referenceBlocks (b : Nat) (boundary delayed prev current : Block)
    (slot : Nat) : Block :=
  if slot = b then current else
  if slot = b-1 then prev else
  if slot = b-4 then delayed else boundary

theorem windowBlocks_eq_reference_at_slots
    (b : Nat) (boundary delayed prev current : Block) (tail : Nat → Block)
    (slot : Nat)
    (hslot : slot = b ∨ slot = b-1 ∨ slot = b-4 ∨ slot = b-5) :
    windowBlocks b boundary delayed prev current tail slot =
      referenceBlocks b boundary delayed prev current slot := by
  rcases hslot with hc | hp | hd | hb
  · simp [windowBlocks, referenceBlocks, hc]
  · simp [windowBlocks, referenceBlocks, hp]
  · simp [windowBlocks, referenceBlocks, hd]
  · simp [windowBlocks, referenceBlocks, hb]

/-- Prefix and out-of-domain dispatch remain the real assembledRawRead
branches. Within the stored domain, only the four selected slots matter. -/
theorem assembledRead_window_eq_reference_at_slots
    (b : Nat) (boundary delayed prev current : Block) (tail : Nat → Block)
    (i : Nat)
    (hslot : (i-32769)/4096 = b ∨ (i-32769)/4096 = b-1 ∨
      (i-32769)/4096 = b-4 ∨ (i-32769)/4096 = b-5) :
    assembledRead (windowBlocks b boundary delayed prev current tail) i =
      assembledRead (referenceBlocks b boundary delayed prev current) i := by
  by_cases hp : i ≤ 32768
  · simp only [assembledRead, assembledRawRead, if_pos hp]
  · by_cases hmax : i ≤ 196608
    · simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax]
      rw [windowBlocks_eq_reference_at_slots b boundary delayed prev current tail
        ((i-32769)/4096) hslot]
    · simp only [assembledRead, assembledRawRead, if_neg hp, if_neg hmax]

/-- Consecutive block interval plus its predecessor has exactly these slots. -/
theorem pair_window_slots (b i : Nat)
    (hlow : 32769+4096*b-1 ≤ i) (hhigh : i ≤ 32769+4096*b+4095) :
    (i-32769)/4096 = b-1 ∨ (i-32769)/4096 = b := by
  omega

/-- The four actual original input indices are inside the four frozen slots.
The first delayed index at b=4 is allowed through its prefix dispatch. -/
theorem original_read_slot_coverage (b i : Nat) (hb : 4 ≤ b)
    (hlow : 32769+4096*b ≤ i) (hhigh : i ≤ 32769+4096*b+4095) :
    ((i-32769)/4096 = b ∨ (i-32769)/4096 = b-1 ∨
      (i-32769)/4096 = b-4 ∨ (i-32769)/4096 = b-5) ∧
    ((i-1-32769)/4096 = b ∨ (i-1-32769)/4096 = b-1 ∨
      (i-1-32769)/4096 = b-4 ∨ (i-1-32769)/4096 = b-5) ∧
    ((i-16385-32769)/4096 = b ∨ (i-16385-32769)/4096 = b-1 ∨
      (i-16385-32769)/4096 = b-4 ∨ (i-16385-32769)/4096 = b-5) ∧
    ((i-16385+1-32769)/4096 = b ∨ (i-16385+1-32769)/4096 = b-1 ∨
      (i-16385+1-32769)/4096 = b-4 ∨ (i-16385+1-32769)/4096 = b-5) := by
  have hc := pair_window_slots b i (by omega) hhigh
  have hp := pair_window_slots b (i-1) (by omega) (by omega)
  have hj := pair_window_slots (b-4) (i-16385) (by omega) (by omega)
  have hjnext := pair_window_slots (b-4) (i-16385+1) (by omega) (by omega)
  have hsub : b-4-1 = b-5 := by omega
  rw [hsub] at hj hjnext
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases hc with hp | hc
    · exact Or.inr (Or.inl hp)
    · exact Or.inl hc
  · rcases hp with hp | hc
    · exact Or.inr (Or.inl hp)
    · exact Or.inl hc
  · rcases hj with hb | hd
    · exact Or.inr (Or.inr (Or.inr hb))
    · exact Or.inr (Or.inr (Or.inl hd))
  · rcases hjnext with hb | hd
    · exact Or.inr (Or.inr (Or.inr hb))
    · exact Or.inr (Or.inr (Or.inl hd))

/-- Explicit initial-prefix boundary: at the first row of Block04 the
delayed read is row32768, independent of every physical block argument. -/
theorem block04_first_delayed_is_prefix
    (boundary delayed prev current : Block) (tail : Nat → Block) :
    assembledRead (windowBlocks 4 boundary delayed prev current tail)
        (32769+4096*4-16385) = integerInitial ∧
    assembledRead (referenceBlocks 4 boundary delayed prev current)
        (32769+4096*4-16385) = integerInitial := by
  constructor <;> apply assembledRead_prefix <;> omega

/-- The later boundary really reads offset4095 of slot b-5; it cannot be
replaced by prev or delayed without changing an original dependency. -/
theorem first_delayed_boundary_row (b : Nat) (hb : 5 ≤ b) (hbmax : b < 40)
    (boundary delayed prev current : Block) (tail : Nat → Block) :
    assembledRead (windowBlocks b boundary delayed prev current tail)
        (32769+4096*b-16385) = toOriginal (boundary.read 4095) := by
  have hp : ¬32769+4096*b-16385 ≤ 32768 := by omega
  have hmax : 32769+4096*b-16385 ≤ 196608 := by omega
  have hslot : (32769+4096*b-16385-32769)/4096 = b-5 := by omega
  have hoffset : (32769+4096*b-16385-32769)%4096 = 4095 := by omega
  have hcurrent : b-5 ≠ b := by omega
  have hprev : b-5 ≠ b-1 := by omega
  have hdelayed : b-5 ≠ b-4 := by omega
  simp only [assembledRead, assembledRawRead, if_neg hp, if_pos hmax,
    hslot, hoffset, windowBlocks, if_neg hcurrent, if_neg hprev,
    if_neg hdelayed]
  rfl

/-- Reusable bounded mother lemma for every 64-row page in blocks04..39.
Every equality is proved from the four-slot window; the only user premise
is the closed original reference-page check. Both delayed reads survive. -/
theorem window_page_transfer_blocks04to39
    (b : Nat) (hb : 4 ≤ b) (_hbmax : b < 40)
    (boundary delayed prev current : Block) (tail : Nat → Block)
    (p : Nat) (hp : p < 64)
    (hclosed : readCheckBlock
      (assembledRead (referenceBlocks b boundary delayed prev current))
      (32769+4096*b+64*p) 64 = true) :
    readCheckBlock
      (assembledRead (windowBlocks b boundary delayed prev current tail))
      (32769+4096*b+64*p) 64 = true := by
  apply readCheckBlock_transfer_allReads
    (assembledRead (windowBlocks b boundary delayed prev current tail))
    (assembledRead (referenceBlocks b boundary delayed prev current))
    (32769+4096*b+64*p) 64 _ hclosed
  intro k hk
  have hlow : 32769+4096*b ≤ 32769+4096*b+64*p+k := by omega
  have hhigh : 32769+4096*b+64*p+k ≤ 32769+4096*b+4095 := by omega
  obtain ⟨hc, hprev, hd, hdn⟩ := original_read_slot_coverage b
    (32769+4096*b+64*p+k) hb hlow hhigh
  exact ⟨assembledRead_window_eq_reference_at_slots b boundary delayed prev current tail
      (32769+4096*b+64*p+k) hc,
    assembledRead_window_eq_reference_at_slots b boundary delayed prev current tail
      (32769+4096*b+64*p+k-1) hprev,
    assembledRead_window_eq_reference_at_slots b boundary delayed prev current tail
      (32769+4096*b+64*p+k-16385) hd,
    assembledRead_window_eq_reference_at_slots b boundary delayed prev current tail
      (32769+4096*b+64*p+k-16385+1) hdn⟩

/-- Selecting the four slots from the same immutable table freezes it
identically. There is no requested read-equality premise. -/
theorem windowBlocks_eq_original (b : Nat) (blocks : Nat → Block) :
    windowBlocks b (blocks (b-5)) (blocks (b-4))
      (blocks (b-1)) (blocks b) blocks = blocks := by
  funext slot
  unfold windowBlocks
  split_ifs with hc hp hd hb <;> subst_vars <;> rfl

/-- Actual SAME-table specialization. The finite reference is supplied
only the table's four named physical blocks; all40 block checks can thus
conclude about the one original assembledRead blocks. -/
theorem assembled_page_transfer_blocks04to39
    (blocks : Nat → Block) (b : Nat) (hb : 4 ≤ b) (hbmax : b < 40)
    (p : Nat) (hp : p < 64)
    (hclosed : readCheckBlock
      (assembledRead (referenceBlocks b (blocks (b-5)) (blocks (b-4))
        (blocks (b-1)) (blocks b)))
      (32769+4096*b+64*p) 64 = true) :
    readCheckBlock (assembledRead blocks) (32769+4096*b+64*p) 64 = true := by
  have h := window_page_transfer_blocks04to39 b hb hbmax
    (blocks (b-5)) (blocks (b-4)) (blocks (b-1)) (blocks b)
    blocks p hp hclosed
  simpa only [windowBlocks_eq_original] using h

end ImbalancedChen.OriginalStoredDelayedPageTransferSourceOnly

/-
CP outcome: source proof candidate only; noPASS.
All concrete reference-page Boolean obligations remain ROOT work. The
transfer neither certifies any numerical page nor supplies the40block
CheckedBlockTable. Checker branches, P112, original rounds, max, integer
denominators, domain endpoints and analytic consumer remain unchanged.
-/
