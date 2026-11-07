import ImbalancedChen.Certificates.OriginalNodeArraysV1.DataCore
import ImbalancedChen.Part4ActualThirdOriginalStoredNodeLocalChecker

/-!
SOURCEONLY / UNCOMPILED / OPEN30.
The second import is a PROPOSED installation name for exact source4f1c94f6
(20261024d-P4-stored-original-node-local-checker-soundness-SOURCEONLY.lean.txt).
The emitter can replace only these two import paths, never arithmetic bodies.

This reuses that source's exact integer checkedUpdate, nodeEqCheck and its
checkedUpdate_eq_original theorem. It changes the carrier from a giant global
Array to bounded trees and restates the same strong-induction consumer.
No alternative update algorithm, target-enclosure assumption, native decision
oracle or raised heartbeat/recursion budget is introduced.
-/

namespace ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly

open ImbalancedChen.OriginalU2StoredNodeBlockDataSourceOnly
open ImbalancedChen.OriginalU2StoredNodeCertificateSourceOnly
open ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly

def toOriginal (x : RawNode) : OriginalNode := ⟨x.Llo,x.Lhi,x.Hlo,x.Hhi⟩

noncomputable def assembledRead (blocks : Nat → Block) (i : Nat) : OriginalNode :=
  toOriginal (assembledRawRead blocks i)

def readCheckStep (read : Nat → OriginalNode) (i : Nat) : Bool :=
  nodeEqCheck (read i) (checkedUpdate i read)

def readCheckPrefix (read : Nat → OriginalNode) : Bool :=
  (List.range 32769).all (fun i => nodeEqCheck (read i) integerInitial)

def readCheckBlock (read : Nat → OriginalNode) (lo count : Nat) : Bool :=
  (List.range count).all (fun k => readCheckStep read (lo+k))

/-- The old array checker is exactly this checker at the array reader. -/
theorem readCheckStep_eq_array (T : StoredFourArrays) (i : Nat) :
    readCheckStep T.read i = checkStep T i := by rfl

theorem readCheckBlock_eq_array (T : StoredFourArrays) (lo count : Nat) :
    readCheckBlock T.read lo count = checkBlock T lo count := by rfl

theorem readCheckPrefix_eq_array (T : StoredFourArrays) :
    readCheckPrefix T.read = checkInitialPrefix T := by rfl

theorem readCheckStep_sound {read : Nat → OriginalNode} {i : Nat}
    (h : readCheckStep read i = true) :
    read i = originalNodeUpdate i read := by
  exact (nodeEqCheck_sound h).trans (checkedUpdate_eq_original i read)

theorem readCheckBlock_step {read : Nat → OriginalNode} {lo count k : Nat}
    (h : readCheckBlock read lo count = true) (hk : k < count) :
    readCheckStep read (lo+k) = true := by
  exact List.all_eq_true.mp h k (List.mem_range.mpr hk)

theorem readCheckBlock_sound {read : Nat → OriginalNode} {lo count k : Nat}
    (h : readCheckBlock read lo count = true) (hk : k < count) :
    read (lo+k) = originalNodeUpdate (lo+k) read := by
  exact readCheckStep_sound (readCheckBlock_step h hk)

theorem readCheckPrefix_sound {read : Nat → OriginalNode}
    (h : readCheckPrefix read = true) {i : Nat} (hi : i ≤ 32768) :
    read i = initialNode := by
  have he : read i = integerInitial := nodeEqCheck_sound
    (List.all_eq_true.mp h i (List.mem_range.mpr (by omega)))
  exact he.trans integerInitial_eq_original

theorem assembledRead_prefix (blocks : Nat → Block) (i : Nat) (hi : i ≤ 32768) :
    assembledRead blocks i = integerInitial := by
  simp only [assembledRead, assembledRawRead, if_pos hi, toOriginal,
    rawInitial, integerInitial, integerP]

/-- Structural prefix proof, not32769 repeated numerical reductions. -/
theorem assembledRead_prefix_checked (blocks : Nat → Block) :
    readCheckPrefix (assembledRead blocks) = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hi' : i ≤ 32768 := by have := List.mem_range.mp hi; omega
  rw [assembledRead_prefix blocks i hi']
  simp [nodeEqCheck]

/-- Assemble64 opaque page proofs; no page's integer work is replayed here. -/
theorem readCheckBlock_of_64_pages (read : Nat → OriginalNode) (lo : Nat)
    (h : ∀ p : Nat, p < 64 → readCheckBlock read (lo+64*p) 64 = true) :
    readCheckBlock read lo 4096 = true := by
  apply List.all_eq_true.mpr
  intro k hk
  have hk' : k < 4096 := List.mem_range.mp hk
  let p := k/64
  let r := k%64
  have hp : p < 64 := by dsimp [p]; omega
  have hr : r < 64 := by dsimp [r]; omega
  have he : lo+64*p+r = lo+k := by dsimp [p, r]; omega
  have hs : readCheckStep read (lo+64*p+r) = true :=
    readCheckBlock_step (h p hp) hr
  simpa only [he] using hs

/-- Same noncircular local-equation consumer as source4f1c, now on a bounded
reader. All40 block obligations concern the SAME read function. -/
theorem checked_block_reader_encloses (read : Nat → OriginalNode)
    (hprefix : readCheckPrefix read = true)
    (hchunks : ∀ b : Fin 40,
      readCheckBlock read (32769+4096*b.val) 4096 = true) :
    ∀ i : Nat, 32768 ≤ i → i ≤ 196608 → NodeEncloses (read i) i := by
  have hsteps : ∀ i : Nat, 32769 ≤ i → i ≤ 196608 →
      read i = originalNodeUpdate i read := by
    intro i hi himax
    let b := (i-32769)/4096
    let k := (i-32769)%4096
    have hb : b < 40 := by dsimp [b]; omega
    have hk : k < 4096 := by dsimp [k]; omega
    have he : 32769+4096*b+k = i := by dsimp [b, k]; omega
    have hr : read (32769+4096*b+k) =
        originalNodeUpdate (32769+4096*b+k) read :=
      readCheckBlock_sound (hchunks ⟨b,hb⟩) hk
    simpa only [he] using hr
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hlow hhigh
      by_cases hi : i = 32768
      · subst i
        rw [readCheckPrefix_sound hprefix (by omega : 32768 ≤ 32768)]
        exact initialNode_encloses
      · have hi' : 32769 ≤ i := by omega
        rw [hsteps i hi' hhigh]
        apply originalNodeUpdate_preserves actualWeightedCellRemainders i hlow read
        intro j hj hjlow
        exact ih j hj hjlow (by omega)

/-- No concrete instance is supplied by this source or by an uncompiled pilot.
Every check must be proved for the exact same immutable block function. -/
structure CheckedBlockTable where
  blocks : Nat → Block
  checked : ∀ b : Fin 40,
    readCheckBlock (assembledRead blocks) (32769+4096*b.val) 4096 = true

theorem CheckedBlockTable.encloses (T : CheckedBlockTable) (i : Nat)
    (hi : 32768 ≤ i) (himax : i ≤ 196608) :
    NodeEncloses (assembledRead T.blocks i) i := by
  exact checked_block_reader_encloses (assembledRead T.blocks)
    (assembledRead_prefix_checked T.blocks) T.checked i hi himax

end ImbalancedChen.OriginalU2StoredNodeBlockCheckerSourceOnly
