import ImbalancedChen.P5OriginalAdoptedEighthPhysicalMasks
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The manuscript constructs 87 eighth cells by assigning one of the two
affine upper planes to each of the 63 nonempty old first-six masks, then
adjoining full and selected-complement physical square rows. This file
makes that finite row generator literal and records the only complete
old-plane assignments present in the compact package: the fifteen
descending mask129 cells. Missing assignments are `none`, never a made-up
default pattern. The 87-cell policy binding remains open.

The descending left-mask codes below are transcribed from
`verification/data/eighth-prefix-descending-independent-20261009.json`,
not numerically replayed. Their owner indices are 15,...,29 in the
30+15+13+29 family. The other independent JSONs contain integral summaries
and SHA bindings, but not complete old-plane row assignments.
-/

namespace ImbalancedChen.P5OriginalEighthAffineRowRecipe

noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open P5OriginalAdoptedEighthPhysicalMasks

abbrev OldMask := Finset (Fin 6)

def oldMasks : Finset OldMask := Finset.univ.erase ∅
def fullSlots : Finset (Fin 8) := Finset.univ
def remainingSlots (i : Cell) : Finset (Fin 8) := Finset.univ \ selectedMask i

theorem oldMasks_card : oldMasks.card = 63 := by decide
theorem fullSlots_card : fullSlots.card = 8 := by decide
theorem mask129_remaining_card : (Finset.univ \ mask129 : Finset (Fin 8)).card = 6 := by decide
theorem mask138_remaining_card : (Finset.univ \ mask138 : Finset (Fin 8)).card = 5 := by decide
theorem mask184_remaining_card : (Finset.univ \ mask184 : Finset (Fin 8)).card = 4 := by decide
theorem mask134_remaining_card : (Finset.univ \ mask134 : Finset (Fin 8)).card = 5 := by decide

/-- The three common indexed parts of the physical affine recipe have
63 old planes, eight complete squares, and the exact mask complement.
Other order, history, active-side and terminal rows are kept separately. -/
def commonPhysicalRowCount (i : Cell) : ℕ :=
  oldMasks.card + fullSlots.card + (remainingSlots i).card

theorem equal_cell_common_rows (i : Cell) (hi : i.val < 30) :
    commonPhysicalRowCount i = 77 := by
  simp [commonPhysicalRowCount, remainingSlots, selectedMask, hi,
    oldMasks_card, fullSlots_card, mask129_remaining_card]

theorem unequal_winner9_common_rows (i : Cell)
    (hlo : 30 ≤ i.val) (hhi : i.val < 43) :
    commonPhysicalRowCount i = 76 := by
  have hnot : ¬ i.val < 30 := by omega
  have h43 : i.val ≠ 43 := by omega
  have h44 : i.val ≠ 44 := by omega
  simp [commonPhysicalRowCount, remainingSlots, selectedMask,
    hnot, h43, h44, oldMasks_card, fullSlots_card,
    mask138_remaining_card]

theorem winner50A_common_rows (i : Cell) (hi : i.val = 43) :
    commonPhysicalRowCount i = 75 := by
  have hnot : ¬ i.val < 30 := by omega
  simp [commonPhysicalRowCount, remainingSlots, selectedMask,
    hnot, hi, oldMasks_card, fullSlots_card, mask184_remaining_card]

theorem winner50D_common_rows (i : Cell) (hi : i.val = 44) :
    commonPhysicalRowCount i = 76 := by
  have hnot : ¬ i.val < 30 := by omega
  have h43 : i.val ≠ 43 := by omega
  simp [commonPhysicalRowCount, remainingSlots, selectedMask,
    hnot, h43, hi, oldMasks_card, fullSlots_card, mask134_remaining_card]

theorem later_common_rows (i : Cell) (hi : 45 ≤ i.val) :
    commonPhysicalRowCount i = 76 := by
  have hnot : ¬ i.val < 30 := by omega
  have h43 : i.val ≠ 43 := by omega
  have h44 : i.val ≠ 44 := by omega
  simp [commonPhysicalRowCount, remainingSlots, selectedMask,
    hnot, h43, h44, oldMasks_card, fullSlots_card, mask138_remaining_card]

/-- A subset of the first six physical labels is encoded as the literal
binary mask used by the original independent cell record. -/
def oldMaskCode (I : OldMask) : ℕ := ∑ j ∈ I, 2 ^ j.val

def oldSubsetSum (t : Point) (I : OldMask) : ℝ :=
  ∑ j ∈ I, t ⟨j.val, by omega⟩

/-- The actual 63 affine upper-plane inequalities for one published
pattern. The code set selects the ascending A plane; its complement
selects the descending C plane. The winning old subset may be an
identity and is not silently forced strict. -/
def oldPlaneRows (i : Cell) (leftCodes : Finset ℕ) (t : Point) : Prop :=
  ∀ I ∈ oldMasks,
    (if oldMaskCode I ∈ leftCodes then A (oldSubsetSum t I)
      else C (oldSubsetSum t I)) ≤ oldComparison i t

/-- The two physical square families are generated at the SAME new
eighth level. They are independent of auxiliary enumeration covers. -/
def fullSquareRows (i : Cell) (t : Point) : Prop :=
  ∀ j ∈ fullSlots, prefixSquareExpr t j < newCap i t

def selectedComplementRows (i : Cell) (t : Point) : Prop :=
  ∀ j ∈ remainingSlots i,
    selectedSquareExpr (selectedMask i) t j < newCap i t

theorem selectedComplementRows_iff (i : Cell) (t : Point) :
    selectedComplementRows i t ↔
      ∀ j ∉ selectedMask i,
        selectedSquareExpr (selectedMask i) t j < newCap i t := by
  simp [selectedComplementRows, remainingSlots]

/-- Strict descending129 complete old-plane assignments present in the
independent compact record, in its recorded cell_id order 0,...,14. -/
def descendingLeftCodes : Fin 15 → Finset ℕ :=
  ![{1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 26, 28, 32, 34, 36, 40, 42, 44, 48, 50, 52, 56, 58, 60},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 26, 28, 32, 34, 36, 40, 42, 44, 48, 50, 52, 56, 60},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 26, 28, 32, 34, 36, 40, 42, 44, 48, 50, 52, 56},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 28, 32, 34, 36, 40, 42, 44, 48, 50, 52, 56, 60},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 28, 32, 34, 36, 40, 42, 44, 48, 50, 52, 56},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 32, 34, 36, 40, 42, 44, 48, 50, 52, 56},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 28, 32, 34, 36, 40, 44, 48, 50, 52, 56, 60},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 28, 32, 34, 36, 40, 44, 48, 50, 52, 56},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 28, 32, 34, 36, 40, 44, 48, 52, 56, 60},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 28, 32, 34, 36, 40, 44, 48, 52, 56},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 32, 34, 36, 40, 44, 48, 50, 52, 56},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 32, 34, 36, 40, 44, 48, 52, 56},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 32, 34, 36, 40, 48, 50, 52, 56},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 32, 34, 36, 40, 48, 52, 56},
    {1, 2, 4, 8, 10, 12, 16, 18, 20, 24, 32, 34, 36, 40, 48, 56}]

def descendingGlobalCell (j : Fin 15) : Cell := ⟨15 + j.val, by omega⟩

theorem descending_index_range (j : Fin 15) :
    15 ≤ (descendingGlobalCell j).val ∧ (descendingGlobalCell j).val < 30 := by
  dsimp [descendingGlobalCell]
  omega

theorem descending_mask129 (j : Fin 15) :
    selectedMask (descendingGlobalCell j) = mask129 := by
  have h := (descending_index_range j).2
  simp [selectedMask, h]

/-- Only the fifteen literal pattern records are present. `none` for any
other index is a provenance fact, not a default old-plane assignment. -/
def compactPackageOldPlanes (i : Cell) : Option (Finset ℕ) :=
  if h : 15 ≤ i.val ∧ i.val < 30 then
    some (descendingLeftCodes ⟨i.val - 15, by omega⟩)
  else none

theorem descending_pattern_present (j : Fin 15) :
    compactPackageOldPlanes (descendingGlobalCell j) = some (descendingLeftCodes j) := by
  have h := descending_index_range j
  have heq : (⟨(descendingGlobalCell j).val - 15, by omega⟩ : Fin 15) = j := by
    apply Fin.ext
    dsimp [descendingGlobalCell]
    omega
  simp [compactPackageOldPlanes, h, heq]

theorem absent_outside_descending (i : Cell)
    (h : i.val < 15 ∨ 30 ≤ i.val) : compactPackageOldPlanes i = none := by
  have hnot : ¬ (15 ≤ i.val ∧ i.val < 30) := by omega
  simp [compactPackageOldPlanes, hnot]

/-- The available literal plane map covers 15 of the 87 published cell
labels. The other 72 require their absent source row files or a new
verified finite reconstruction; no source-only proof below equates them
with arbitrary assignments. -/
theorem available_and_missing_counts :
    (Finset.Ico 15 30).card = 15 ∧ 87 - (Finset.Ico 15 30).card = 72 := by
  norm_num

end
end ImbalancedChen.P5OriginalEighthAffineRowRecipe
