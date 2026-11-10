import ImbalancedChen.P5OriginalEighthNavigationMap
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal 87-cell old-plane map is now joined to the original physical
row recipe. The bag has one indexed row for every nonempty old first-six
mask, one for every full square, and one for every remaining selected
square. Distinct tags keep multiplicities even when formulas coincide.
The Phase3 signed rho policy uses the same selected mask for its chosen
eighth guard. Neither affine feasibility nor common ancestor selection
is proved here.
-/

namespace ImbalancedChen.P5OriginalEighthPhysicalRowBag

noncomputable section
open P5OriginalAdoptedEighthPhysicalMasks
open P5OriginalEighthAffineRowRecipe
open P5OriginalEighthNavigationMap

inductive RowTag where
  | old (I : OldMask)
  | full (j : Fin 8)
  | selectedComplement (j : Fin 8)
  deriving DecidableEq

/-- The exact physical common-row multiset at an actual published slot.
The 63 old rows are evaluated with that slot's literal A/D assignment. -/
def physicalRowBag (i : Cell) : Multiset RowTag :=
  (oldMasks.val.map RowTag.old) +
    (fullSlots.val.map RowTag.full) +
    ((remainingSlots i).val.map RowTag.selectedComplement)

def rowHolds (i : Cell) (leftCodes : Finset ℕ) (t : Point) : RowTag → Prop
  | .old I =>
      (if oldMaskCode I ∈ leftCodes then A (oldSubsetSum t I)
        else C (oldSubsetSum t I)) ≤ oldComparison i t
  | .full j => prefixSquareExpr t j < newCap i t
  | .selectedComplement j =>
      selectedSquareExpr (selectedMask i) t j < newCap i t

theorem physical_row_bag_holds_iff (i : Cell) (leftCodes : Finset ℕ)
    (t : Point) :
    (∀ r ∈ physicalRowBag i, rowHolds i leftCodes t r) ↔
      oldPlaneRows i leftCodes t ∧ fullSquareRows i t ∧
        selectedComplementRows i t := by
  simp [physicalRowBag, rowHolds, oldPlaneRows, fullSquareRows,
    selectedComplementRows]

/-- No pattern is assigned by a default value: the Phase10 `Option`
lookup must be present at each of the 87 published owner slots. -/
theorem actual_row_bag_iff (i : Cell) (t : Point) :
    (∃ leftCodes, adoptedOldPlanes i = some leftCodes ∧
      ∀ r ∈ physicalRowBag i, rowHolds i leftCodes t r) ↔
        adoptedPhysicalSquareAndPlaneRows i t := by
  cases h : adoptedOldPlanes i with
  | none =>
      have hs := adopted_old_planes_all i
      simp [h] at hs
  | some leftCodes =>
      simp [adoptedPhysicalSquareAndPlaneRows, h,
        physical_row_bag_holds_iff]

theorem physical_row_bag_card (i : Cell) :
    (physicalRowBag i).card = commonPhysicalRowCount i := by
  simp [physicalRowBag, commonPhysicalRowCount]

theorem equal_parent_row_card (i : Cell) (hi : i.val < 30) :
    (physicalRowBag i).card = 77 := by
  rw [physical_row_bag_card]
  exact equal_cell_common_rows i hi

theorem winner9_row_card (i : Cell)
    (hlo : 30 ≤ i.val) (hhi : i.val < 43) :
    (physicalRowBag i).card = 76 := by
  rw [physical_row_bag_card]
  exact unequal_winner9_common_rows i hlo hhi

theorem winner50A_row_card (i : Cell) (hi : i.val = 43) :
    (physicalRowBag i).card = 75 := by
  rw [physical_row_bag_card]
  exact winner50A_common_rows i hi

theorem winner50D_row_card (i : Cell) (hi : i.val = 44) :
    (physicalRowBag i).card = 76 := by
  rw [physical_row_bag_card]
  exact winner50D_common_rows i hi

theorem later_row_card (i : Cell) (hi : 45 ≤ i.val) :
    (physicalRowBag i).card = 76 := by
  rw [physical_row_bag_card]
  exact later_common_rows i hi

/-- Every one of the 87 global slots has its exact common physical
row multiplicity. The unequal winner50 A slot is the sole 75-row case. -/
theorem every_slot_row_card (i : Cell) :
    (physicalRowBag i).card =
      if i.val < 30 then 77 else if i.val = 43 then 75 else 76 := by
  split_ifs with h30 h43
  · exact equal_parent_row_card i h30
  · exact winner50A_row_card i h43
  · have hlo : 30 ≤ i.val := by omega
    by_cases hlt : i.val < 43
    · exact winner9_row_card i hlo hlt
    · by_cases h44 : i.val = 44
      · exact winner50D_row_card i h44
      · exact later_row_card i (by omega)

/-- The very cell chosen by the Phase3 eighth guard uses these full and
selected-complement square rows at the exponent used by its policy. -/
theorem chosen_guard_square_rows
    (N : ℝ) (lambda3 lambda6 : List ℕ → ℝ) (pre : List ℕ)
    (h : adoptedGuard N lambda3 lambda6 pre) :
    let i := Classical.choose h
    let t := primeHistoryLogCoordinates N 8 pre
    raisedExponent N lambda3 lambda6 pre = newCap i t ∧
      fullSquareRows i t ∧ selectedComplementRows i t := by
  dsimp
  have hs := Classical.choose_spec h
  refine ⟨?_, ?_, ?_⟩
  · simp [raisedExponent, h]
  · intro j _
    exact hs.full_squares j
  · intro j hj
    exact hs.complement_squares j (Finset.mem_sdiff.mp hj).2

/-- The same Phase3 family policy supplies the signed physical rho,
supported on squarefree moduli coprime to N and bounded by one. Its
chosen eighth mask has the physical square rows above. -/
theorem chosen_guard_signed_rho_support
    (N cap : ℕ) (w z L : ℝ) (lambda3 lambda6 : List ℕ → ℝ)
    (base : Bool → List ℕ → Bool) (pre : List ℕ)
    (h : adoptedGuard (N : ℝ) lambda3 lambda6 pre) (q : ℕ)
    (hq : actualSmallRoughRho
      ((familyPolicy (N : ℝ) lambda3 lambda6 base) false) N cap w z L q ≠ 0) :
    let i := Classical.choose h
    let t := primeHistoryLogCoordinates (N : ℝ) 8 pre
    (raisedExponent (N : ℝ) lambda3 lambda6 pre = newCap i t ∧
      fullSquareRows i t ∧ selectedComplementRows i t) ∧
    q ∈ actualSmallRoughModuli
      ((familyPolicy (N : ℝ) lambda3 lambda6 base) false) N cap w z ∧
    Squarefree q ∧ q.Coprime N ∧
    |actualSmallRoughRho
      ((familyPolicy (N : ℝ) lambda3 lambda6 base) false) N cap w z L q| ≤ 1 := by
  dsimp
  exact ⟨chosen_guard_square_rows (N : ℝ) lambda3 lambda6 pre h,
    adopted_nonzero_physical_support N cap w z L lambda3 lambda6 base q hq⟩

end
end ImbalancedChen.P5OriginalEighthPhysicalRowBag
