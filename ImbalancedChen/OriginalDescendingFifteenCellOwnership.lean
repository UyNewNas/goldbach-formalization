import ImbalancedChen.P4ASlot17DescendingChargedFrontier

/-!
SOURCE ONLY / UNCOMPILED. Literal strict descending129 fifteen-cell
branch payload, read without executing its producer or certifier.

Source navigation: eighth-prefix-family-20261009-descending-navigation.json,
SHA256 420ec389ac361a175bd429ab9bf4215fc42a4e1ec7a7e382f244773ea98083b1.
Independent semantics producer: eighth-prefix-descending-independent-20261009.py,
SHA256 ebbb4830d6e73294715f064f2eb59555a28d502081e7f2fd82b14566bc3e608e.
The fifteen left-pattern lists below are the navigation's literal lists;
the right pattern is the complement in masks 1 through 63. The rows are
the producer's named strict inequalities, with the winning mask6 row
omitted exactly as in the producer. Full and selected-complement squares
remain inside the cell. Boundary points belong to no strict cell.

No simplex/Jensen floor, global payload validation, actual third-cap
approximation or existence of an arithmetic frontier is asserted.
-/

namespace ImbalancedChen.OriginalDescendingFifteenCellOwnership

noncomputable section
open scoped Classical BigOperators
open P2OriginalDescendingEighthLogSemantics
open VariableEnvelope

/-- The fifteen independently published descending branch patterns. -/
def leftMasks : Fin 15 → Finset ℕ :=
  ![{1,2,4,8,10,12,16,18,20,24,26,28,32,34,36,40,42,44,48,50,52,56,58,60},
    {1,2,4,8,10,12,16,18,20,24,26,28,32,34,36,40,42,44,48,50,52,56,60},
    {1,2,4,8,10,12,16,18,20,24,26,28,32,34,36,40,42,44,48,50,52,56},
    {1,2,4,8,10,12,16,18,20,24,28,32,34,36,40,42,44,48,50,52,56,60},
    {1,2,4,8,10,12,16,18,20,24,28,32,34,36,40,42,44,48,50,52,56},
    {1,2,4,8,10,12,16,18,20,24,32,34,36,40,42,44,48,50,52,56},
    {1,2,4,8,10,12,16,18,20,24,28,32,34,36,40,44,48,50,52,56,60},
    {1,2,4,8,10,12,16,18,20,24,28,32,34,36,40,44,48,50,52,56},
    {1,2,4,8,10,12,16,18,20,24,28,32,34,36,40,44,48,52,56,60},
    {1,2,4,8,10,12,16,18,20,24,28,32,34,36,40,44,48,52,56},
    {1,2,4,8,10,12,16,18,20,24,32,34,36,40,44,48,50,52,56},
    {1,2,4,8,10,12,16,18,20,24,32,34,36,40,44,48,52,56},
    {1,2,4,8,10,12,16,18,20,24,32,34,36,40,48,50,52,56},
    {1,2,4,8,10,12,16,18,20,24,32,34,36,40,48,52,56},
    {1,2,4,8,10,12,16,18,20,24,32,34,36,40,48,56}]

theorem leftMasks_injective : Function.Injective leftMasks := by decide

theorem leftMasks_subset (i : Fin 15) : leftMasks i ⊆ Finset.Icc 1 63 := by
  fin_cases i <;> decide

theorem six_not_left (i : Fin 15) : 6 ∉ leftMasks i := by
  fin_cases i <;> decide

/-- Bit j selects the original processing coordinate tj, only j<6. -/
def maskSlots (m : ℕ) : Finset (Fin 8) :=
  Finset.univ.filter (fun j => j.val < 6 ∧ m.testBit j.val = true)

def subsetSum (m : ℕ) (t : Point) : ℝ := ∑ j ∈ maskSlots m, t j

def branchPlane (i : Fin 15) (m : ℕ) (t : Point) : ℝ :=
  if m ∈ leftMasks i then A (subsetSum m t) else C (subsetSum m t)

/-- This is the producer's semantic system of 96 strict affine rows.
Every square is retained, including all six selected129 complements. -/
structure StrictRows (i : Fin 15) (t : Point) : Prop where
  largest : t 0 < mu
  thirdFloor : (1 / 100 : ℝ) < t 2
  lastFloor : (53 / 13824 : ℝ) < t 7
  order : ∀ j : Fin 7, t j.succ < t j.castSucc
  firstHistory : 3 * t 0 < oldRaw t
  thirdHistory : history3 t < oldRaw t
  fifthHistory : history5 t < oldRaw t
  seventhHistory : history7 t < oldRaw t
  oldWinner : mu < d t
  oldW : VariableEnvelope.cap - 3 * t 2 / 8 < oldRaw t
  improvement : oldRaw t < newCap t
  descending : mu < selectedSum t
  fullSquares : ∀ j : Fin 8, prefixSquareExpr t j < newCap t
  complementSquares : ∀ j : Fin 8, j ≠ 0 → j ≠ 7 →
    selectedSum t + (∑ k ∈ Finset.univ.filter (fun k : Fin 8 => 0 < k ∧ k < j), t k) +
      2 * t j < newCap t
  oldResidual : total t + t 7 < oldRaw t
  terminal : newCap t < total t + 3 * t 7
  branches : ∀ m ∈ Finset.Icc 1 63, m ≠ 6 → branchPlane i m t < oldRaw t

def cell (i : Fin 15) : Set Point := {t | StrictRows i t}

/-- Literal different masks give a separating left/right branch. The
winning mask6 cannot be the separator, because it is right in all cells. -/
private theorem exists_separator {i j : Fin 15} (hij : i ≠ j) :
    ∃ m ∈ Finset.Icc 1 63, m ≠ 6 ∧
      ((m ∈ leftMasks i ∧ m ∉ leftMasks j) ∨
        (m ∈ leftMasks j ∧ m ∉ leftMasks i)) := by
  have hne : leftMasks i ≠ leftMasks j := fun h => hij (leftMasks_injective h)
  by_cases hsub : leftMasks i ⊆ leftMasks j
  · have hnot : ¬leftMasks j ⊆ leftMasks i :=
      fun h => hne (Finset.Subset.antisymm hsub h)
    obtain ⟨m, hm, hnotm⟩ := Finset.not_subset.mp hnot
    exact ⟨m, leftMasks_subset j hm, (fun h => six_not_left j (h ▸ hm)),
      Or.inr ⟨hm, hnotm⟩⟩
  · obtain ⟨m, hm, hnotm⟩ := Finset.not_subset.mp hsub
    exact ⟨m, leftMasks_subset i hm, (fun h => six_not_left i (h ▸ hm)),
      Or.inl ⟨hm, hnotm⟩⟩

/-- No overlap multiplicity is introduced by the fifteen literal strict
cells. The forbidden positive gap rules out opposing branch planes. -/
theorem strict_cells_disjoint {i j : Fin 15} (hij : i ≠ j) :
    Disjoint (cell i) (cell j) := by
  apply Set.disjoint_left.mpr
  intro t hi hj
  obtain ⟨m, hm, hm6, hsep⟩ := exists_separator hij
  have hpi := hi.branches m hm hm6
  have hpj := hj.branches m hm hm6
  rcases hsep with ⟨hmi, hmj⟩ | ⟨hmj, hmi⟩
  · rw [branchPlane, if_pos hmi] at hpi
    rw [branchPlane, if_neg hmj] at hpj
    exact chosen_planes_incompatible hi.oldWinner (subsetSum m t) ⟨hpi.le, hpj.le⟩
  · rw [branchPlane, if_neg hmi] at hpi
    rw [branchPlane, if_pos hmj] at hpj
    exact chosen_planes_incompatible hi.oldWinner (subsetSum m t) ⟨hpj.le, hpi.le⟩

theorem owner_unique {i j : Fin 15} {t : Point}
    (hi : StrictRows i t) (hj : StrictRows j t) : i = j := by
  by_contra hij
  exact Set.disjoint_left.mp (strict_cells_disjoint hij) hi hj

/-- A tied branch row is excluded arithmetically; no measure-zero
argument removes the corresponding integer history. -/
theorem branch_tie_not_owned (i : Fin 15) (m : ℕ) (t : Point)
    (hm : m ∈ Finset.Icc 1 63) (hm6 : m ≠ 6)
    (heq : branchPlane i m t = oldRaw t) : ¬StrictRows i t := by
  intro h
  exact (ne_of_lt (h.branches m hm hm6)) heq

/-- On the descending old-winner side a tie with either affine plane is
outside the entire adopted union, not merely outside one branch pattern. -/
theorem plane_tie_outside_all (m : ℕ) (t : Point)
    (hm : m ∈ Finset.Icc 1 63) (hm6 : m ≠ 6) (hd : mu < d t)
    (heq : A (subsetSum m t) = oldRaw t ∨ C (subsetSum m t) = oldRaw t) :
    ∀ i : Fin 15, ¬StrictRows i t := by
  intro i h
  have hb := h.branches m hm hm6
  by_cases hmi : m ∈ leftMasks i
  · rw [branchPlane, if_pos hmi] at hb
    rcases heq with heq | heq
    · exact (ne_of_lt hb) heq
    · exact chosen_planes_incompatible hd (subsetSum m t) ⟨hb.le, heq.le⟩
  · rw [branchPlane, if_neg hmi] at hb
    rcases heq with heq | heq
    · exact chosen_planes_incompatible hd (subsetSum m t) ⟨heq.le, hb.le⟩
    · exact (ne_of_lt hb) heq

theorem coordinates_pos {i : Fin 15} {t : Point} (h : StrictRows i t) :
    ∀ j, 0 < t j := by
  have hlast : 0 < t 7 := lt_trans (by norm_num) h.lastFloor
  have h0 := h.order 0
  have h1 := h.order 1
  have h2 := h.order 2
  have h3 := h.order 3
  have h4 := h.order 4
  have h5 := h.order 5
  have h6 := h.order 6
  norm_num at h0 h1 h2 h3 h4 h5 h6
  intro j
  fin_cases j <;> linarith

/-- Literal owned rows enter the EXISTING original descending action once
the actual inherited parent has passed rank7 and is below its raw envelope.
These parent facts remain actual policy obligations, not fabricated data. -/
theorem rows_descendingGuard {i : Fin 15} {t : Point} (h : StrictRows i t)
    (current : ℝ) (hHistory : history7 t < current) (hCap : current ≤ oldRaw t) :
    P4ASlot17DescendingChargedFrontierSourceOnly.DescendingRows t current where
  coordinates := coordinates_pos h
  lastOrder := by simpa using h.order 6
  seventhHistory := hHistory
  parentUpper := hCap
  improvement := h.improvement
  terminal := by linarith [h.terminal]
  descendingSide := h.descending

/-- On an owned arithmetic history, the original action actually selects
the descending cap. No ownership predicate is supplied by the caller. -/
theorem owned_history_raisedExponent
    (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) (i : Fin 15)
    (hRows : StrictRows i (primeHistoryLogCoordinates N 8 pre))
    (hHistory : history7 (primeHistoryLogCoordinates N 8 pre) <
      P4ASlot17DescendingChargedFrontierSourceOnly.inheritedSixth lambda6 pre)
    (hCap : P4ASlot17DescendingChargedFrontierSourceOnly.inheritedSixth lambda6 pre ≤
      oldRaw (primeHistoryLogCoordinates N 8 pre)) :
    P4ASlot17DescendingChargedFrontierSourceOnly.raisedExponent N lambda6 pre =
      newCap (primeHistoryLogCoordinates N 8 pre) := by
  unfold P4ASlot17DescendingChargedFrontierSourceOnly.raisedExponent
  dsimp only
  exact if_pos (rows_descendingGuard hRows _ hHistory hCap)

/-- Restrict the existing original descending action to the literal
adopted strict union. Histories outside it, including its row ties,
inherit their sixth parent rather than being dropped from the sieve. -/
def ownedRaisedExponent (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) : ℝ :=
  if ∃ i : Fin 15, StrictRows i (primeHistoryLogCoordinates N 8 pre) then
    P4ASlot17DescendingChargedFrontierSourceOnly.raisedExponent N lambda6 pre
  else P4ASlot17DescendingChargedFrontierSourceOnly.inheritedSixth lambda6 pre

theorem ownedRaisedExponent_eq_original_action
    (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) (i : Fin 15)
    (hi : StrictRows i (primeHistoryLogCoordinates N 8 pre)) :
    ownedRaisedExponent N lambda6 pre =
      P4ASlot17DescendingChargedFrontierSourceOnly.raisedExponent N lambda6 pre :=
  if_pos ⟨i, hi⟩

theorem ownedRaisedExponent_eq_parent_outside
    (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ)
    (houtside : ∀ i : Fin 15, ¬StrictRows i (primeHistoryLogCoordinates N 8 pre)) :
    ownedRaisedExponent N lambda6 pre =
      P4ASlot17DescendingChargedFrontierSourceOnly.inheritedSixth lambda6 pre := by
  exact if_neg (by rintro ⟨i, hi⟩; exact houtside i hi)

theorem ownedRaisedExponent_eq_selected_cap
    (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) (i : Fin 15)
    (hRows : StrictRows i (primeHistoryLogCoordinates N 8 pre))
    (hHistory : history7 (primeHistoryLogCoordinates N 8 pre) <
      P4ASlot17DescendingChargedFrontierSourceOnly.inheritedSixth lambda6 pre)
    (hCap : P4ASlot17DescendingChargedFrontierSourceOnly.inheritedSixth lambda6 pre ≤
      oldRaw (primeHistoryLogCoordinates N 8 pre)) :
    ownedRaisedExponent N lambda6 pre = newCap (primeHistoryLogCoordinates N 8 pre) := by
  rw [ownedRaisedExponent_eq_original_action N lambda6 pre i hRows]
  exact owned_history_raisedExponent N lambda6 pre i hRows hHistory hCap

theorem ownedRaisedExponent_inherits_at_plane_tie
    (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) (m : ℕ)
    (hm : m ∈ Finset.Icc 1 63) (hm6 : m ≠ 6)
    (hd : mu < d (primeHistoryLogCoordinates N 8 pre))
    (heq : A (subsetSum m (primeHistoryLogCoordinates N 8 pre)) =
        oldRaw (primeHistoryLogCoordinates N 8 pre) ∨
      C (subsetSum m (primeHistoryLogCoordinates N 8 pre)) =
        oldRaw (primeHistoryLogCoordinates N 8 pre)) :
    ownedRaisedExponent N lambda6 pre =
      P4ASlot17DescendingChargedFrontierSourceOnly.inheritedSixth lambda6 pre :=
  ownedRaisedExponent_eq_parent_outside N lambda6 pre
    (plane_tie_outside_all m _ hm hm6 hd heq)

/-- The owned action is placed after rank eight on the existing parent,
so every selected prefix, sign, mass and remaining carrier is preserved. -/
def ownedPolicy (N : ℝ) (lambda6 : List ℕ → ℝ)
    (parent : Bool → List ℕ → Bool) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 8 parent
    (frozenParityRosserPolicy false 8 (fun pre => N ^ ownedRaisedExponent N lambda6 pre))

theorem ownedPolicy_frontier_eight
    (N : ℝ) (lambda6 : List ℕ → ℝ) (parent : Bool → List ℕ → Bool)
    (h : ℕ → ℝ) (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 8 (ownedPolicy N lambda6 parent) h pre positive mass carrier =
      firstExitDepthFrontier 8 parent h pre positive mass carrier :=
  firstExitDepthFrontier_depthSplice_eq 8 8 le_rfl parent _ h pre carrier positive mass

end
end ImbalancedChen.OriginalDescendingFifteenCellOwnership
