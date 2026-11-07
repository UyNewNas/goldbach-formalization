import ImbalancedChen.P4ASlot19ChargedFrontier

/-!
SOURCE ONLY / UNCOMPILED. Literal A23/s23_low ascending13 branch payload
from navigation48e7b215239e9236f3e4d632a228f3a11a2161aa43d16b79257758de7107ecb4.
The selected alternative contains13cells and97 strict affine rows each.
The ascending new-license row and raw winner9 row are identically zero;
they are identities, not strict inequalities. All eight full squares and
five selected138 complement squares remain in the domain. No floating
navigation exclusion, simplex floor or adopted third/sixth provenance is
claimed. Row ties inherit the actual parent rather than deleting integers.
-/
namespace ImbalancedChen.OriginalAscendingThirteenCellOwnership
noncomputable section
open scoped Classical BigOperators
open P2OriginalThirdMinorantLogDictionarySourceOnly VariableEnvelope

def leftMasks : Fin 13 → Finset ℕ :=
  ![{1,2,4,6,8,9,10,12,16,17,18,20,24,28,32,33,34,36,40,44,48,49,50,52,56},
    {1,2,4,6,8,9,10,12,16,17,18,20,24,28,32,33,34,36,40,44,48,50,52,56,60},
    {1,2,4,6,8,9,10,12,16,17,18,20,24,28,32,33,34,36,40,44,48,50,52,56},
    {1,2,4,6,8,9,10,12,16,17,18,20,24,28,32,33,34,36,40,44,48,52,56,60},
    {1,2,4,6,8,9,10,12,16,17,18,20,24,28,32,33,34,36,40,44,48,52,56},
    {1,2,4,6,8,9,10,12,16,17,18,20,24,32,33,34,36,40,44,48,49,50,52,56},
    {1,2,4,6,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,49,50,52,56},
    {1,2,4,6,8,9,10,12,16,17,18,20,24,32,33,34,36,40,44,48,50,52,56},
    {1,2,4,6,8,9,10,12,16,17,18,20,24,32,33,34,36,40,44,48,52,56},
    {1,2,4,6,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,50,52,56},
    {1,2,4,6,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,52,56},
    {1,2,4,6,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,56},
    {1,2,4,6,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48}]

theorem leftMasks_injective : Function.Injective leftMasks := by decide
theorem leftMasks_subset (i : Fin 13) : leftMasks i ⊆ Finset.Icc 1 63 := by
  fin_cases i <;> decide
theorem nine_left (i : Fin 13) : 9 ∈ leftMasks i := by fin_cases i <;> decide

def maskSlots (m : ℕ) : Finset (Fin 8) :=
  Finset.univ.filter (fun j => j.val < 6 ∧ m.testBit j.val = true)
def subsetSum (m : ℕ) (t : Point) : ℝ := ∑ j ∈ maskSlots m, t j
def branchPlane (i : Fin 13) (m : ℕ) (t : Point) : ℝ :=
  if m ∈ leftMasks i then A (subsetSum m t) else C (subsetSum m t)

structure StrictRows (i : Fin 13) (t : Point) : Prop where
  largest : t 0 < mu
  thirdFloor : (1 / 100 : ℝ) < t 2
  lastFloor : (53 / 13824 : ℝ) < t 7
  order : ∀ j : Fin 7, t j.succ < t j.castSucc
  firstHistory : 3 * t 0 < thirdMinorant t
  thirdHistory : history3 t < thirdMinorant t
  fifthHistory : history5 t < thirdMinorant t
  seventhHistory : history7 t < thirdMinorant t
  aboveThird : thirdMinorant t < comparisonCap t
  oldWinner : t 0 + t 3 < mu
  oldW : VariableEnvelope.cap - 3 * t 2 / 8 < comparisonCap t
  ascendingThird : t 1 + t 2 < mu
  improvement : comparisonCap t < newCap t
  ascendingNew : selectedSum t < mu
  fullSquares : ∀ j : Fin 8, prefixSquareExpr t j < newCap t
  complementSquares : ∀ j : Fin 8, j ≠ 1 → j ≠ 3 → j ≠ 7 →
    selectedSum t + (∑ k ∈ Finset.univ.filter
      (fun k : Fin 8 => k < j ∧ k ≠ 1 ∧ k ≠ 3 ∧ k ≠ 7), t k) + 2 * t j < newCap t
  oldResidual : total t + t 7 < comparisonCap t
  terminal : newCap t < total t + 3 * t 7
  branches : ∀ m ∈ Finset.Icc 1 63, m ≠ 9 → branchPlane i m t < comparisonCap t

def cell (i : Fin 13) : Set Point := {t | StrictRows i t}

theorem ascending_license_identity (t : Point) :
    A (selectedSum t) - eta - newCap t = 0 := by rw [newCap]; ring
theorem winner9_identity (t : Point) : A (t 0 + t 3) - comparisonCap t = 0 := by
  rw [comparisonCap]; ring

private theorem chosen_planes_incompatible {t : Point} (he : t 0 + t 3 < mu) (s : ℝ) :
    ¬(A s ≤ comparisonCap t ∧ C s ≤ comparisonCap t) := by
  dsimp [A, C, comparisonCap, mu] at *
  rintro ⟨ha, hc⟩
  linarith

private theorem exists_separator {i j : Fin 13} (hij : i ≠ j) :
    ∃ m ∈ Finset.Icc 1 63, m ≠ 9 ∧
      ((m ∈ leftMasks i ∧ m ∉ leftMasks j) ∨
        (m ∈ leftMasks j ∧ m ∉ leftMasks i)) := by
  have hne : leftMasks i ≠ leftMasks j := fun h => hij (leftMasks_injective h)
  by_cases hsub : leftMasks i ⊆ leftMasks j
  · obtain ⟨m, hm, hnotm⟩ := Finset.not_subset.mp
      (show ¬leftMasks j ⊆ leftMasks i from fun h => hne (Finset.Subset.antisymm hsub h))
    refine ⟨m, leftMasks_subset j hm, ?_, Or.inr ⟨hm, hnotm⟩⟩
    intro hm9
    exact hnotm (by simpa only [hm9] using nine_left i)
  · obtain ⟨m, hm, hnotm⟩ := Finset.not_subset.mp hsub
    refine ⟨m, leftMasks_subset i hm, ?_, Or.inl ⟨hm, hnotm⟩⟩
    intro hm9
    exact hnotm (by simpa only [hm9] using nine_left j)

theorem strict_cells_disjoint {i j : Fin 13} (hij : i ≠ j) : Disjoint (cell i) (cell j) := by
  apply Set.disjoint_left.mpr
  intro t hi hj
  obtain ⟨m, hm, hm9, hsep⟩ := exists_separator hij
  have hpi := hi.branches m hm hm9
  have hpj := hj.branches m hm hm9
  rcases hsep with ⟨hmi, hmj⟩ | ⟨hmj, hmi⟩
  · rw [branchPlane, if_pos hmi] at hpi
    rw [branchPlane, if_neg hmj] at hpj
    exact chosen_planes_incompatible hi.oldWinner (subsetSum m t) ⟨hpi.le, hpj.le⟩
  · rw [branchPlane, if_neg hmi] at hpi
    rw [branchPlane, if_pos hmj] at hpj
    exact chosen_planes_incompatible hi.oldWinner (subsetSum m t) ⟨hpj.le, hpi.le⟩

theorem owner_unique {i j : Fin 13} {t : Point} (hi : StrictRows i t) (hj : StrictRows j t) : i = j := by
  by_contra hij
  exact Set.disjoint_left.mp (strict_cells_disjoint hij) hi hj

theorem rows_antitone {i : Fin 13} {t : Point} (h : StrictRows i t) : Antitone t := by
  have h0 := h.order 0
  have h1 := h.order 1
  have h2 := h.order 2
  have h3 := h.order 3
  have h4 := h.order 4
  have h5 := h.order 5
  have h6 := h.order 6
  norm_num at h0 h1 h2 h3 h4 h5 h6
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij ⊢ <;> linarith

theorem rows_physical {i : Fin 13} {t : Point} (h : StrictRows i t) : PhysicalRows t where
  ordered := rows_antitone h
  eighthCutoff := h.lastFloor.le
  thirdCutoff := h.thirdFloor.le
  largestBelowMu := h.largest.le
  ascendingThird := h.ascendingThird.le
  ascendingOldWinner := h.oldWinner.le
  ascendingNew := h.ascendingNew.le
  firstHistory := h.firstHistory.le
  thirdHistory := h.thirdHistory.le
  fifthHistory := h.fifthHistory.le
  seventhHistory := h.seventhHistory.le
  comparisonAboveThird := h.aboveThird.le
  improvement := h.improvement.le
  newResidualUpper := by linarith [h.terminal]

theorem plane_tie_outside_all (m : ℕ) (t : Point)
    (hm : m ∈ Finset.Icc 1 63) (hm9 : m ≠ 9) (he : t 0 + t 3 < mu)
    (heq : A (subsetSum m t) = comparisonCap t ∨ C (subsetSum m t) = comparisonCap t) :
    ∀ i : Fin 13, ¬StrictRows i t := by
  intro i h
  have hb := h.branches m hm hm9
  by_cases hmi : m ∈ leftMasks i
  · rw [branchPlane, if_pos hmi] at hb
    rcases heq with heq | heq
    · exact (ne_of_lt hb) heq
    · exact chosen_planes_incompatible he (subsetSum m t) ⟨hb.le, heq.le⟩
  · rw [branchPlane, if_neg hmi] at hb
    rcases heq with heq | heq
    · exact chosen_planes_incompatible he (subsetSum m t) ⟨heq.le, hb.le⟩
    · exact (ne_of_lt hb) heq

def ownedRaisedExponent (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) : ℝ :=
  if ∃ i : Fin 13, StrictRows i (primeHistoryLogCoordinates N 8 pre) then
    P4ASlot19ChargedFrontierSourceOnly.raisedExponent N lambda6 pre
  else P4ASlot19ChargedFrontierSourceOnly.inheritedSixth lambda6 pre

theorem ownedRaisedExponent_eq_selected_cap
    (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ) (i : Fin 13)
    (h : StrictRows i (primeHistoryLogCoordinates N 8 pre))
    (hCap : P4ASlot19ChargedFrontierSourceOnly.inheritedSixth lambda6 pre ≤
      comparisonCap (primeHistoryLogCoordinates N 8 pre)) :
    ownedRaisedExponent N lambda6 pre = newCap (primeHistoryLogCoordinates N 8 pre) := by
  rw [ownedRaisedExponent, if_pos ⟨i, h⟩]
  unfold P4ASlot19ChargedFrontierSourceOnly.raisedExponent
  dsimp only
  exact if_pos (show P4ASlot19ChargedFrontierSourceOnly.actionGuard _ _ from ⟨rows_physical h, hCap⟩)

theorem ownedRaisedExponent_inherits_outside
    (N : ℝ) (lambda6 : List ℕ → ℝ) (pre : List ℕ)
    (hout : ∀ i : Fin 13, ¬StrictRows i (primeHistoryLogCoordinates N 8 pre)) :
    ownedRaisedExponent N lambda6 pre =
      P4ASlot19ChargedFrontierSourceOnly.inheritedSixth lambda6 pre :=
  if_neg (by rintro ⟨i, hi⟩; exact hout i hi)

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
end ImbalancedChen.OriginalAscendingThirteenCellOwnership
