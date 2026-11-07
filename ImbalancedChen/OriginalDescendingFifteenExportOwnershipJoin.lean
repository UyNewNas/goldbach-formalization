import ImbalancedChen.OriginalDescendingFifteenLiteralAffineRows

/-!
SOURCE ONLY / UNCOMPILED. The exported 1440 rational strict rows are
identified with the previously constructed literal fifteen-cell ownership
predicate. Every original full square and selected129 complement square
occurs, with the same positive-slack comparison. The two tent-crossing
rows have their exact positive factor two, so equality still fails the
strict test. No payload-match or ownership conclusion is a premise.
-/

namespace ImbalancedChen.OriginalDescendingFifteenExportOwnershipJoin
noncomputable section
open scoped Classical BigOperators
open P2OriginalDescendingEighthLogSemantics VariableEnvelope
open OriginalDescendingFifteenCellOwnership
open OriginalDescendingFifteenLiteralAffineRows

private theorem evaluate_ite (p : Prop) [Decidable p] (a b : Expr) (t : Point) :
    evaluate (if p then a else b) t = if p then evaluate a t else evaluate b t := by
  by_cases hp : p <;> simp [hp]

private theorem evaluate_subsetExpr (m : ℕ) (t : Point) :
    evaluate (subsetExpr m) t = subsetSum m t := by
  simp [subsetExpr, evaluate, evaluate_ite, K, X, subsetSum, maskSlots,
    Finset.sum_filter, Fin.sum_univ_succ] <;> ring

def namedSlack (i : Fin 15) (r : Fin 96) (t : Point) : ℝ :=
  (![mu - t 0,
    t 2 - 1 / 100,
    t 7 - 53 / 13824,
    t 0 - t 1,
    t 1 - t 2,
    t 2 - t 3,
    t 3 - t 4,
    t 4 - t 5,
    t 5 - t 6,
    t 6 - t 7,
    oldRaw t - 3 * t 0,
    oldRaw t - history3 t,
    oldRaw t - history5 t,
    oldRaw t - history7 t,
    A (d t) - oldRaw t,
    oldRaw t - (VariableEnvelope.cap - 3 * t 2 / 8),
    newCap t - oldRaw t,
    A (selectedSum t) - eta - newCap t,
    newCap t - prefixSquareExpr t 0,
    newCap t - prefixSquareExpr t 1,
    newCap t - (selectedSum t + (∑ k ∈ Finset.univ.filter (fun k : Fin 8 => 0 < k ∧ k < 1), t k) + 2 * t 1),
    newCap t - prefixSquareExpr t 2,
    newCap t - (selectedSum t + (∑ k ∈ Finset.univ.filter (fun k : Fin 8 => 0 < k ∧ k < 2), t k) + 2 * t 2),
    newCap t - prefixSquareExpr t 3,
    newCap t - (selectedSum t + (∑ k ∈ Finset.univ.filter (fun k : Fin 8 => 0 < k ∧ k < 3), t k) + 2 * t 3),
    newCap t - prefixSquareExpr t 4,
    newCap t - (selectedSum t + (∑ k ∈ Finset.univ.filter (fun k : Fin 8 => 0 < k ∧ k < 4), t k) + 2 * t 4),
    newCap t - prefixSquareExpr t 5,
    newCap t - (selectedSum t + (∑ k ∈ Finset.univ.filter (fun k : Fin 8 => 0 < k ∧ k < 5), t k) + 2 * t 5),
    newCap t - prefixSquareExpr t 6,
    newCap t - (selectedSum t + (∑ k ∈ Finset.univ.filter (fun k : Fin 8 => 0 < k ∧ k < 6), t k) + 2 * t 6),
    newCap t - prefixSquareExpr t 7,
    oldRaw t - (total t + t 7),
    total t + 3 * t 7 - newCap t,
    oldRaw t - branchPlane i 1 t,
    oldRaw t - branchPlane i 2 t,
    oldRaw t - branchPlane i 3 t,
    oldRaw t - branchPlane i 4 t,
    oldRaw t - branchPlane i 5 t,
    oldRaw t - branchPlane i 7 t,
    oldRaw t - branchPlane i 8 t,
    oldRaw t - branchPlane i 9 t,
    oldRaw t - branchPlane i 10 t,
    oldRaw t - branchPlane i 11 t,
    oldRaw t - branchPlane i 12 t,
    oldRaw t - branchPlane i 13 t,
    oldRaw t - branchPlane i 14 t,
    oldRaw t - branchPlane i 15 t,
    oldRaw t - branchPlane i 16 t,
    oldRaw t - branchPlane i 17 t,
    oldRaw t - branchPlane i 18 t,
    oldRaw t - branchPlane i 19 t,
    oldRaw t - branchPlane i 20 t,
    oldRaw t - branchPlane i 21 t,
    oldRaw t - branchPlane i 22 t,
    oldRaw t - branchPlane i 23 t,
    oldRaw t - branchPlane i 24 t,
    oldRaw t - branchPlane i 25 t,
    oldRaw t - branchPlane i 26 t,
    oldRaw t - branchPlane i 27 t,
    oldRaw t - branchPlane i 28 t,
    oldRaw t - branchPlane i 29 t,
    oldRaw t - branchPlane i 30 t,
    oldRaw t - branchPlane i 31 t,
    oldRaw t - branchPlane i 32 t,
    oldRaw t - branchPlane i 33 t,
    oldRaw t - branchPlane i 34 t,
    oldRaw t - branchPlane i 35 t,
    oldRaw t - branchPlane i 36 t,
    oldRaw t - branchPlane i 37 t,
    oldRaw t - branchPlane i 38 t,
    oldRaw t - branchPlane i 39 t,
    oldRaw t - branchPlane i 40 t,
    oldRaw t - branchPlane i 41 t,
    oldRaw t - branchPlane i 42 t,
    oldRaw t - branchPlane i 43 t,
    oldRaw t - branchPlane i 44 t,
    oldRaw t - branchPlane i 45 t,
    oldRaw t - branchPlane i 46 t,
    oldRaw t - branchPlane i 47 t,
    oldRaw t - branchPlane i 48 t,
    oldRaw t - branchPlane i 49 t,
    oldRaw t - branchPlane i 50 t,
    oldRaw t - branchPlane i 51 t,
    oldRaw t - branchPlane i 52 t,
    oldRaw t - branchPlane i 53 t,
    oldRaw t - branchPlane i 54 t,
    oldRaw t - branchPlane i 55 t,
    oldRaw t - branchPlane i 56 t,
    oldRaw t - branchPlane i 57 t,
    oldRaw t - branchPlane i 58 t,
    oldRaw t - branchPlane i 59 t,
    oldRaw t - branchPlane i 60 t,
    oldRaw t - branchPlane i 61 t,
    oldRaw t - branchPlane i 62 t,
    oldRaw t - branchPlane i 63 t] : Fin 96 → ℝ) r

theorem semanticSlack_eq_namedSlack (i : Fin 15) (r : Fin 96) (t : Point) :
    semanticSlack i r t = namedSlack i r t := by
  fin_cases r
  all_goals
    simp [semanticSlack, semanticExpr, namedSlack, evaluate, evaluate_ite,
      evaluate_subsetExpr, oldExpr, newExpr, ascendingExpr, descendingExpr, K, X,
      oldRaw, newCap, total, history3, history5, history7, d, selectedSum,
      branchPlane, prefixSquareExpr, Finset.sum_filter, Fin.sum_univ_succ,
      VariableEnvelope.A, VariableEnvelope.C, eta, VariableEnvelope.cap, mu]
    <;> split_ifs <;> ring

def fullRow : Fin 8 → Fin 96 := ![18,19,21,23,25,27,29,31]
def middleIndex (k : Fin 6) : Fin 8 := ⟨k.val + 1, by omega⟩
def complementRow : Fin 6 → Fin 96 := ![20,22,24,26,28,30]
def branchRow (k : Fin 62) : Fin 96 := ⟨34 + k.val, by omega⟩

def branchMasks : Fin 62 → ℕ := ![1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]

private theorem middleIndex_covers : ∀ j : Fin 8, j ≠ 0 → j ≠ 7 →
    ∃ k : Fin 6, middleIndex k = j := by decide

private theorem branchMask_mem (k : Fin 62) :
    branchMasks k ∈ Finset.Icc 1 63 ∧ branchMasks k ≠ 6 := by
  fin_cases k <;> decide

private theorem branchMasks_cover : ∀ m : Fin 64, 0 < m.val → m.val ≠ 6 →
    ∃ k : Fin 62, branchMasks k = m.val := by decide

private theorem namedSlack_full (i : Fin 15) (j : Fin 8) (t : Point) :
    namedSlack i (fullRow j) t = newCap t - prefixSquareExpr t j := by
  fin_cases j <;> simp [fullRow, namedSlack]

private theorem namedSlack_complement (i : Fin 15) (k : Fin 6) (t : Point) :
    namedSlack i (complementRow k) t =
      newCap t - (selectedSum t +
        (∑ j ∈ Finset.univ.filter (fun j : Fin 8 => 0 < j ∧ j < middleIndex k), t j) +
          2 * t (middleIndex k)) := by
  fin_cases k <;> simp [complementRow, middleIndex, namedSlack]

private theorem namedSlack_branch (i : Fin 15) (k : Fin 62) (t : Point) :
    namedSlack i (branchRow k) t = oldRaw t - branchPlane i (branchMasks k) t := by
  fin_cases k <;> simp [branchRow, branchMasks, namedSlack]

private theorem strictRows_namedSlack_pos {i : Fin 15} {t : Point}
    (h : StrictRows i t) : ∀ r : Fin 96, 0 < namedSlack i r t := by
  intro r
  fin_cases r
  · simpa [namedSlack] using sub_pos.mpr (h.largest)
  · simpa [namedSlack] using sub_pos.mpr (h.thirdFloor)
  · simpa [namedSlack] using sub_pos.mpr (h.lastFloor)
  · simpa [namedSlack] using sub_pos.mpr (h.order (0 : Fin 7))
  · simpa [namedSlack] using sub_pos.mpr (h.order (1 : Fin 7))
  · simpa [namedSlack] using sub_pos.mpr (h.order (2 : Fin 7))
  · simpa [namedSlack] using sub_pos.mpr (h.order (3 : Fin 7))
  · simpa [namedSlack] using sub_pos.mpr (h.order (4 : Fin 7))
  · simpa [namedSlack] using sub_pos.mpr (h.order (5 : Fin 7))
  · simpa [namedSlack] using sub_pos.mpr (h.order (6 : Fin 7))
  · simpa [namedSlack] using sub_pos.mpr (h.firstHistory)
  · simpa [namedSlack] using sub_pos.mpr (h.thirdHistory)
  · simpa [namedSlack] using sub_pos.mpr (h.fifthHistory)
  · simpa [namedSlack] using sub_pos.mpr (h.seventhHistory)
  · have hw := h.oldWinner
    dsimp [d, mu] at hw
    dsimp [namedSlack, VariableEnvelope.A, oldRaw, VariableEnvelope.C, d]
    linarith
  · simpa [namedSlack] using sub_pos.mpr h.oldW
  · simpa [namedSlack] using sub_pos.mpr h.improvement
  · have hd := h.descending
    dsimp [mu, selectedSum] at hd
    dsimp [namedSlack, VariableEnvelope.A, newCap, VariableEnvelope.C, eta, selectedSum]
    linarith
  · simpa [namedSlack] using sub_pos.mpr (h.fullSquares 0)
  · simpa [namedSlack] using sub_pos.mpr (h.fullSquares 1)
  · simpa [namedSlack] using sub_pos.mpr (h.complementSquares 1 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.fullSquares 2)
  · simpa [namedSlack] using sub_pos.mpr (h.complementSquares 2 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.fullSquares 3)
  · simpa [namedSlack] using sub_pos.mpr (h.complementSquares 3 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.fullSquares 4)
  · simpa [namedSlack] using sub_pos.mpr (h.complementSquares 4 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.fullSquares 5)
  · simpa [namedSlack] using sub_pos.mpr (h.complementSquares 5 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.fullSquares 6)
  · simpa [namedSlack] using sub_pos.mpr (h.complementSquares 6 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.fullSquares 7)
  · simpa [namedSlack] using sub_pos.mpr h.oldResidual
  · simpa [namedSlack] using sub_pos.mpr h.terminal
  · simpa [namedSlack] using sub_pos.mpr (h.branches 1 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 2 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 3 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 4 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 5 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 7 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 8 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 9 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 10 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 11 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 12 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 13 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 14 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 15 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 16 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 17 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 18 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 19 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 20 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 21 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 22 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 23 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 24 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 25 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 26 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 27 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 28 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 29 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 30 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 31 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 32 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 33 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 34 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 35 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 36 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 37 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 38 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 39 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 40 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 41 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 42 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 43 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 44 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 45 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 46 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 47 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 48 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 49 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 50 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 51 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 52 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 53 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 54 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 55 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 56 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 57 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 58 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 59 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 60 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 61 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 62 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 63 (by decide) (by decide))

private theorem strictRows_of_namedSlack_pos {i : Fin 15} {t : Point}
    (h : ∀ r : Fin 96, 0 < namedSlack i r t) : StrictRows i t where
  largest := by simpa [namedSlack] using sub_pos.mp (h 0)
  thirdFloor := by simpa [namedSlack] using sub_pos.mp (h 1)
  lastFloor := by simpa [namedSlack] using sub_pos.mp (h 2)
  order := by
    intro j
    fin_cases j
    · simpa [namedSlack] using sub_pos.mp (h 3)
    · simpa [namedSlack] using sub_pos.mp (h 4)
    · simpa [namedSlack] using sub_pos.mp (h 5)
    · simpa [namedSlack] using sub_pos.mp (h 6)
    · simpa [namedSlack] using sub_pos.mp (h 7)
    · simpa [namedSlack] using sub_pos.mp (h 8)
    · simpa [namedSlack] using sub_pos.mp (h 9)
  firstHistory := by simpa [namedSlack] using sub_pos.mp (h 10)
  thirdHistory := by simpa [namedSlack] using sub_pos.mp (h 11)
  fifthHistory := by simpa [namedSlack] using sub_pos.mp (h 12)
  seventhHistory := by simpa [namedSlack] using sub_pos.mp (h 13)
  oldWinner := by
    have hw := h 14
    dsimp [namedSlack, VariableEnvelope.A, oldRaw, VariableEnvelope.C, d] at hw
    dsimp [mu, d]
    linarith
  oldW := by simpa [namedSlack] using sub_pos.mp (h 15)
  improvement := by simpa [namedSlack] using sub_pos.mp (h 16)
  descending := by
    have hd := h 17
    dsimp [namedSlack, VariableEnvelope.A, newCap, VariableEnvelope.C, eta, selectedSum] at hd
    dsimp [mu, selectedSum]
    linarith
  fullSquares := by
    intro j
    have hh := h (fullRow j)
    rw [namedSlack_full] at hh
    exact sub_pos.mp hh
  complementSquares := by
    intro j hj0 hj7
    obtain ⟨k, rfl⟩ := middleIndex_covers j hj0 hj7
    have hh := h (complementRow k)
    rw [namedSlack_complement] at hh
    exact sub_pos.mp hh
  oldResidual := by simpa [namedSlack] using sub_pos.mp (h 32)
  terminal := by simpa [namedSlack] using sub_pos.mp (h 33)
  branches := by
    intro m hm hm6
    have hlo := (Finset.mem_Icc.mp hm).1
    have hhi := (Finset.mem_Icc.mp hm).2
    obtain ⟨k, hk⟩ := branchMasks_cover ⟨m, by omega⟩ hlo hm6
    have hh := h (branchRow k)
    rw [namedSlack_branch, hk] at hh
    exact sub_pos.mp hh

/-- The original strict export and actual ownership structure agree on
every real point, including all affine walls and all boundary ties. -/
theorem strictExportedRows_iff_StrictRows (i : Fin 15) (t : Point) :
    StrictExportedRows i t ↔ StrictRows i t := by
  rw [strictExportedRows_iff_strictSemanticRows]
  constructor
  · intro h
    apply strictRows_of_namedSlack_pos
    intro r
    rw [← semanticSlack_eq_namedSlack]
    exact h r
  · intro h r
    rw [semanticSlack_eq_namedSlack]
    exact strictRows_namedSlack_pos h r

theorem exported_strict_cells_disjoint {i j : Fin 15} (hij : i ≠ j) :
    Disjoint {t : Point | StrictExportedRows i t} {t : Point | StrictExportedRows j t} := by
  apply Set.disjoint_left.mpr
  intro t hi hj
  exact Set.disjoint_left.mp (strict_cells_disjoint hij)
    ((strictExportedRows_iff_StrictRows i t).mp hi)
    ((strictExportedRows_iff_StrictRows j t).mp hj)

end
end ImbalancedChen.OriginalDescendingFifteenExportOwnershipJoin
