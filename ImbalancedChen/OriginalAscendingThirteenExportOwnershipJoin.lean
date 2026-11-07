import ImbalancedChen.OriginalAscendingThirteenLiteralAffineRows

/-!
SOURCE ONLY / UNCOMPILED. All1261exported strict rational rows are
identified with the original13ascending cell ownership predicate. The
original97named slacks preserve every full/selected138 complement square.
The zero ascending-license and winner9 identities are not strict rows.
The two actual tent-side rows have their positive factor two, preserving
arithmetic ties and inherited fallback. No payload-match, simplex floor,
actual third/sixth provenance or integral conclusion is assumed.
-/
namespace ImbalancedChen.OriginalAscendingThirteenExportOwnershipJoin
noncomputable section
open scoped Classical BigOperators
open P2OriginalThirdMinorantLogDictionarySourceOnly VariableEnvelope
open OriginalAscendingThirteenCellOwnership
open OriginalDescendingFifteenLiteralAffineRows
  (Expr evaluate subsetExpr K X ascendingExpr descendingExpr)
open OriginalAscendingThirteenLiteralAffineRows

private theorem evaluate_ite (p : Prop) [Decidable p] (a b : Expr) (t : Point) :
    evaluate (if p then a else b) t = if p then evaluate a t else evaluate b t := by
  by_cases hp : p <;> simp [hp]

private theorem evaluate_subsetExpr (m : ℕ) (t : Point) :
    evaluate (subsetExpr m) t = subsetSum m t := by
  simp [subsetExpr, evaluate, evaluate_ite, K, X, subsetSum, maskSlots,
    Finset.sum_filter, Fin.sum_univ_succ] <;> ring

def namedSlack (i : Fin 13) (r : Fin 97) (t : Point) : ℝ :=
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
    thirdMinorant t - 3 * t 0,
    thirdMinorant t - history3 t,
    thirdMinorant t - history5 t,
    thirdMinorant t - history7 t,
    comparisonCap t - thirdMinorant t,
    C (t 0 + t 3) - comparisonCap t,
    comparisonCap t - (VariableEnvelope.cap - 3 * t 2 / 8),
    mu - (t 1 + t 2),
    newCap t - comparisonCap t,
    C (selectedSum t) - eta - newCap t,
    newCap t - prefixSquareExpr t 0,
    newCap t - (selectedSum t + (∑ k ∈ Finset.univ.filter (fun k : Fin 8 => k < 0 ∧ k ≠ 1 ∧ k ≠ 3 ∧ k ≠ 7), t k) + 2 * t 0),
    newCap t - prefixSquareExpr t 1,
    newCap t - prefixSquareExpr t 2,
    newCap t - (selectedSum t + (∑ k ∈ Finset.univ.filter (fun k : Fin 8 => k < 2 ∧ k ≠ 1 ∧ k ≠ 3 ∧ k ≠ 7), t k) + 2 * t 2),
    newCap t - prefixSquareExpr t 3,
    newCap t - prefixSquareExpr t 4,
    newCap t - (selectedSum t + (∑ k ∈ Finset.univ.filter (fun k : Fin 8 => k < 4 ∧ k ≠ 1 ∧ k ≠ 3 ∧ k ≠ 7), t k) + 2 * t 4),
    newCap t - prefixSquareExpr t 5,
    newCap t - (selectedSum t + (∑ k ∈ Finset.univ.filter (fun k : Fin 8 => k < 5 ∧ k ≠ 1 ∧ k ≠ 3 ∧ k ≠ 7), t k) + 2 * t 5),
    newCap t - prefixSquareExpr t 6,
    newCap t - (selectedSum t + (∑ k ∈ Finset.univ.filter (fun k : Fin 8 => k < 6 ∧ k ≠ 1 ∧ k ≠ 3 ∧ k ≠ 7), t k) + 2 * t 6),
    newCap t - prefixSquareExpr t 7,
    comparisonCap t - (total t + t 7),
    total t + 3 * t 7 - newCap t,
    comparisonCap t - branchPlane i 1 t,
    comparisonCap t - branchPlane i 2 t,
    comparisonCap t - branchPlane i 3 t,
    comparisonCap t - branchPlane i 4 t,
    comparisonCap t - branchPlane i 5 t,
    comparisonCap t - branchPlane i 6 t,
    comparisonCap t - branchPlane i 7 t,
    comparisonCap t - branchPlane i 8 t,
    comparisonCap t - branchPlane i 10 t,
    comparisonCap t - branchPlane i 11 t,
    comparisonCap t - branchPlane i 12 t,
    comparisonCap t - branchPlane i 13 t,
    comparisonCap t - branchPlane i 14 t,
    comparisonCap t - branchPlane i 15 t,
    comparisonCap t - branchPlane i 16 t,
    comparisonCap t - branchPlane i 17 t,
    comparisonCap t - branchPlane i 18 t,
    comparisonCap t - branchPlane i 19 t,
    comparisonCap t - branchPlane i 20 t,
    comparisonCap t - branchPlane i 21 t,
    comparisonCap t - branchPlane i 22 t,
    comparisonCap t - branchPlane i 23 t,
    comparisonCap t - branchPlane i 24 t,
    comparisonCap t - branchPlane i 25 t,
    comparisonCap t - branchPlane i 26 t,
    comparisonCap t - branchPlane i 27 t,
    comparisonCap t - branchPlane i 28 t,
    comparisonCap t - branchPlane i 29 t,
    comparisonCap t - branchPlane i 30 t,
    comparisonCap t - branchPlane i 31 t,
    comparisonCap t - branchPlane i 32 t,
    comparisonCap t - branchPlane i 33 t,
    comparisonCap t - branchPlane i 34 t,
    comparisonCap t - branchPlane i 35 t,
    comparisonCap t - branchPlane i 36 t,
    comparisonCap t - branchPlane i 37 t,
    comparisonCap t - branchPlane i 38 t,
    comparisonCap t - branchPlane i 39 t,
    comparisonCap t - branchPlane i 40 t,
    comparisonCap t - branchPlane i 41 t,
    comparisonCap t - branchPlane i 42 t,
    comparisonCap t - branchPlane i 43 t,
    comparisonCap t - branchPlane i 44 t,
    comparisonCap t - branchPlane i 45 t,
    comparisonCap t - branchPlane i 46 t,
    comparisonCap t - branchPlane i 47 t,
    comparisonCap t - branchPlane i 48 t,
    comparisonCap t - branchPlane i 49 t,
    comparisonCap t - branchPlane i 50 t,
    comparisonCap t - branchPlane i 51 t,
    comparisonCap t - branchPlane i 52 t,
    comparisonCap t - branchPlane i 53 t,
    comparisonCap t - branchPlane i 54 t,
    comparisonCap t - branchPlane i 55 t,
    comparisonCap t - branchPlane i 56 t,
    comparisonCap t - branchPlane i 57 t,
    comparisonCap t - branchPlane i 58 t,
    comparisonCap t - branchPlane i 59 t,
    comparisonCap t - branchPlane i 60 t,
    comparisonCap t - branchPlane i 61 t,
    comparisonCap t - branchPlane i 62 t,
    comparisonCap t - branchPlane i 63 t] : Fin 97 → ℝ) r

theorem semanticSlack_eq_namedSlack (i : Fin 13) (r : Fin 97) (t : Point) :
    semanticSlack i r t = namedSlack i r t := by
  fin_cases r
  all_goals
    simp [semanticSlack, semanticExpr, namedSlack, evaluate, evaluate_ite,
      evaluate_subsetExpr, oldExpr, thirdExpr, newExpr, ascendingExpr, descendingExpr, K, X,
      comparisonCap, thirdMinorant, newCap, total, history3, history5, history7, selectedSum,
      branchPlane, prefixSquareExpr, Finset.sum_filter, Fin.sum_univ_succ,
      VariableEnvelope.A, VariableEnvelope.C, eta, VariableEnvelope.cap, mu]
    <;> split_ifs <;> ring

def fullRow : Fin 8 → Fin 97 := ![20,22,23,25,26,28,30,32]
def middleIndex : Fin 5 → Fin 8 := ![0,2,4,5,6]
def complementRow : Fin 5 → Fin 97 := ![21,24,27,29,31]
def branchRow (k : Fin 62) : Fin 97 := ⟨35 + k.val, by omega⟩

def branchMasks : Fin 62 → ℕ := ![1,2,3,4,5,6,7,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]

private theorem middleIndex_covers : ∀ j : Fin 8, j ≠ 1 → j ≠ 3 → j ≠ 7 →
    ∃ k : Fin 5, middleIndex k = j := by decide

private theorem branchMasks_cover : ∀ m : Fin 64, 0 < m.val → m.val ≠ 9 →
    ∃ k : Fin 62, branchMasks k = m.val := by decide

private theorem namedSlack_full (i : Fin 13) (j : Fin 8) (t : Point) :
    namedSlack i (fullRow j) t = newCap t - prefixSquareExpr t j := by
  fin_cases j <;> simp [fullRow, namedSlack]

private theorem namedSlack_complement (i : Fin 13) (k : Fin 5) (t : Point) :
    namedSlack i (complementRow k) t =
      newCap t - (selectedSum t + (∑ j ∈ Finset.univ.filter
        (fun j : Fin 8 => j < middleIndex k ∧ j ≠ 1 ∧ j ≠ 3 ∧ j ≠ 7), t j) +
          2 * t (middleIndex k)) := by
  fin_cases k <;> simp [complementRow, middleIndex, namedSlack]

private theorem namedSlack_branch (i : Fin 13) (k : Fin 62) (t : Point) :
    namedSlack i (branchRow k) t = comparisonCap t - branchPlane i (branchMasks k) t := by
  fin_cases k <;> simp [branchRow, branchMasks, namedSlack]

private theorem strictRows_namedSlack_pos {i : Fin 13} {t : Point}
    (h : StrictRows i t) : ∀ r : Fin 97, 0 < namedSlack i r t := by
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
  · simpa [namedSlack] using sub_pos.mpr (h.aboveThird)
  · have hw := h.oldWinner
    dsimp [mu] at hw
    dsimp [namedSlack, VariableEnvelope.A, VariableEnvelope.C, comparisonCap]
    linarith
  · simpa [namedSlack] using sub_pos.mpr h.oldW
  · simpa [namedSlack] using sub_pos.mpr h.ascendingThird
  · simpa [namedSlack] using sub_pos.mpr h.improvement
  · have hn := h.ascendingNew
    dsimp [mu] at hn
    dsimp [namedSlack, VariableEnvelope.A, VariableEnvelope.C, newCap, eta]
    linarith
  · simpa [namedSlack] using sub_pos.mpr (h.fullSquares 0)
  · simpa [namedSlack] using sub_pos.mpr (h.complementSquares 0 (by decide) (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.fullSquares 1)
  · simpa [namedSlack] using sub_pos.mpr (h.fullSquares 2)
  · simpa [namedSlack] using sub_pos.mpr (h.complementSquares 2 (by decide) (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.fullSquares 3)
  · simpa [namedSlack] using sub_pos.mpr (h.fullSquares 4)
  · simpa [namedSlack] using sub_pos.mpr (h.complementSquares 4 (by decide) (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.fullSquares 5)
  · simpa [namedSlack] using sub_pos.mpr (h.complementSquares 5 (by decide) (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.fullSquares 6)
  · simpa [namedSlack] using sub_pos.mpr (h.complementSquares 6 (by decide) (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.fullSquares 7)
  · simpa [namedSlack] using sub_pos.mpr h.oldResidual
  · simpa [namedSlack] using sub_pos.mpr h.terminal
  · simpa [namedSlack] using sub_pos.mpr (h.branches 1 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 2 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 3 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 4 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 5 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 6 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 7 (by decide) (by decide))
  · simpa [namedSlack] using sub_pos.mpr (h.branches 8 (by decide) (by decide))
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

private theorem strictRows_of_namedSlack_pos {i : Fin 13} {t : Point}
    (h : ∀ r : Fin 97, 0 < namedSlack i r t) : StrictRows i t where
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
  aboveThird := by simpa [namedSlack] using sub_pos.mp (h 14)
  oldWinner := by
    have hw := h 15
    dsimp [namedSlack, VariableEnvelope.A, VariableEnvelope.C, comparisonCap] at hw
    dsimp [mu]
    linarith
  oldW := by simpa [namedSlack] using sub_pos.mp (h 16)
  ascendingThird := by simpa [namedSlack] using sub_pos.mp (h 17)
  improvement := by simpa [namedSlack] using sub_pos.mp (h 18)
  ascendingNew := by
    have hn := h 19
    dsimp [namedSlack, newCap, VariableEnvelope.A, VariableEnvelope.C, eta] at hn
    dsimp [mu]
    linarith
  fullSquares := by
    intro j
    have hh := h (fullRow j)
    rw [namedSlack_full] at hh
    exact sub_pos.mp hh
  complementSquares := by
    intro j hj1 hj3 hj7
    obtain ⟨k, rfl⟩ := middleIndex_covers j hj1 hj3 hj7
    have hh := h (complementRow k)
    rw [namedSlack_complement] at hh
    exact sub_pos.mp hh
  oldResidual := by simpa [namedSlack] using sub_pos.mp (h 33)
  terminal := by simpa [namedSlack] using sub_pos.mp (h 34)
  branches := by
    intro m hm hm9
    have hlo := (Finset.mem_Icc.mp hm).1
    have hhi := (Finset.mem_Icc.mp hm).2
    obtain ⟨k, hk⟩ := branchMasks_cover ⟨m, by omega⟩ hlo hm9
    have hh := h (branchRow k)
    rw [namedSlack_branch, hk] at hh
    exact sub_pos.mp hh

theorem strictExportedRows_iff_StrictRows (i : Fin 13) (t : Point) :
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

theorem exported_strict_cells_disjoint {i j : Fin 13} (hij : i ≠ j) :
    Disjoint {t : Point | StrictExportedRows i t} {t : Point | StrictExportedRows j t} := by
  apply Set.disjoint_left.mpr
  intro t hi hj
  exact Set.disjoint_left.mp (strict_cells_disjoint hij)
    ((strictExportedRows_iff_StrictRows i t).mp hi)
    ((strictExportedRows_iff_StrictRows j t).mp hj)

theorem exportedRows_physical {i : Fin 13} {t : Point} (h : StrictExportedRows i t) :
    PhysicalRows t := rows_physical ((strictExportedRows_iff_StrictRows i t).mp h)

end
end ImbalancedChen.OriginalAscendingThirteenExportOwnershipJoin
