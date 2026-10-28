import ImbalancedChen.P4AOriginalCell0ActualSixthParentGuard
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal next ascending cell1, in the immutable navigation's row order.
Compared with cell0 exactly row90 (old mask58) changes from A to C.
This source proves its own full CellGuard; cell0's guard is not reused.
-/
namespace ImbalancedChen.P4AOriginalAscendingCell1Affine
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P2OriginalAscendingEighthCapDictionary
open P4AOriginalAscending14Literal42 P4AOriginalAscendingCell0AfterSeed7
abbrev Point8 := Fin 8 → ℝ

/-- Raw source cell1 row90; all other 95 rows are byte-level identical
rational vectors in the pinned cell0/cell1 navigation. -/
def rows1 (k : Fin 96) : String × (Fin 9 → ℚ) :=
  if k = 90 then
    ("old subset 58 chosen plane 1 below R6", ![0,0,0,-3/2,3/2,3/2,3/2,0,0])
  else P4AOriginalAscendingCell0Literal96.rows k

abbrev sourceRow := rows1
abbrev evalRow := P4AOriginalSeed7Unequal15Literal.evalAffine

def literalRows (t : Point8) : Prop := ∀ k : Fin 96, 0 < evalRow (rows1 k).2 t

/-- These four common rows still separate cell1 from the adopted seed7. -/
theorem literalRows_core (t : Point8) (h : literalRows t) : Cell0Affine t := by
  have h14 := h (14 : Fin 96)
  have h16 := h (16 : Fin 96)
  have h17 := h (17 : Fin 96)
  have h58 := h (58 : Fin 96)
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    norm_num [rows1, P4AOriginalAscendingCell0Literal96.rows,
      cell0Row14, cell0Row16, cell0Row17, cell0Row58] at *
    assumption

private def planeIndex (I : Finset (Fin 6)) : Fin 96 :=
  ⟨if sixMask I < 6 then 33 + sixMask I else 32 + sixMask I, by
    have hmask : sixMask I ≤ 63 := by fin_cases I <;> decide
    split_ifs <;> omega⟩

/-- The exact rational coefficients of R minus the selected old plane. -/
private def planeGapRow (I : Finset (Fin 6)) : Fin 9 → ℚ :=
  fun j => if j = 0 then
      if literalPattern 1 I then 0 else 25 / 64
    else
      (if j.val = 2 ∨ j.val = 3 then (-3 / 2 : ℚ) else 0) -
      (if ∃ i ∈ I, i.val + 1 = j.val then
        if literalPattern 1 I then (-3 / 2 : ℚ) else 1 / 2
       else 0)

/-- This finite equality checks the original row order, including the
omitted mask-6 identity. It does not check a sampled point. -/
private theorem plane_row_exact :
    ∀ I : Finset (Fin 6), I ≠ ∅ → I ≠ winner6 →
      (sourceRow (planeIndex I)).2 = planeGapRow I := by
  decide

private theorem plane_gap_eval (I : Finset (Fin 6)) (t : Point8) :
    evalRow (planeGapRow I) t =
      R t - chosenOldPlane (literalPattern 1) t I := by
  fin_cases I <;>
    norm_num [planeGapRow, literalPattern, literalLeftMasks, sixMask,
      evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      chosenOldPlane, subsetSum, R, d, A, C, Fin.sum_univ_succ] <;> ring

/-- The 62 recorded planes and the one omitted equality provide every
one of the 63 nonempty old-subset tests. -/
theorem literalRows_old_planes (t : Point8) (h : literalRows t) :
    OldPlaneRows (literalPattern 1) t := by
  intro I hI
  have hne : I ≠ ∅ := by simpa [oldMasks] using hI
  by_cases hw : I = winner6
  · subst I
    norm_num [chosenOldPlane, literalPattern, literalLeftMasks, sixMask,
      winner6, subsetSum, R, d, A, C]
  · have hr := h (planeIndex I)
    rw [plane_row_exact I hne hw, plane_gap_eval] at hr
    linarith

private theorem literalRows_order (t : Point8) (h : literalRows t) : StrictAnti t := by
  have h01 := h (3 : Fin 96)
  have h12 := h (4 : Fin 96)
  have h23 := h (5 : Fin 96)
  have h34 := h (6 : Fin 96)
  have h45 := h (7 : Fin 96)
  have h56 := h (8 : Fin 96)
  have h67 := h (9 : Fin 96)
  norm_num [sourceRow, rows1, P4AOriginalAscendingCell0Literal96.rows,
    evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
    Fin.sum_univ_succ] at h01 h12 h23 h34 h45 h56 h67
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij ⊢ <;> linarith

private theorem literalRows_ascending (t : Point8) (h : literalRows t) :
    A (selectedSum t) < C (selectedSum t) := by
  have hr := h (17 : Fin 96)
  norm_num [sourceRow, rows1, P4AOriginalAscendingCell0Literal96.rows,
    evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
    Fin.sum_univ_succ] at hr
  dsimp [A, C, selectedSum]
  linarith

private def fullIndex : Fin 8 → Fin 96 := ![18,19,21,23,25,27,29,31]

private theorem full_square_row (t : Point8) (j : Fin 8)
    (ha : A (selectedSum t) < C (selectedSum t)) :
    evalRow (sourceRow (fullIndex j)).2 t = M t - fullSquare t j := by
  rw [M, min_eq_left ha.le]
  fin_cases j <;>
    norm_num [fullIndex, sourceRow, rows1, P4AOriginalAscendingCell0Literal96.rows,
      evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      fullSquare, prefixSum, Finset.sum_filter, Fin.sum_univ_succ,
      selectedSum, A, eta] <;> ring

private theorem selected_square_row (t : Point8) (j : Fin 8)
    (hj0 : 0 < j) (hj7 : j < 7)
    (ha : A (selectedSum t) < C (selectedSum t)) :
    evalRow (sourceRow ⟨18 + 2 * j.val, by omega⟩).2 t =
      M t - selectedRemainingSquare t j := by
  rw [M, min_eq_left ha.le]
  fin_cases j <;> norm_num at hj0 hj7 ⊢ <;>
    norm_num [sourceRow, rows1, P4AOriginalAscendingCell0Literal96.rows,
      evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ,
      selectedSum, A, eta] <;> ring

/-- Complete finite row-to-semantics bridge for original cell 1.
The inherited cap is deliberately absent: it is determined by its own
actual causal tree, rather than by the navigation's comparison R. -/
theorem literalRows_cellGuard (t : Point8) (h : literalRows t) :
    CellGuard (literalPattern 1) t := by
  have h0 := h (0 : Fin 96)
  have h1 := h (1 : Fin 96)
  have h2 := h (2 : Fin 96)
  have h10 := h (10 : Fin 96)
  have h11 := h (11 : Fin 96)
  have h12 := h (12 : Fin 96)
  have h13 := h (13 : Fin 96)
  have h15 := h (15 : Fin 96)
  have h32 := h (32 : Fin 96)
  have h33 := h (33 : Fin 96)
  norm_num [sourceRow, rows1, P4AOriginalAscendingCell0Literal96.rows,
    evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
    Fin.sum_univ_succ] at h0 h1 h2 h10 h11 h12 h13 h15 h32 h33
  have ha := literalRows_ascending t h
  have hc := literalRows_core t h
  have hsemantic := cell0_affine_semantic t hc
  refine {
    order := literalRows_order t h
    last_pos := by linarith
    largest := by dsimp [mu]; linarith
    third_activation := by linarith
    compact_cutoff := by linarith
    first_history := ?_
    history3 := ?_
    history5 := ?_
    history7 := ?_
    old_descending := hsemantic.1
    old_W := ?_
    old_planes := literalRows_old_planes t h
    new_ascending := ha
    improvement := hsemantic.2
    full_squares := ?_
    selected_squares := ?_
    old_residual := ?_
    new_residual := ?_ }
  · dsimp [R, d, C]; linarith
  · norm_num [oddCube, prefixSum, Finset.sum_filter,
      Fin.sum_univ_succ, R, d, C]; linarith
  · norm_num [oddCube, prefixSum, Finset.sum_filter,
      Fin.sum_univ_succ, R, d, C]; linarith
  · norm_num [oddCube, prefixSum, Finset.sum_filter,
      Fin.sum_univ_succ, R, d, C]; linarith
  · dsimp [B, cap, R, d, C]; linarith
  · intro j
    have hr := h (fullIndex j)
    rw [full_square_row t j ha] at hr
    linarith
  · intro j hj0 hj7
    have hr := h (⟨18 + 2 * j.val, by omega⟩ : Fin 96)
    rw [selected_square_row t j hj0 hj7 ha] at hr
    linarith
  · norm_num [S, Fin.sum_univ_succ, R, d, C]; linarith
  · rw [M, min_eq_left ha.le]
    norm_num [S, Fin.sum_univ_succ, A, selectedSum, eta]
    linarith


end
end ImbalancedChen.P4AOriginalAscendingCell1Affine
