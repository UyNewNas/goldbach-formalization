import ImbalancedChen.P4AOriginalCell2CommonRefinedParent
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The exact remaining original ascending source IDs are 3,4,5,6,8,...,14.
Each is a fixed navigation cell, not an arbitrary CellGuard input. All rows
use the original 96-row order. The eight actual A-to-C patch vectors and
the eleven exact per-cell patch sets below transcribe immutable navigation.
-/
namespace ImbalancedChen.P4AOriginalRemainingAscendingAtlas
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P2OriginalAscendingEighthCapDictionary
open P4AOriginalAscending14Literal42
abbrev RemainingCell := Fin 11
abbrev Point8 := Fin 8 → ℝ
abbrev evalRow := P4AOriginalSeed7Unequal15Literal.evalAffine
abbrev baseRows := P4AOriginalAscendingCell0Literal96.rows

def sourceId : RemainingCell → Fin 15 := ![3,4,5,6,8,9,10,11,12,13,14]

def changedRows : RemainingCell → Finset (Fin 96) :=
  ![
    {58,90},
    {58,90,92},
    {58,60,90,92},
    {58,74,90},
    {58,74,82,90},
    {58,74,82,90,92},
    {58,60,74,90,92},
    {58,60,74,82,90,92},
    {58,60,74,76,90,92},
    {58,60,74,76,82,90,92},
    {58,60,74,76,82,84,90,92}
  ]

def rightPatch (k : Fin 96) : String × (Fin 9 → ℚ) :=
  match k.val with
  | 58 => ("old subset 26 chosen plane 1 below R6", ![0,0,0,-3/2,3/2,3/2,0,0,0])
  | 60 => ("old subset 28 chosen plane 1 below R6", ![0,0,-3/2,0,3/2,3/2,0,0,0])
  | 74 => ("old subset 42 chosen plane 1 below R6", ![0,0,0,-3/2,3/2,0,3/2,0,0])
  | 76 => ("old subset 44 chosen plane 1 below R6", ![0,0,-3/2,0,3/2,0,3/2,0,0])
  | 82 => ("old subset 50 chosen plane 1 below R6", ![0,0,0,-3/2,0,3/2,3/2,0,0])
  | 84 => ("old subset 52 chosen plane 1 below R6", ![0,0,-3/2,0,0,3/2,3/2,0,0])
  | 90 => ("old subset 58 chosen plane 1 below R6", ![0,0,0,-3/2,3/2,3/2,3/2,0,0])
  | 92 => ("old subset 60 chosen plane 1 below R6", ![0,0,-3/2,0,3/2,3/2,3/2,0,0])
  | _ => baseRows k

def rows (c : RemainingCell) (k : Fin 96) :=
  if k ∈ changedRows c then rightPatch k else baseRows k

def sourceRows (c : RemainingCell) (t : Point8) : Prop :=
  ∀ k : Fin 96, 0 < evalRow (rows c k).2 t

def seedSeparator : RemainingCell → Fin 96 := ![74,74,60,92,82,82,60,60,60,60,60]


theorem sourceId_injective : Function.Injective sourceId := by decide

theorem sourceId_selected (c : RemainingCell) : sourceId c ∈ selectedCellIndices := by
  fin_cases c <;> decide

private def commonRows (t : Point8) : Prop :=
  ∀ k : Fin 34, 0 < evalRow (baseRows ⟨k.val, by omega⟩).2 t

private theorem common_row_exact : ∀ (c : RemainingCell) (k : Fin 34),
    rows c ⟨k.val, by omega⟩ = baseRows ⟨k.val, by omega⟩ := by decide

private theorem sourceRows_common (c : RemainingCell) (t : Point8)
    (h : sourceRows c t) : commonRows t := by
  intro k
  simpa only [common_row_exact] using h ⟨k.val, by omega⟩

private theorem singleton_row_exact (c : RemainingCell) : rows c 34 = baseRows 34 := by
  fin_cases c <;> decide

private def planeIndex (I : Finset (Fin 6)) : Fin 96 :=
  ⟨if sixMask I < 6 then 33 + sixMask I else 32 + sixMask I, by
    have hmask : sixMask I ≤ 63 := by fin_cases I <;> decide
    split_ifs <;> omega⟩

private def planeGapRow (c : RemainingCell) (I : Finset (Fin 6)) : Fin 9 → ℚ :=
  fun j => if j = 0 then
      if literalPattern (sourceId c) I then 0 else 25 / 64
    else
      (if j.val = 2 ∨ j.val = 3 then (-3 / 2 : ℚ) else 0) -
      (if ∃ i ∈ I, i.val + 1 = j.val then
        if literalPattern (sourceId c) I then (-3 / 2 : ℚ) else 1 / 2 else 0)

/-- A finite source equality for all eleven literal row systems. The
closed decision body is a source proposal; it has not been evaluated. -/
private theorem plane_row_exact : ∀ (c : RemainingCell) (I : Finset (Fin 6)),
    I ≠ ∅ → I ≠ winner6 → (rows c (planeIndex I)).2 = planeGapRow c I := by decide

private theorem plane_gap_eval (c : RemainingCell) (I : Finset (Fin 6)) (t : Point8) :
    evalRow (planeGapRow c I) t =
      R t - chosenOldPlane (literalPattern (sourceId c)) t I := by
  fin_cases c <;> fin_cases I <;>
    norm_num [planeGapRow, sourceId, literalPattern, literalLeftMasks, sixMask,
      evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      chosenOldPlane, subsetSum, R, d, A, C, Fin.sum_univ_succ] <;> ring

theorem sourceRows_old_planes (c : RemainingCell) (t : Point8) (h : sourceRows c t) :
    OldPlaneRows (literalPattern (sourceId c)) t := by
  intro I hI
  have hne : I ≠ ∅ := by simpa [oldMasks] using hI
  by_cases hw : I = winner6
  · subst I
    fin_cases c <;> norm_num [chosenOldPlane, sourceId, literalPattern,
      literalLeftMasks, sixMask, winner6, subsetSum, R, d, A, C]
  · have hr := h (planeIndex I)
    rw [plane_row_exact c I hne hw, plane_gap_eval] at hr
    linarith

private theorem common_order (t : Point8) (h : commonRows t) : StrictAnti t := by
  have h01 := h 3
  have h12 := h 4
  have h23 := h 5
  have h34 := h 6
  have h45 := h 7
  have h56 := h 8
  have h67 := h 9
  norm_num [baseRows, P4AOriginalAscendingCell0Literal96.rows,
    evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
    Fin.sum_univ_succ] at h01 h12 h23 h34 h45 h56 h67
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij ⊢ <;> linarith

private theorem common_ascending (t : Point8) (h : commonRows t) :
    A (selectedSum t) < C (selectedSum t) := by
  have hr := h 17
  norm_num [baseRows, P4AOriginalAscendingCell0Literal96.rows,
    evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine, Fin.sum_univ_succ] at hr
  dsimp [A, C, selectedSum]
  linarith

private theorem common_descending_gain (t : Point8) (h : commonRows t) :
    C (d t) < A (d t) ∧ R t < M t := by
  have hw := h 14
  have hg := h 16
  have ha := common_ascending t h
  norm_num [baseRows, P4AOriginalAscendingCell0Literal96.rows,
    evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine, Fin.sum_univ_succ] at hw hg
  rw [M, min_eq_left ha.le]
  dsimp [A, C, R, d, selectedSum, eta]
  constructor <;> linarith

private def fullIndex : Fin 8 → Fin 34 := ![18,19,21,23,25,27,29,31]

private theorem full_square_row (t : Point8) (j : Fin 8)
    (ha : A (selectedSum t) < C (selectedSum t)) :
    evalRow (baseRows ⟨(fullIndex j).val, by omega⟩).2 t = M t - fullSquare t j := by
  rw [M, min_eq_left ha.le]
  fin_cases j <;>
    norm_num [fullIndex, baseRows, P4AOriginalAscendingCell0Literal96.rows,
      evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      fullSquare, prefixSum, Finset.sum_filter, Fin.sum_univ_succ,
      selectedSum, A, eta] <;> ring

private theorem selected_square_row (t : Point8) (j : Fin 8) (hj0 : 0 < j) (hj7 : j < 7)
    (ha : A (selectedSum t) < C (selectedSum t)) :
    evalRow (baseRows ⟨18 + 2 * j.val, by omega⟩).2 t = M t - selectedRemainingSquare t j := by
  rw [M, min_eq_left ha.le]
  fin_cases j <;> norm_num at hj0 hj7 ⊢ <;>
    norm_num [baseRows, P4AOriginalAscendingCell0Literal96.rows,
      evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ,
      selectedSum, A, eta] <;> ring

/-- The complete guard is derived from each of the eleven actual raw
navigation row systems, with its own exact sourceId and changedRows. -/
theorem sourceRows_cellGuard (c : RemainingCell) (t : Point8) (h : sourceRows c t) :
    CellGuard (literalPattern (sourceId c)) t := by
  have hc := sourceRows_common c t h
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h10 := hc 10
  have h11 := hc 11
  have h12 := hc 12
  have h13 := hc 13
  have h15 := hc 15
  have h32 := hc 32
  have h33 := hc 33
  norm_num [baseRows, P4AOriginalAscendingCell0Literal96.rows,
    evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
    Fin.sum_univ_succ] at h0 h1 h2 h10 h11 h12 h13 h15 h32 h33
  have ha := common_ascending t hc
  have hgain := common_descending_gain t hc
  refine {
    order := common_order t hc
    last_pos := by linarith
    largest := by dsimp [mu]; linarith
    third_activation := by linarith
    compact_cutoff := by linarith
    first_history := ?_
    history3 := ?_
    history5 := ?_
    history7 := ?_
    old_descending := hgain.1
    old_W := ?_
    old_planes := sourceRows_old_planes c t h
    new_ascending := ha
    improvement := hgain.2
    full_squares := ?_
    selected_squares := ?_
    old_residual := ?_
    new_residual := ?_ }
  · dsimp [R, d, C]; linarith
  · norm_num [oddCube, prefixSum, Finset.sum_filter, Fin.sum_univ_succ, R, d, C]; linarith
  · norm_num [oddCube, prefixSum, Finset.sum_filter, Fin.sum_univ_succ, R, d, C]; linarith
  · norm_num [oddCube, prefixSum, Finset.sum_filter, Fin.sum_univ_succ, R, d, C]; linarith
  · dsimp [B, cap, R, d, C]; linarith
  · intro j
    have hr := hc (fullIndex j)
    rw [full_square_row t j ha] at hr
    linarith
  · intro j hj0 hj7
    have hr := hc (⟨18 + 2 * j.val, by omega⟩ : Fin 34)
    rw [selected_square_row t j hj0 hj7 ha] at hr
    linarith
  · norm_num [S, Fin.sum_univ_succ, R, d, C]; linarith
  · rw [M, min_eq_left ha.le]
    norm_num [S, Fin.sum_univ_succ, A, selectedSum, eta]
    linarith

/-- Literal source separator from already adopted equal-parent cell7.
The separator can be mask42, mask28, mask60 or mask50; mask26 alone would
incorrectly cover only the first few cells. -/
theorem sourceRows_not_seed7 (c : RemainingCell) (t : Point8) (h : sourceRows c t)
    (hseed : P4AOriginalSeed7Unequal15Literal.seed7SourceRows t) : False := by
  have hl := h (seedSeparator c)
  have hr := hseed (seedSeparator c)
  have hd := (sourceRows_cellGuard c t h).old_descending
  fin_cases c <;>
    norm_num [seedSeparator, rows, changedRows, rightPatch, baseRows,
      P4AOriginalAscendingCell0Literal96.rows, P4AOriginalSeed7Unequal15Literal.seed7Rows,
      evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      Fin.sum_univ_succ] at hl hr <;>
    dsimp [A, C, d] at hd <;> linarith

end
end ImbalancedChen.P4AOriginalRemainingAscendingAtlas
