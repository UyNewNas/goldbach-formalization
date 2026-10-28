import ImbalancedChen.P4AOriginalAscendingCell0Literal96
import ImbalancedChen.P4AOriginalH3AffineSelectedAction
import ImbalancedChen.HistoricalThirdCoarsePolicy
import Mathlib.Tactic

/-!
Source-only continuation: decode the complete literal cell-0 affine system.
No compiler, certificate checker or numerical replay has been run.

The static navigation provides an open real cell. We prove its complete
semantic guard, rather than assuming that guard separately. Actual discrete
carrier admission and the actual inherited parent guard remain separate.
In particular the original `firstStop` is a retained predicate, never a
numerical term in a finite maximum.
-/
namespace ImbalancedChen.P4AOriginalCell0AffineChronology
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P2OriginalAscendingEighthCapDictionary
open P4AOriginalAscending14Literal42
open P4AOriginalAscendingCell0AfterSeed7

abbrev Point8 := Fin 8 → ℝ
abbrev literalRows := P4AOriginalAscendingCell0Literal96.sourceRows
abbrev sourceRow := P4AOriginalAscendingCell0Literal96.rows
abbrev evalRow := P4AOriginalSeed7Unequal15Literal.evalAffine

private def planeIndex (I : Finset (Fin 6)) : Fin 96 :=
  ⟨if sixMask I < 6 then 33 + sixMask I else 32 + sixMask I, by
    have hmask : sixMask I ≤ 63 := by fin_cases I <;> decide
    split_ifs <;> omega⟩

/-- The exact rational coefficients of R minus the selected old plane. -/
private def planeGapRow (I : Finset (Fin 6)) : Fin 9 → ℚ :=
  fun j => if j = 0 then
      if literalPattern 0 I then 0 else 25 / 64
    else
      (if j.val = 2 ∨ j.val = 3 then (-3 / 2 : ℚ) else 0) -
      (if ∃ i ∈ I, i.val + 1 = j.val then
        if literalPattern 0 I then (-3 / 2 : ℚ) else 1 / 2
       else 0)

/-- This finite equality checks the original row order, including the
omitted mask-6 identity. It does not check a sampled point. -/
private theorem plane_row_exact :
    ∀ I : Finset (Fin 6), I ≠ ∅ → I ≠ winner6 →
      (sourceRow (planeIndex I)).2 = planeGapRow I := by
  decide

private theorem plane_gap_eval (I : Finset (Fin 6)) (t : Point8) :
    evalRow (planeGapRow I) t =
      R t - chosenOldPlane (literalPattern 0) t I := by
  fin_cases I <;>
    norm_num [planeGapRow, literalPattern, literalLeftMasks, sixMask,
      evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      chosenOldPlane, subsetSum, R, d, A, C, Fin.sum_univ_succ] <;> ring

/-- The 62 recorded planes and the one omitted equality provide every
one of the 63 nonempty old-subset tests. -/
theorem literalRows_old_planes (t : Point8) (h : literalRows t) :
    OldPlaneRows (literalPattern 0) t := by
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
  norm_num [sourceRow, P4AOriginalAscendingCell0Literal96.rows,
    evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
    Fin.sum_univ_succ] at h01 h12 h23 h34 h45 h56 h67
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij ⊢ <;> linarith

private theorem literalRows_ascending (t : Point8) (h : literalRows t) :
    A (selectedSum t) < C (selectedSum t) := by
  have hr := h (17 : Fin 96)
  norm_num [sourceRow, P4AOriginalAscendingCell0Literal96.rows,
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
    norm_num [fullIndex, sourceRow, P4AOriginalAscendingCell0Literal96.rows,
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
    norm_num [sourceRow, P4AOriginalAscendingCell0Literal96.rows,
      evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
      selectedRemainingSquare, Finset.sum_filter, Fin.sum_univ_succ,
      selectedSum, A, eta] <;> ring

/-- Complete finite row-to-semantics bridge for the original cell 0.
The inherited cap is deliberately absent: it is determined by its own
actual causal tree, rather than by the navigation's comparison R. -/
theorem literalRows_cellGuard (t : Point8) (h : literalRows t) :
    CellGuard (literalPattern 0) t := by
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
  norm_num [sourceRow, P4AOriginalAscendingCell0Literal96.rows,
    evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
    Fin.sum_univ_succ] at h0 h1 h2 h10 h11 h12 h13 h15 h32 h33
  have ha := literalRows_ascending t h
  have hc := P4AOriginalAscendingCell0Literal96.sourceRows_core t h
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

/-- The complete literal ascending cell has already passed H3 at D23;
it cannot simultaneously be one of the later H3-first-failure cells. -/
theorem literalRows_not_H3_first_failure (t : Point8) (h : literalRows t)
    (i : Fin 12)
    (hf : P4AOriginalFirstFailureH3Literal.sourceAffineGuard i t) : False := by
  have hc := literalRows_cellGuard t h
  have hh := (P4AOriginalH3AffineSelectedAction.affine_h3_priority_and_improvement
    i t hf).2.1
  have hp := hc.history3
  norm_num [oddCube, prefixSum, Finset.sum_filter, Fin.sum_univ_succ,
    R, d, C, P4AOriginalFirstFailureH3Literal.D23,
    P4AOriginalFirstFailureH3Literal.D,
    P4AOriginalFirstFailureH3Literal.H3] at hp hh
  linarith

open P4AOriginalActualSeed7Slot15
open P1OriginalVariableFifthContinuation P1OriginalVariableFourthContinuation
open ImbalancedChen.Certificates.P2OriginalSixthElevenLogSemantics

variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
  (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
  (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
  (J5 : Finset (Label5 m)) (rows5 : Finset (FifthRow m))

/-- The selected domain retains the genuine original coarse-label stop.
Neither this predicate nor its coarse endpoint is inserted into a max. -/
def retainedLiteralCell0 (pre : List ℕ) : Prop :=
  pre.length = 8 ∧
    HistoricalThirdCoarse.firstStop (e : ℝ) m N (rosserAncestor 1 pre) ∧
    literalRows (primeHistoryLogCoordinates N 8 pre) ∧
    CurrentParentGuard (primeHistoryLogCoordinates N 8 pre)
      (sixth e chi m omega N rows4 licensed4 J5 rows5
        (rosserAncestor 6 pre))

/-- All geometric premises of the preceding slot16 theorem are now
consequences of the recorded affine rows. Only actual parent retention
and the original first-stop domain must come from the existing tree. -/
theorem retainedLiteralCell0_selected (pre : List ℕ)
    (h : retainedLiteralCell0 e chi m omega N rows4 licensed4 J5 rows5 pre) :
    cell0Selected e chi m omega N rows4 licensed4 J5 rows5 pre := by
  rcases h with ⟨hlen, _hstop, hrows, hparent⟩
  exact ⟨hlen, literalRows_cellGuard _ hrows, hparent,
    P4AOriginalAscendingCell0Literal96.sourceRows_core _ hrows⟩

theorem retainedLiteralCell0_slot16 (pre : List ℕ)
    (h : retainedLiteralCell0 e chi m omega N rows4 licensed4 J5 rows5 pre) :
    P4AOriginalPrior58Chronology.slot16 N
      (sixth e chi m omega N rows4 licensed4 J5 rows5) pre =
        M (primeHistoryLogCoordinates N 8 pre) := by
  exact chronological_slot16_cell0 e chi m omega N rows4 licensed4 J5 rows5
    pre (retainedLiteralCell0_selected e chi m omega N rows4 licensed4 J5 rows5 pre h)

/-- Earlier tree surgery is invisible through rank eight, including the
rank-one first-stop decision and its half-open source ownership. -/
theorem original_stop_and_frozen_prefix (pre earlier : List ℕ) (positive : Bool)
    (h : retainedLiteralCell0 e chi m omega N rows4 licensed4 J5 rows5 pre)
    (hlen : earlier.length ≤ 8) :
    HistoricalThirdCoarse.firstStop (e : ℝ) m N (rosserAncestor 1 pre) ∧
      actual58Candidate e chi m omega N rows4 licensed4 J5 rows5 positive earlier =
        P4AOriginalActualElevenSixthCandidate.sixthSourcePolicy
          e chi m omega N rows4 licensed4 J5 rows5 positive earlier := by
  exact ⟨h.2.1, actual58_through_eight e chi m omega N rows4 licensed4 J5 rows5
    positive earlier hlen⟩

end
end ImbalancedChen.P4AOriginalCell0AffineChronology
