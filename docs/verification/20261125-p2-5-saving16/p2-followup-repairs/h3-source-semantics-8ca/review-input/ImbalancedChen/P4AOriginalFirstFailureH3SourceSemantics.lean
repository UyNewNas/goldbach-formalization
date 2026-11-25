import ImbalancedChen.OriginalDescendingFifteenLiteralAffineRows
import ImbalancedChen.P4AOriginalFirstFailureH3Literal
import ImbalancedChen.SelectedPrefixBoxCap
import ImbalancedChen.VariableEnvelope
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original twelve H3 first-failure cells have 99 literal strict affine
rows each. This file proves the missing row-to-semantic dictionary on the
ENTIRE original open cell, including all eight full squares and all five
mask138 complement squares. No small box, branch licence, selected-square
claim, or target cap bound is assumed. The finite symbolic row identities
below are UNEVALUATED; no Lean/compiler or numerical replay was run.

The final dictionary removes the redundant StrictH3 conjunct from the
EXISTING ActualH3Guard and leaves h3Exponent exactly unchanged. Its actual
sixth-parent comparisons remain explicit. This is not a construction of
the whole 87-domain policy, its missing actual sixth parent, or its rho.
-/

namespace ImbalancedChen.P4AOriginalFirstFailureH3SourceSemantics

noncomputable section
open scoped Classical BigOperators
open P4AOriginalFirstFailureH3Literal

/-- The physical square expressions in the independent source, with its
original zero-based chronological slots. -/
def fullExpr (t : Point) (j : Fin 8) : ℝ :=
  (∑ k : Fin 8, if k < j then t k else 0) + 2 * t j

def complementExpr (t : Point) (j : Fin 8) : ℝ :=
  selected138 t +
    (∑ k : Fin 8, if k < j ∧ k ≠ 1 ∧ k ≠ 3 ∧ k ≠ 7 then t k else 0) +
    2 * t j

/-- Exactly the first 37 strict slacks, in the archived row order.
The constant ascending-licence identity is absent from the archive and
is not incorrectly required to be strictly positive. -/
def commonSlack (t : Point) : Fin 37 → ℝ :=
  ![mu - t 0, t 2 - 1 / 100, t 7 - 53 / 13824,
    t 0 - t 1, t 1 - t 2, t 2 - t 3, t 3 - t 4,
    t 4 - t 5, t 5 - t 6, t 6 - t 7,
    B3 t - H1 t, B3 t - H3 t, B3 t - H5 t, B3 t - H7 t,
    R6 t - B3 t, D (t 0 + t 3) - R6 t, R6 t - W t,
    t 1 + t 2 - mu, H3 t - D23 t, M8 t - R6 t,
    (D (selected138 t) - eta) - M8 t,
    M8 t - fullExpr t 0, M8 t - complementExpr t 0,
    M8 t - fullExpr t 1, M8 t - fullExpr t 2,
    M8 t - complementExpr t 2, M8 t - fullExpr t 3,
    M8 t - fullExpr t 4, M8 t - complementExpr t 4,
    M8 t - fullExpr t 5, M8 t - complementExpr t 5,
    M8 t - fullExpr t 6, M8 t - complementExpr t 6,
    M8 t - fullExpr t 7, R6 t - (S8 t + t 7),
    (S8 t + 3 * t 7) - M8 t, D23 t - H1 t]

def commonRow (k : Fin 37) : Fin 99 := ⟨k.val, by omega⟩

/-- The 62 proper old masks in the source are 1,...,8,10,...,63.
Mask9 is the winning raw identity and is not a strict row. -/
def branchMask (k : Fin 62) : ℕ :=
  if k.val < 8 then k.val + 1 else k.val + 2

def branchRow (k : Fin 62) : Fin 99 := ⟨37 + k.val, by omega⟩

/-! H3-specific affine syntax. The verified compiler itself is imported;
no generic compiler or literal source row is recreated here. -/
open OriginalDescendingFifteenLiteralAffineRows
  (Expr K X coefficients evaluate evaluateCoefficients evaluate_coefficients
    oldExpr subsetExpr ascendingExpr descendingExpr)

/-! Notation adapters for the existing verified Expr evaluator; these
are exactly constructor reduction, not a new affine compiler. -/
private theorem h3_eval_notation_add (a b : Expr) (t : Point) :
    evaluate (a + b) t = evaluate a t + evaluate b t := by rfl

private theorem h3_eval_notation_sub (a b : Expr) (t : Point) :
    evaluate (a - b) t = evaluate a t - evaluate b t := by rfl

private theorem h3_eval_notation_smul (q : ℚ) (a : Expr) (t : Point) :
    evaluate (q • a) t = (q : ℝ) * evaluate a t := by rfl

private theorem h3_eval_notation_ite (p : Prop) [Decidable p] (a b : Expr) (t : Point) :
    evaluate (if p then a else b) t = if p then evaluate a t else evaluate b t := by
  split_ifs <;> rfl

private theorem h3_castCoord (j : Fin 6) :
    j.castSucc.castSucc = Fin.ofNat 8 j.val := by
  apply Fin.ext
  change j.val = j.val % 8
  exact (Nat.mod_eq_of_lt (lt_trans j.isLt (by decide : 6 < 8))).symm

private theorem h3_subset_sum_canonical (m : ℕ) (t : Point) :
    oldSubsetSum m t = ∑ j : Fin 6,
      if decide (m / 2 ^ j.val % 2 = 1) then t (Fin.ofNat 8 j.val) else 0 := by
  unfold oldSubsetSum
  apply Finset.sum_congr rfl
  intro j _
  rw [h3_castCoord j]

private theorem h3_eval_subset (m : ℕ) (t : Point) :
    evaluate (subsetExpr m) t = oldSubsetSum m t := by
  rw [h3_subset_sum_canonical]
  simp only [subsetExpr, h3_eval_notation_add, h3_eval_notation_ite]
  norm_num [evaluate, K, X, Nat.testBit_eq_decide_div_mod_eq, Fin.sum_univ_succ,
    Fin.ofNat, Fin.succ, add_assoc]
  rfl

private theorem h3_eval_ascending (m : ℕ) (t : Point) :
    evaluate (ascendingExpr m) t = A (oldSubsetSum m t) := by
  simp only [ascendingExpr, h3_eval_notation_add, h3_eval_notation_smul,
    h3_eval_subset]
  norm_num only [evaluate, K, A]
  ring

private theorem h3_eval_descending (m : ℕ) (t : Point) :
    evaluate (descendingExpr m) t = D (oldSubsetSum m t) := by
  simp only [descendingExpr, h3_eval_notation_sub, h3_eval_notation_smul,
    h3_eval_subset]
  norm_num only [evaluate, K, D]
  ring

private theorem h3_eval_R6 (t : Point) :
    evaluate (ascendingExpr 9) t = R6 t := by
  norm_num [h3_eval_ascending, h3_subset_sum_canonical, Fin.sum_univ_succ,
    Fin.ofNat, Fin.succ, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod, R6, A]
  rfl

private theorem h3_eval_B3 (t : Point) :
    evaluate (ascendingExpr 1) t = B3 t := by
  norm_num [h3_eval_ascending, h3_subset_sum_canonical, Fin.sum_univ_succ,
    Fin.ofNat, Fin.succ, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod, B3, A]

private theorem h3_eval_oppositeR6 (t : Point) :
    evaluate (descendingExpr 9) t = D (t 0 + t 3) := by
  norm_num [h3_eval_descending, h3_subset_sum_canonical, Fin.sum_univ_succ,
    Fin.ofNat, Fin.succ, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod, D]
  rfl

private theorem h3_eval_D23 (t : Point) :
    evaluate oldExpr t = D23 t := by
  simp only [oldExpr, h3_eval_notation_add, h3_eval_notation_sub, h3_eval_notation_smul]
  norm_num only [evaluate, K, X, D23, D]
  ring

private def h3M8Expr : Expr :=
  K (1 / 2) + (1 / 2 : ℚ) • (X 1 + X 3 + X 7) - K (1 / 1000000)

private theorem h3_eval_M8 (t : Point) :
    evaluate h3M8Expr t = M8 t := by
  simp only [h3M8Expr, h3_eval_notation_add, h3_eval_notation_sub,
    h3_eval_notation_smul]
  norm_num only [evaluate, K, X, M8, A, eta]
  ring

private def h3Opposite138Expr : Expr :=
  K (57 / 64) - (3 / 2 : ℚ) • (X 1 + X 3 + X 7) - K (1 / 1000000)

private theorem h3_eval_opposite138 (t : Point) :
    evaluate h3Opposite138Expr t = D (selected138 t) - eta := by
  simp only [h3Opposite138Expr, h3_eval_notation_add, h3_eval_notation_sub,
    h3_eval_notation_smul]
  norm_num only [evaluate, K, X, D, selected138, eta]
  ring

private def h3HistoryExpr : Fin 4 → Expr :=
  ![(3 : ℚ) • X 0, X 0 + X 1 + (3 : ℚ) • X 2,
    X 0 + X 1 + X 2 + X 3 + (3 : ℚ) • X 4,
    X 0 + X 1 + X 2 + X 3 + X 4 + X 5 + (3 : ℚ) • X 6]

private theorem h3_eval_history (j : Fin 4) (t : Point) :
    evaluate (h3HistoryExpr j) t = (![H1 t, H3 t, H5 t, H7 t] : Fin 4 → ℝ) j := by
  fin_cases j <;>
    norm_num only [h3HistoryExpr, h3_eval_notation_add, h3_eval_notation_smul,
      evaluate, X, H1, H3, H5, H7] <;> rfl

private def h3TotalExpr : Expr := X 0 + X 1 + X 2 + X 3 + X 4 + X 5 + X 6 + X 7

private theorem h3_eval_total (t : Point) :
    evaluate h3TotalExpr t = S8 t := by
  simp only [h3TotalExpr, h3_eval_notation_add]
  simpa [evaluate, X, S8, Fin.sum_univ_succ, Fin.succ, add_assoc]

private def h3FullExpr (j : Fin 8) : Expr :=
  (if (0 : Fin 8) < j then X 0 else K 0) +
  (if (1 : Fin 8) < j then X 1 else K 0) +
  (if (2 : Fin 8) < j then X 2 else K 0) +
  (if (3 : Fin 8) < j then X 3 else K 0) +
  (if (4 : Fin 8) < j then X 4 else K 0) +
  (if (5 : Fin 8) < j then X 5 else K 0) +
  (if (6 : Fin 8) < j then X 6 else K 0) +
  (if (7 : Fin 8) < j then X 7 else K 0) + (2 : ℚ) • X j

private theorem h3_eval_full (j : Fin 8) (t : Point) :
    evaluate (h3FullExpr j) t = fullExpr t j := by
  fin_cases j <;>
    simp only [h3FullExpr, fullExpr, h3_eval_notation_add, h3_eval_notation_smul,
      h3_eval_notation_ite, Fin.sum_univ_succ] <;>
    norm_num [evaluate, K, X, Fin.succ, Fin.ofNat, Fin.lt_def,
      Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod, add_assoc]

private def h3ComplementExpr (j : Fin 8) : Expr :=
  X 1 + X 3 + X 7 +
    ((if (0 : Fin 8) < j then X 0 else K 0) +
     (if (2 : Fin 8) < j then X 2 else K 0) +
     (if (4 : Fin 8) < j then X 4 else K 0) +
     (if (5 : Fin 8) < j then X 5 else K 0) +
     (if (6 : Fin 8) < j then X 6 else K 0)) + (2 : ℚ) • X j

private theorem h3_eval_complement (j : Fin 8) (t : Point) :
    evaluate (h3ComplementExpr j) t = complementExpr t j := by
  fin_cases j <;>
    simp only [h3ComplementExpr, complementExpr, selected138,
      h3_eval_notation_add, h3_eval_notation_smul, h3_eval_notation_ite,
      Fin.sum_univ_succ] <;>
    norm_num [evaluate, K, X, Fin.sum_univ_zero,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.lt_def, Fin.ext_iff, Fin.val_zero, Fin.val_succ,
      Fin.val_mk, Fin.coe_ofNat_eq_mod,
      Fin.mk_lt_mk, Fin.mk.inj_iff, ne_eq, Nat.reduceMod,
      and_true, true_and, and_false, false_and,
      not_true_eq_false, not_false_eq_true, ite_true, ite_false, add_assoc]

private def h3CommonExpr : Fin 37 → Expr :=
  ![K (25 / 128) - X 0, X 2 - K (1 / 100), X 7 - K (53 / 13824),
    X 0 - X 1, X 1 - X 2, X 2 - X 3, X 3 - X 4,
    X 4 - X 5, X 5 - X 6, X 6 - X 7,
    ascendingExpr 1 - h3HistoryExpr 0, ascendingExpr 1 - h3HistoryExpr 1,
    ascendingExpr 1 - h3HistoryExpr 2, ascendingExpr 1 - h3HistoryExpr 3,
    ascendingExpr 9 - ascendingExpr 1, descendingExpr 9 - ascendingExpr 9,
    ascendingExpr 9 - (K (153 / 256) - (3 / 8 : ℚ) • X 2),
    X 1 + X 2 - K (25 / 128), h3HistoryExpr 1 - oldExpr,
    h3M8Expr - ascendingExpr 9, h3Opposite138Expr - h3M8Expr,
    h3M8Expr - h3FullExpr 0, h3M8Expr - h3ComplementExpr 0,
    h3M8Expr - h3FullExpr 1, h3M8Expr - h3FullExpr 2,
    h3M8Expr - h3ComplementExpr 2, h3M8Expr - h3FullExpr 3,
    h3M8Expr - h3FullExpr 4, h3M8Expr - h3ComplementExpr 4,
    h3M8Expr - h3FullExpr 5, h3M8Expr - h3ComplementExpr 5,
    h3M8Expr - h3FullExpr 6, h3M8Expr - h3ComplementExpr 6,
    h3M8Expr - h3FullExpr 7, ascendingExpr 9 - (h3TotalExpr + X 7),
    h3TotalExpr + (3 : ℚ) • X 7 - h3M8Expr, oldExpr - h3HistoryExpr 0]

private theorem h3_eval_common (k : Fin 37) (t : Point) :
    evaluate (h3CommonExpr k) t = commonSlack t k := by
  fin_cases k <;>
    simp only [h3CommonExpr, commonSlack, Matrix.cons_val_zero', Matrix.cons_val_succ',
      h3_eval_notation_add, h3_eval_notation_sub, h3_eval_notation_smul,
      h3_eval_history, h3_eval_B3, h3_eval_R6, h3_eval_oppositeR6, h3_eval_D23,
      h3_eval_M8, h3_eval_opposite138, h3_eval_full, h3_eval_complement,
      h3_eval_total] <;>
    norm_num [evaluate, K, X, mu, W] <;> ring

private def h3BranchExpr (i : Fin 12) (m : ℕ) : Expr :=
  ascendingExpr 9 -
    (if m ∈ leftMasks i then ascendingExpr m else descendingExpr m)

private theorem h3_eval_branch (i : Fin 12) (m : ℕ) (t : Point) :
    evaluate (h3BranchExpr i m) t = R6 t - oldPlane i m t := by
  by_cases h : m ∈ leftMasks i
  · simp only [h3BranchExpr, oldPlane, if_pos h, h3_eval_notation_sub]
    rw [h3_eval_R6, h3_eval_ascending]
  · simp only [h3BranchExpr, oldPlane, if_neg h, h3_eval_notation_sub]
    rw [h3_eval_R6, h3_eval_descending]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_common_coeff_00 :
    ∀ (k : Fin 37) (j : Fin 9),
      (sourceAffineRows (0 : Fin 12) (commonRow k)).2 j =
        coefficients (h3CommonExpr k) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_common_coeff_01 :
    ∀ (k : Fin 37) (j : Fin 9),
      (sourceAffineRows (1 : Fin 12) (commonRow k)).2 j =
        coefficients (h3CommonExpr k) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_common_coeff_02 :
    ∀ (k : Fin 37) (j : Fin 9),
      (sourceAffineRows (2 : Fin 12) (commonRow k)).2 j =
        coefficients (h3CommonExpr k) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_common_coeff_03 :
    ∀ (k : Fin 37) (j : Fin 9),
      (sourceAffineRows (3 : Fin 12) (commonRow k)).2 j =
        coefficients (h3CommonExpr k) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_common_coeff_04 :
    ∀ (k : Fin 37) (j : Fin 9),
      (sourceAffineRows (4 : Fin 12) (commonRow k)).2 j =
        coefficients (h3CommonExpr k) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_common_coeff_05 :
    ∀ (k : Fin 37) (j : Fin 9),
      (sourceAffineRows (5 : Fin 12) (commonRow k)).2 j =
        coefficients (h3CommonExpr k) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_common_coeff_06 :
    ∀ (k : Fin 37) (j : Fin 9),
      (sourceAffineRows (6 : Fin 12) (commonRow k)).2 j =
        coefficients (h3CommonExpr k) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_common_coeff_07 :
    ∀ (k : Fin 37) (j : Fin 9),
      (sourceAffineRows (7 : Fin 12) (commonRow k)).2 j =
        coefficients (h3CommonExpr k) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_common_coeff_08 :
    ∀ (k : Fin 37) (j : Fin 9),
      (sourceAffineRows (8 : Fin 12) (commonRow k)).2 j =
        coefficients (h3CommonExpr k) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_common_coeff_09 :
    ∀ (k : Fin 37) (j : Fin 9),
      (sourceAffineRows (9 : Fin 12) (commonRow k)).2 j =
        coefficients (h3CommonExpr k) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_common_coeff_10 :
    ∀ (k : Fin 37) (j : Fin 9),
      (sourceAffineRows (10 : Fin 12) (commonRow k)).2 j =
        coefficients (h3CommonExpr k) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_common_coeff_11 :
    ∀ (k : Fin 37) (j : Fin 9),
      (sourceAffineRows (11 : Fin 12) (commonRow k)).2 j =
        coefficients (h3CommonExpr k) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_branch_coeff_00 :
    ∀ (k : Fin 62) (j : Fin 9),
      (sourceAffineRows (0 : Fin 12) (branchRow k)).2 j =
        coefficients (h3BranchExpr (0 : Fin 12) (branchMask k)) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_branch_coeff_01 :
    ∀ (k : Fin 62) (j : Fin 9),
      (sourceAffineRows (1 : Fin 12) (branchRow k)).2 j =
        coefficients (h3BranchExpr (1 : Fin 12) (branchMask k)) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_branch_coeff_02 :
    ∀ (k : Fin 62) (j : Fin 9),
      (sourceAffineRows (2 : Fin 12) (branchRow k)).2 j =
        coefficients (h3BranchExpr (2 : Fin 12) (branchMask k)) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_branch_coeff_03 :
    ∀ (k : Fin 62) (j : Fin 9),
      (sourceAffineRows (3 : Fin 12) (branchRow k)).2 j =
        coefficients (h3BranchExpr (3 : Fin 12) (branchMask k)) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_branch_coeff_04 :
    ∀ (k : Fin 62) (j : Fin 9),
      (sourceAffineRows (4 : Fin 12) (branchRow k)).2 j =
        coefficients (h3BranchExpr (4 : Fin 12) (branchMask k)) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_branch_coeff_05 :
    ∀ (k : Fin 62) (j : Fin 9),
      (sourceAffineRows (5 : Fin 12) (branchRow k)).2 j =
        coefficients (h3BranchExpr (5 : Fin 12) (branchMask k)) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_branch_coeff_06 :
    ∀ (k : Fin 62) (j : Fin 9),
      (sourceAffineRows (6 : Fin 12) (branchRow k)).2 j =
        coefficients (h3BranchExpr (6 : Fin 12) (branchMask k)) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_branch_coeff_07 :
    ∀ (k : Fin 62) (j : Fin 9),
      (sourceAffineRows (7 : Fin 12) (branchRow k)).2 j =
        coefficients (h3BranchExpr (7 : Fin 12) (branchMask k)) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_branch_coeff_08 :
    ∀ (k : Fin 62) (j : Fin 9),
      (sourceAffineRows (8 : Fin 12) (branchRow k)).2 j =
        coefficients (h3BranchExpr (8 : Fin 12) (branchMask k)) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_branch_coeff_09 :
    ∀ (k : Fin 62) (j : Fin 9),
      (sourceAffineRows (9 : Fin 12) (branchRow k)).2 j =
        coefficients (h3BranchExpr (9 : Fin 12) (branchMask k)) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_branch_coeff_10 :
    ∀ (k : Fin 62) (j : Fin 9),
      (sourceAffineRows (10 : Fin 12) (branchRow k)).2 j =
        coefficients (h3BranchExpr (10 : Fin 12) (branchMask k)) j := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem h3_branch_coeff_11 :
    ∀ (k : Fin 62) (j : Fin 9),
      (sourceAffineRows (11 : Fin 12) (branchRow k)).2 j =
        coefficients (h3BranchExpr (11 : Fin 12) (branchMask k)) j := by
  decide +kernel

private theorem h3_common_coefficients (i : Fin 12) (k : Fin 37) (j : Fin 9) :
    (sourceAffineRows i (commonRow k)).2 j = coefficients (h3CommonExpr k) j := by
  fin_cases i
  · exact h3_common_coeff_00 k j
  · exact h3_common_coeff_01 k j
  · exact h3_common_coeff_02 k j
  · exact h3_common_coeff_03 k j
  · exact h3_common_coeff_04 k j
  · exact h3_common_coeff_05 k j
  · exact h3_common_coeff_06 k j
  · exact h3_common_coeff_07 k j
  · exact h3_common_coeff_08 k j
  · exact h3_common_coeff_09 k j
  · exact h3_common_coeff_10 k j
  · exact h3_common_coeff_11 k j

private theorem h3_branch_coefficients (i : Fin 12) (k : Fin 62) (j : Fin 9) :
    (sourceAffineRows i (branchRow k)).2 j = coefficients (h3BranchExpr i (branchMask k)) j := by
  fin_cases i
  · exact h3_branch_coeff_00 k j
  · exact h3_branch_coeff_01 k j
  · exact h3_branch_coeff_02 k j
  · exact h3_branch_coeff_03 k j
  · exact h3_branch_coeff_04 k j
  · exact h3_branch_coeff_05 k j
  · exact h3_branch_coeff_06 k j
  · exact h3_branch_coeff_07 k j
  · exact h3_branch_coeff_08 k j
  · exact h3_branch_coeff_09 k j
  · exact h3_branch_coeff_10 k j
  · exact h3_branch_coeff_11 k j

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- UNEVALUATED symbolic equality against every original common row.
The free real tuple is never sampled or replaced by a centre. -/
theorem source_common_row (i : Fin 12) (k : Fin 37) (t : Point) :
    evalAffine (sourceAffineRows i (commonRow k)).2 t = commonSlack t k := by
  have hcoeff : (sourceAffineRows i (commonRow k)).2 = coefficients (h3CommonExpr k) :=
    funext (h3_common_coefficients i k)
  change evaluateCoefficients (sourceAffineRows i (commonRow k)).2 t = commonSlack t k
  rw [hcoeff, evaluate_coefficients]
  exact h3_eval_common k t

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- UNEVALUATED symbolic equality against the original 12-by-62
assigned old planes; no payload-equality hypothesis is accepted. -/
theorem source_branch_row (i : Fin 12) (k : Fin 62) (t : Point) :
    evalAffine (sourceAffineRows i (branchRow k)).2 t =
      R6 t - oldPlane i (branchMask k) t := by
  have hcoeff : (sourceAffineRows i (branchRow k)).2 =
      coefficients (h3BranchExpr i (branchMask k)) := funext (h3_branch_coefficients i k)
  change evaluateCoefficients (sourceAffineRows i (branchRow k)).2 t =
    R6 t - oldPlane i (branchMask k) t
  rw [hcoeff, evaluate_coefficients]
  exact h3_eval_branch i (branchMask k) t

theorem branchMask_mem (k : Fin 62) :
    branchMask k ∈ Finset.Icc 1 63 ∧ branchMask k ≠ 9 := by
  have hk := k.isLt
  unfold branchMask
  split_ifs <;> simp only [Finset.mem_Icc] <;> omega

theorem branchMask_covers (m : ℕ) (hm : m ∈ Finset.Icc 1 63)
    (hm9 : m ≠ 9) : ∃ k : Fin 62, branchMask k = m := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hm
  by_cases h : m < 9
  · refine ⟨⟨m - 1, by omega⟩, ?_⟩
    simp only [branchMask]
    have hh : m - 1 < 8 := by omega
    rw [if_pos hh]
    omega
  · refine ⟨⟨m - 2, by omega⟩, ?_⟩
    simp only [branchMask]
    have hh : ¬m - 2 < 8 := by omega
    rw [if_neg hh]
    omega

/-- A lossless split of all 99 rows; neither the old-plane family nor
the short physical square rows can disappear during the conversion. -/
theorem sourceAffineGuard_iff_common_and_branches (i : Fin 12) (t : Point) :
    sourceAffineGuard i t ↔
      (∀ k : Fin 37, 0 < commonSlack t k) ∧
      (∀ k : Fin 62, oldPlane i (branchMask k) t < R6 t) := by
  constructor
  · intro h
    constructor
    · intro k
      rw [← source_common_row i k t]
      exact h (commonRow k)
    · intro k
      have hk := h (branchRow k)
      rw [source_branch_row] at hk
      exact sub_pos.mp hk
  · rintro ⟨hc, hb⟩ k
    by_cases hk : k.val < 37
    · let j : Fin 37 := ⟨k.val, hk⟩
      have hj : commonRow j = k := Fin.ext rfl
      rw [← hj, source_common_row]
      exact hc j
    · let j : Fin 62 := ⟨k.val - 37, by have := k.isLt; omega⟩
      have hj : branchRow j = k := by
        apply Fin.ext
        dsimp [branchRow, j]
        omega
      rw [← hj, source_branch_row]
      exact sub_pos.mpr (hb j)

def fullRow : Fin 8 → Fin 37 := ![21, 23, 24, 26, 27, 29, 31, 33]
def remainingSlot : Fin 5 → Fin 8 := ![0, 2, 4, 5, 6]
def complementRow : Fin 5 → Fin 37 := ![22, 25, 28, 30, 32]

private theorem commonSlack_full (j : Fin 8) (t : Point) :
    commonSlack t (fullRow j) = M8 t - fullExpr t j := by
  fin_cases j <;> simp [commonSlack, fullRow]

private theorem commonSlack_complement (j : Fin 5) (t : Point) :
    commonSlack t (complementRow j) = M8 t - complementExpr t (remainingSlot j) := by
  fin_cases j <;> simp [commonSlack, complementRow, remainingSlot]

private theorem remainingSlot_covers (j : Fin 8)
    (hj1 : j ≠ 1) (hj3 : j ≠ 3) (hj7 : j ≠ 7) :
    ∃ k : Fin 5, remainingSlot k = j := by
  fin_cases j
  · exact ⟨0, rfl⟩
  · exact (hj1 rfl).elim
  · exact ⟨1, rfl⟩
  · exact (hj3 rfl).elim
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact (hj7 rfl).elim

private theorem strictH3_of_common_and_branches {i : Fin 12} {t : Point}
    (hc : ∀ k : Fin 37, 0 < commonSlack t k)
    (hb : ∀ k : Fin 62, oldPlane i (branchMask k) t < R6 t) :
    StrictH3 i t where
  largest := by simpa [commonSlack] using sub_pos.mp (hc 0)
  third_cutoff := by simpa [commonSlack] using sub_pos.mp (hc 1)
  eighth_cutoff := by simpa [commonSlack] using sub_pos.mp (hc 2)
  ordered := by
    intro j
    fin_cases j
    · simpa [commonSlack] using sub_pos.mp (hc 3)
    · simpa [commonSlack] using sub_pos.mp (hc 4)
    · simpa [commonSlack] using sub_pos.mp (hc 5)
    · simpa [commonSlack] using sub_pos.mp (hc 6)
    · simpa [commonSlack] using sub_pos.mp (hc 7)
    · simpa [commonSlack] using sub_pos.mp (hc 8)
    · simpa [commonSlack] using sub_pos.mp (hc 9)
  first_below_B3 := by simpa [commonSlack] using sub_pos.mp (hc 10)
  H3_below_B3 := by simpa [commonSlack] using sub_pos.mp (hc 11)
  H5_below_B3 := by simpa [commonSlack] using sub_pos.mp (hc 12)
  H7_below_B3 := by simpa [commonSlack] using sub_pos.mp (hc 13)
  R6_above_B3 := by simpa [commonSlack] using sub_pos.mp (hc 14)
  winner9_ascending := by simpa [commonSlack] using sub_pos.mp (hc 15)
  W_below_R6 := by simpa [commonSlack] using sub_pos.mp (hc 16)
  d23_high := by simpa [commonSlack] using sub_pos.mp (hc 17)
  first_H3_failure := by simpa [commonSlack] using sub_pos.mp (hc 18)
  previous_H1_pass := by simpa [commonSlack] using sub_pos.mp (hc 36)
  improved := by simpa [commonSlack] using sub_pos.mp (hc 19)
  selected_descending_license := by simpa [commonSlack] using sub_pos.mp (hc 20)
  full_squares := by
    intro j
    have h := hc (fullRow j)
    rw [commonSlack_full] at h
    exact sub_pos.mp h
  selected_remaining_squares := by
    intro j hj1 hj3 hj7
    obtain ⟨k, rfl⟩ := remainingSlot_covers j hj1 hj3 hj7
    have h := hc (complementRow k)
    rw [commonSlack_complement] at h
    exact sub_pos.mp h
  old_residual := by simpa [commonSlack] using sub_pos.mp (hc 34)
  new_residual := by simpa [commonSlack] using sub_pos.mp (hc 35)
  old_planes := by
    intro m hm hm9
    obtain ⟨k, rfl⟩ := branchMask_covers m hm hm9
    exact hb k

private theorem strictH3_common_pos {i : Fin 12} {t : Point}
    (h : StrictH3 i t) : ∀ k : Fin 37, 0 < commonSlack t k := by
  intro k
  fin_cases k
  · simpa [commonSlack] using sub_pos.mpr h.largest
  · simpa [commonSlack] using sub_pos.mpr h.third_cutoff
  · simpa [commonSlack] using sub_pos.mpr h.eighth_cutoff
  · simpa [commonSlack] using sub_pos.mpr (h.ordered 0)
  · simpa [commonSlack] using sub_pos.mpr (h.ordered 1)
  · simpa [commonSlack] using sub_pos.mpr (h.ordered 2)
  · simpa [commonSlack] using sub_pos.mpr (h.ordered 3)
  · simpa [commonSlack] using sub_pos.mpr (h.ordered 4)
  · simpa [commonSlack] using sub_pos.mpr (h.ordered 5)
  · simpa [commonSlack] using sub_pos.mpr (h.ordered 6)
  · simpa [commonSlack] using sub_pos.mpr h.first_below_B3
  · simpa [commonSlack] using sub_pos.mpr h.H3_below_B3
  · simpa [commonSlack] using sub_pos.mpr h.H5_below_B3
  · simpa [commonSlack] using sub_pos.mpr h.H7_below_B3
  · simpa [commonSlack] using sub_pos.mpr h.R6_above_B3
  · simpa [commonSlack] using sub_pos.mpr h.winner9_ascending
  · simpa [commonSlack] using sub_pos.mpr h.W_below_R6
  · simpa [commonSlack] using sub_pos.mpr h.d23_high
  · simpa [commonSlack] using sub_pos.mpr h.first_H3_failure
  · simpa [commonSlack] using sub_pos.mpr h.improved
  · simpa [commonSlack] using sub_pos.mpr h.selected_descending_license
  · simpa [commonSlack, fullExpr] using sub_pos.mpr (h.full_squares 0)
  · simpa [commonSlack, complementExpr] using sub_pos.mpr
      (h.selected_remaining_squares 0 (by decide) (by decide) (by decide))
  · simpa [commonSlack, fullExpr] using sub_pos.mpr (h.full_squares 1)
  · simpa [commonSlack, fullExpr] using sub_pos.mpr (h.full_squares 2)
  · simpa [commonSlack, complementExpr] using sub_pos.mpr
      (h.selected_remaining_squares 2 (by decide) (by decide) (by decide))
  · simpa [commonSlack, fullExpr] using sub_pos.mpr (h.full_squares 3)
  · simpa [commonSlack, fullExpr] using sub_pos.mpr (h.full_squares 4)
  · simpa [commonSlack, complementExpr] using sub_pos.mpr
      (h.selected_remaining_squares 4 (by decide) (by decide) (by decide))
  · simpa [commonSlack, fullExpr] using sub_pos.mpr (h.full_squares 5)
  · simpa [commonSlack, complementExpr] using sub_pos.mpr
      (h.selected_remaining_squares 5 (by decide) (by decide) (by decide))
  · simpa [commonSlack, fullExpr] using sub_pos.mpr (h.full_squares 6)
  · simpa [commonSlack, complementExpr] using sub_pos.mpr
      (h.selected_remaining_squares 6 (by decide) (by decide) (by decide))
  · simpa [commonSlack, fullExpr] using sub_pos.mpr (h.full_squares 7)
  · simpa [commonSlack] using sub_pos.mpr h.old_residual
  · simpa [commonSlack] using sub_pos.mpr h.new_residual
  · simpa [commonSlack] using sub_pos.mpr h.previous_H1_pass

/-- Exact equivalence on every real point, including all boundary ties.
This eliminates the redundant semantic input from the original H3 guard. -/
theorem sourceAffineGuard_iff_StrictH3 (i : Fin 12) (t : Point) :
    sourceAffineGuard i t ↔ StrictH3 i t := by
  rw [sourceAffineGuard_iff_common_and_branches]
  constructor
  · rintro ⟨hc, hb⟩
    exact strictH3_of_common_and_branches hc hb
  · intro h
    refine ⟨strictH3_common_pos h, ?_⟩
    intro k
    exact h.old_planes (branchMask k) (branchMask_mem k).1 (branchMask_mem k).2

/-- The selected tent permission follows from the original strict rows.
The identity M8=A(selected)-eta is used, not assumed as a licence. -/
theorem source_selected_license {i : Fin 12} {t : Point}
    (h : sourceAffineGuard i t) :
    M8 t < VariableEnvelope.v (selected138 t) := by
  have hs := (sourceAffineGuard_iff_StrictH3 i t).mp h
  rw [VariableEnvelope.v_eq_min]
  apply lt_min
  · dsimp [M8, A, eta, selected138, VariableEnvelope.A]
    linarith
  · have hd := hs.selected_descending_license
    dsimp [D, eta, VariableEnvelope.C] at hd ⊢
    linarith

theorem source_newCap_lt_Lambda {i : Fin 12} {t : Point}
    (h : sourceAffineGuard i t) : M8 t < (153 / 256 : ℝ) := by
  exact (source_selected_license h).trans_le (VariableEnvelope.v_le_cap _)

/-- The selected physical mask is the unchanged source mask138. -/
def selectedSlots : Finset (Fin 8) := {1, 3, 7}

theorem source_full_and_selected_squares {i : Fin 12} {t : Point}
    (h : sourceAffineGuard i t) :
    (∀ j, prefixSquareExpr t j < M8 t) ∧
      (∀ j ∉ selectedSlots, selectedSquareExpr selectedSlots t j < M8 t) := by
  have hs := (sourceAffineGuard_iff_StrictH3 i t).mp h
  constructor
  · intro j
    simpa [prefixSquareExpr, Finset.sum_filter] using hs.full_squares j
  · intro j hj
    have hnot : j ≠ 1 ∧ j ≠ 3 ∧ j ≠ 7 := by
      simpa [selectedSlots] using hj
    have hh := hs.selected_remaining_squares j hnot.1 hnot.2.1 hnot.2.2
    simpa [selectedSquareExpr, selectedSlots, selected138, Finset.sum_filter,
      add_assoc, and_assoc] using hh

/-- Same N, same tuple, same M8: actual integer square support is now
supplied by source-domain membership rather than a PhysicalRows field. -/
theorem source_integer_square_gates {i : Fin 12} {t : Point}
    (h : sourceAffineGuard i t) (N : ℝ) (hN : 1 < N)
    (p : Fin 8 → ℕ) (hp : ∀ j, (p j : ℝ) ≤ N ^ t j) :
    (∀ j, ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j), p k : ℕ) : ℝ) *
      (p j : ℝ) ^ 2 < N ^ M8 t) ∧
    (∀ j ∉ selectedSlots,
      ((∏ k ∈ selectedSlots, p k : ℕ) : ℝ) *
        ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j ∧ k ∉ selectedSlots),
          p k : ℕ) : ℝ) * (p j : ℝ) ^ 2 < N ^ M8 t) := by
  have hs := source_full_and_selected_squares h
  exact ⟨fun j => prefixSquareExpr_actual_gate N hN p t hp j (hs.1 j),
    fun j hj => selectedSquareExpr_actual_gate selectedSlots N hN p t hp j (hs.2 j hj)⟩

/-- Exact original guard, with only the duplicated semantic conjunct
removed. The actual retained-parent and upper-parent conditions are
explicitly still required and are not replaced by a branch licence. -/
theorem actualH3Guard_iff_source (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) :
    ActualH3Guard N lambda6 pre ↔
      pre.length = 8 ∧ ∃ i : Fin 12,
        sourceAffineGuard i (primeHistoryLogCoordinates N 8 pre) ∧
        H7 (primeHistoryLogCoordinates N 8 pre) < lambda6 (rosserAncestor 6 pre) ∧
        lambda6 (rosserAncestor 6 pre) ≤ R6 (primeHistoryLogCoordinates N 8 pre) := by
  constructor
  · rintro ⟨hlen, i, _, hrows, hlo, hhi⟩
    exact ⟨hlen, i, hrows, hlo, hhi⟩
  · rintro ⟨hlen, i, hrows, hlo, hhi⟩
    exact ⟨hlen, i, (sourceAffineGuard_iff_StrictH3 i _).mp hrows, hrows, hlo, hhi⟩

/-- A dictionary for the EXISTING physical exponent. No replacement
policy, ambient prime universe, coefficient, or rho is introduced. -/
theorem h3Exponent_eq_source_dispatch (N : ℝ) (lambda6 : List ℕ → ℝ)
    (pre : List ℕ) :
    h3Exponent N lambda6 pre =
      if pre.length = 8 ∧ ∃ i : Fin 12,
          sourceAffineGuard i (primeHistoryLogCoordinates N 8 pre) ∧
          H7 (primeHistoryLogCoordinates N 8 pre) < lambda6 (rosserAncestor 6 pre) ∧
          lambda6 (rosserAncestor 6 pre) ≤ R6 (primeHistoryLogCoordinates N 8 pre)
      then M8 (primeHistoryLogCoordinates N 8 pre)
      else lambda6 (rosserAncestor 6 pre) := by
  unfold h3Exponent
  exact ite_cond_congr (propext (actualH3Guard_iff_source N lambda6 pre))

end
end ImbalancedChen.P4AOriginalFirstFailureH3SourceSemantics
