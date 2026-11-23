import ImbalancedChen.OriginalDescendingFifteenLiteralAffineRows
import ImbalancedChen.P4AOriginalAscendingFourteenAffineSource
import ImbalancedChen.P4AOriginalSeed7Unequal15Literal
import ImbalancedChen.P4AOriginalFirstFailureH5H7Literal
import ImbalancedChen.ActualExtendedThirdIdealCap
import ImbalancedChen.SelectedPrefixBoxCap
import Mathlib.Tactic

/-!
Compilation records: docs/verification/20261123-blue-compilation.
These 47 literal sources are exactly ascending14+seed7+unequal15+H5/H7.
Inputs are membership in the entire original strict affine row list.
No parent, licence, cap or square estimate is accepted as a premise.
Symbolic finite bodies are UNEVALUATED. The original gated/clipped ideal
third is retained. Its upper bound is not called the actual sixth parent.
-/
namespace ImbalancedChen.P4AOriginalRemainingEighthSources
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope

abbrev Point := Fin 8 → ℝ
inductive Cell where
  | ascending (i : Fin 14)
  | seed
  | nine (i : Fin 13)
  | fiftyA
  | fiftyD
  | h5 (i : Fin 7)
  | h7 (i : Fin 10)
  deriving DecidableEq, Fintype

def rowCount : Cell → ℕ
  | .ascending _ | .seed | .fiftyD => 96
  | .nine _ => 97
  | .fiftyA => 95
  | .h5 _ => 100
  | .h7 _ => 101

def row : (c : Cell) → Fin (rowCount c) → Fin 9 → ℚ
  | .ascending i, k => P4AOriginalAscendingFourteenAffineSource.rows i k
  | .seed, k => (P4AOriginalSeed7Unequal15Literal.seed7Rows k).2
  | .nine i, k => (P4AOriginalSeed7Unequal15Literal.nineRows i k).2
  | .fiftyA, k => (P4AOriginalSeed7Unequal15Literal.fiftyAscRows k).2
  | .fiftyD, k => (P4AOriginalSeed7Unequal15Literal.fiftyDescRows k).2
  | .h5 i, k => (P4AOriginalFirstFailureH5H7Literal.h5AffineRows i k).2
  | .h7 i, k => (P4AOriginalFirstFailureH5H7Literal.h7AffineRows i k).2

def evalRow (a : Fin 9 → ℚ) (t : Point) : ℝ :=
  (a 0 : ℝ) + ∑ j : Fin 8, (a j.succ : ℝ) * t j
def Source (c : Cell) (t : Point) : Prop := ∀ k, 0 < evalRow (row c k) t

def selected : Cell → Finset (Fin 8)
  | .ascending _ | .seed => {0,7}
  | .fiftyA => {3,4,5,7}
  | .fiftyD => {1,2,7}
  | _ => {1,3,7}
def selectedSum (c : Cell) (t : Point) : ℝ := ∑ j ∈ selected c, t j
def eta : ℝ := 1 / 1000000
def comparison : Cell → Point → ℝ
  | .ascending _, t | .seed, t => C (t 1 + t 2)
  | .fiftyA, t => A (t 1 + t 4 + t 5)
  | .fiftyD, t => C (t 1 + t 4 + t 5)
  | _, t => A (t 0 + t 3)
def minorant : Cell → Point → ℝ
  | .ascending _, t | .seed, t | .nine _, t => C (t 1 + t 2)
  | .fiftyA, t => A (t 1 + t 2)
  | _, t => A (t 0)
def descendingNew : Cell → Bool
  | .fiftyD => true
  | _ => false
def newCap (c : Cell) (t : Point) : ℝ :=
  (if descendingNew c then C (selectedSum c t) else A (selectedSum c t)) - eta
def otherPlane (c : Cell) (s : ℝ) : ℝ :=
  if descendingNew c then A s else C s
def history (t : Point) : Fin 4 → ℝ :=
  ![3*t 0, t 0+t 1+3*t 2, t 0+t 1+t 2+t 3+3*t 4,
    t 0+t 1+t 2+t 3+t 4+t 5+3*t 6]
def total (t : Point) : ℝ := ∑ j, t j
def sideSlack : Cell → Point → ℝ
  | .ascending _, t | .seed, t | .nine _, t => 2*(t 1+t 2-mu)
  | .fiftyA, t => 2*(mu-t 1-t 2)
  | _, t => mu-t 0

/-- Selected slots use the already present largest row as a harmless
selector entry. No selected-complement obligation is asserted there. -/
def commonSlack (c : Cell) (t : Point) : Fin 35 → ℝ :=
  ![mu-t 0, t 2-1/100, t 7-53/13824,
    t 0-t 1, t 1-t 2, t 2-t 3, t 3-t 4, t 4-t 5, t 5-t 6, t 6-t 7,
    minorant c t-history t 0, minorant c t-history t 1,
    minorant c t-history t 2, minorant c t-history t 3,
    comparison c t-VariableEnvelope.B (t 2), newCap c t-comparison c t,
    total t+3*t 7-newCap c t,
    otherPlane c (selectedSum c t)-eta-newCap c t,
    newCap c t-prefixSquareExpr t 0, newCap c t-prefixSquareExpr t 1,
    newCap c t-prefixSquareExpr t 2, newCap c t-prefixSquareExpr t 3,
    newCap c t-prefixSquareExpr t 4, newCap c t-prefixSquareExpr t 5,
    newCap c t-prefixSquareExpr t 6, newCap c t-prefixSquareExpr t 7,
    if 0 ∈ selected c then mu-t 0 else newCap c t-selectedSquareExpr (selected c) t 0,
    if 1 ∈ selected c then mu-t 0 else newCap c t-selectedSquareExpr (selected c) t 1,
    if 2 ∈ selected c then mu-t 0 else newCap c t-selectedSquareExpr (selected c) t 2,
    if 3 ∈ selected c then mu-t 0 else newCap c t-selectedSquareExpr (selected c) t 3,
    if 4 ∈ selected c then mu-t 0 else newCap c t-selectedSquareExpr (selected c) t 4,
    if 5 ∈ selected c then mu-t 0 else newCap c t-selectedSquareExpr (selected c) t 5,
    if 6 ∈ selected c then mu-t 0 else newCap c t-selectedSquareExpr (selected c) t 6,
    if 7 ∈ selected c then mu-t 0 else newCap c t-selectedSquareExpr (selected c) t 7,
    sideSlack c t]

-- GENERATED_ROW_IDENTITIES
def commonRow : (c : Cell) → Fin 35 → Fin (rowCount c)
  | .ascending _ => (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 33, 17, 18, 19, 21, 23, 25, 27, 29, 31, 0, 20, 22, 24, 26, 28, 30, 0, 14] : Fin 35 → Fin 96)
  | .seed => (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 33, 17, 18, 19, 21, 23, 25, 27, 29, 31, 0, 20, 22, 24, 26, 28, 30, 0, 14] : Fin 35 → Fin 96)
  | .nine _ => (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 17, 18, 34, 19, 20, 22, 23, 25, 26, 28, 30, 32, 21, 0, 24, 0, 27, 29, 31, 0, 16] : Fin 35 → Fin 97)
  | .fiftyA => (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 16, 79, 94, 80, 81, 83, 85, 87, 88, 89, 90, 92, 82, 84, 86, 0, 0, 0, 91, 0, 10] : Fin 35 → Fin 95)
  | .fiftyD => (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 16, 79, 95, 80, 81, 83, 84, 85, 87, 89, 91, 93, 82, 0, 0, 86, 88, 90, 92, 0, 0] : Fin 35 → Fin 96)
  | .h5 _ => (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 19, 35, 20, 21, 23, 24, 26, 27, 29, 31, 33, 22, 0, 25, 0, 28, 30, 32, 0, 0] : Fin 35 → Fin 100)
  | .h7 _ => (![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 19, 35, 20, 21, 23, 24, 26, 27, 29, 31, 33, 22, 0, 25, 0, 28, 30, 32, 0, 0] : Fin 35 → Fin 101)

def branchRow : (c : Cell) → Fin 62 → Fin (rowCount c)
  | .ascending _ => (![34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95] : Fin 62 → Fin 96)
  | .seed => (![34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95] : Fin 62 → Fin 96)
  | .nine _ => (![35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96] : Fin 62 → Fin 97)
  | .fiftyA => (![17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78] : Fin 62 → Fin 95)
  | .fiftyD => (![17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78] : Fin 62 → Fin 96)
  | .h5 _ => (![38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99] : Fin 62 → Fin 100)
  | .h7 _ => (![39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100] : Fin 62 → Fin 101)

def leftMasks : Cell → Finset ℕ
  | .ascending i => P4AOriginalAscendingFourteenAffineSource.leftMasks i
  | .seed => P4AOriginalSeed7Unequal15Literal.seed7Left
  | .nine i => P4AOriginalSeed7Unequal15Literal.nineLeft i
  | .fiftyA => P4AOriginalSeed7Unequal15Literal.fiftyAscLeft
  | .fiftyD => P4AOriginalSeed7Unequal15Literal.fiftyDescLeft
  | .h5 i => P4AOriginalFirstFailureH5H7Literal.h5LeftMasks i
  | .h7 i => P4AOriginalFirstFailureH5H7Literal.h7LeftMasks i
def winner : Cell → ℕ
  | .ascending _ | .seed => 6
  | .fiftyA | .fiftyD => 50
  | _ => 9
def branchMask (c : Cell) (k : Fin 62) : ℕ :=
  if k.val+1 < winner c then k.val+1 else k.val+2
def subsetSum (m : ℕ) (t : Point) : ℝ :=
  ∑ j : Fin 6, if decide (m / 2^j.val % 2 = 1) then t j.castSucc.castSucc else 0
def oldPlane (c : Cell) (m : ℕ) (t : Point) : ℝ :=
  if m ∈ leftMasks c then A (subsetSum m t) else C (subsetSum m t)

/-! Private syntax for the original affine slacks. The generic compiler and
its all-real evaluation theorem are imported, not reimplemented here. -/
open OriginalDescendingFifteenLiteralAffineRows
  (Expr K X coefficients evaluate evaluateCoefficients evaluate_coefficients
    oldExpr subsetExpr ascendingExpr descendingExpr)

/-! Notation-level evaluation adapters only: these unfold the already
proved compiler's existing Add/Sub/SMul instances and evaluator. -/
private theorem rem_eval_notation_add (a b : Expr) (t : Point) :
    evaluate (a + b) t = evaluate a t + evaluate b t := by rfl

private theorem rem_eval_notation_sub (a b : Expr) (t : Point) :
    evaluate (a - b) t = evaluate a t - evaluate b t := by rfl

private theorem rem_eval_notation_smul (q : ℚ) (a : Expr) (t : Point) :
    evaluate (q • a) t = (q : ℝ) * evaluate a t := by rfl

private theorem rem_eval_notation_ite (p : Prop) [Decidable p] (a b : Expr) (t : Point) :
    evaluate (if p then a else b) t = if p then evaluate a t else evaluate b t := by
  split_ifs <;> rfl

private def remSlotSumExpr (I : Finset (Fin 8)) : Expr :=
  (if (0 : Fin 8) ∈ I then X 0 else K 0) +
  (if (1 : Fin 8) ∈ I then X 1 else K 0) +
  (if (2 : Fin 8) ∈ I then X 2 else K 0) +
  (if (3 : Fin 8) ∈ I then X 3 else K 0) +
  (if (4 : Fin 8) ∈ I then X 4 else K 0) +
  (if (5 : Fin 8) ∈ I then X 5 else K 0) +
  (if (6 : Fin 8) ∈ I then X 6 else K 0) +
  (if (7 : Fin 8) ∈ I then X 7 else K 0)

private theorem rem_eval_slotSum (I : Finset (Fin 8)) (t : Point) :
    evaluate (remSlotSumExpr I) t = ∑ j ∈ I, t j := by
  have hI : Finset.univ.filter (fun j : Fin 8 => j ∈ I) = I := by
    ext j
    simp
  calc
    evaluate (remSlotSumExpr I) t = ∑ j : Fin 8, if j ∈ I then t j else 0 := by
      simp only [remSlotSumExpr, rem_eval_notation_add, rem_eval_notation_ite,
        evaluate, K, X, Fin.sum_univ_succ] <;> norm_num <;> first | rfl | ring1!
    _ = ∑ j ∈ Finset.univ.filter (fun j : Fin 8 => j ∈ I), t j := by
      rw [Finset.sum_filter]
    _ = ∑ j ∈ I, t j := by rw [hI]

private def remAExpr (e : Expr) : Expr := K (1 / 2) + (1 / 2 : ℚ) • e
private def remCExpr (e : Expr) : Expr := K (57 / 64) - (3 / 2 : ℚ) • e

private theorem rem_eval_A (e : Expr) (t : Point) :
    evaluate (remAExpr e) t = A (evaluate e t) := by
  norm_num only [remAExpr, rem_eval_notation_add, rem_eval_notation_smul,
    evaluate, K, A] <;> first | rfl | ring1!

private theorem rem_eval_C (e : Expr) (t : Point) :
    evaluate (remCExpr e) t = C (evaluate e t) := by
  norm_num only [remCExpr, rem_eval_notation_sub, rem_eval_notation_smul,
    evaluate, K, C] <;> first | rfl | ring1!

private theorem rem_eval_old (t : Point) :
    evaluate oldExpr t = C (t 1 + t 2) := by
  norm_num only [oldExpr, rem_eval_notation_add, rem_eval_notation_sub,
    rem_eval_notation_smul, evaluate, K, X, C] <;> first | rfl | ring1!

private theorem rem_castCoord (j : Fin 6) :
    j.castSucc.castSucc = Fin.ofNat 8 j.val := by
  apply Fin.ext
  change j.val = j.val % 8
  exact (Nat.mod_eq_of_lt (lt_trans j.isLt (by decide : 6 < 8))).symm

private theorem rem_subset_sum_canonical (m : ℕ) (t : Point) :
    subsetSum m t = ∑ j : Fin 6,
      if decide (m / 2 ^ j.val % 2 = 1) then t (Fin.ofNat 8 j.val) else 0 := by
  unfold subsetSum
  apply Finset.sum_congr rfl
  intro j _
  rw [rem_castCoord j]

private theorem rem_eval_subset (m : ℕ) (t : Point) :
    evaluate (subsetExpr m) t = subsetSum m t := by
  rw [rem_subset_sum_canonical]
  norm_num only [subsetExpr, rem_eval_notation_add, rem_eval_notation_ite,
    evaluate, K, X, Nat.testBit_eq_decide_div_mod_eq, Fin.sum_univ_succ,
    Fin.ofNat, Fin.succ] <;> first | rfl | ring1!

private theorem rem_eval_ascending (m : ℕ) (t : Point) :
    evaluate (ascendingExpr m) t = A (subsetSum m t) := by
  norm_num only [ascendingExpr, rem_eval_notation_add, rem_eval_notation_smul,
    evaluate, K, rem_eval_subset, A] <;> first | rfl | ring1!

private theorem rem_eval_descending (m : ℕ) (t : Point) :
    evaluate (descendingExpr m) t = C (subsetSum m t) := by
  norm_num only [descendingExpr, rem_eval_notation_sub, rem_eval_notation_smul,
    evaluate, K, rem_eval_subset, C] <;> first | rfl | ring1!

private def remComparisonExpr : Cell → Expr
  | .ascending _ | .seed => oldExpr
  | .fiftyA => ascendingExpr 50
  | .fiftyD => descendingExpr 50
  | _ => ascendingExpr 9

private def remMinorantExpr : Cell → Expr
  | .ascending _ | .seed | .nine _ => oldExpr
  | .fiftyA => ascendingExpr 6
  | _ => ascendingExpr 1

private theorem rem_eval_comparison (c : Cell) (t : Point) :
    evaluate (remComparisonExpr c) t = comparison c t := by
  cases c <;>
    norm_num only [remComparisonExpr, comparison, rem_eval_old, rem_eval_ascending,
      rem_eval_descending, rem_subset_sum_canonical, Fin.sum_univ_succ,
      Fin.ofNat, Fin.succ, A, C] <;> first | rfl | ring1!

private theorem rem_eval_minorant (c : Cell) (t : Point) :
    evaluate (remMinorantExpr c) t = minorant c t := by
  cases c <;>
    norm_num only [remMinorantExpr, minorant, rem_eval_old, rem_eval_ascending,
      rem_subset_sum_canonical, Fin.sum_univ_succ, Fin.ofNat, Fin.succ, A, C]
    <;> first | rfl | ring1!

private def remNewCapExpr (c : Cell) : Expr :=
  (if descendingNew c then remCExpr (remSlotSumExpr (selected c))
   else remAExpr (remSlotSumExpr (selected c))) - K (1 / 1000000)

private def remOtherPlaneExpr (c : Cell) : Expr :=
  if descendingNew c then remAExpr (remSlotSumExpr (selected c))
  else remCExpr (remSlotSumExpr (selected c))

private theorem rem_eval_newCap (c : Cell) (t : Point) :
    evaluate (remNewCapExpr c) t = newCap c t := by
  by_cases h : descendingNew c = true
  · norm_num only [remNewCapExpr, newCap, if_pos h, rem_eval_notation_sub,
      rem_eval_C, rem_eval_slotSum, selectedSum, evaluate, K, eta]
  · norm_num only [remNewCapExpr, newCap, if_neg h, rem_eval_notation_sub,
      rem_eval_A, rem_eval_slotSum, selectedSum, evaluate, K, eta]

private theorem rem_eval_otherPlane (c : Cell) (t : Point) :
    evaluate (remOtherPlaneExpr c) t = otherPlane c (selectedSum c t) := by
  by_cases h : descendingNew c = true
  · simp only [remOtherPlaneExpr, otherPlane, if_pos h, rem_eval_A,
      rem_eval_slotSum, selectedSum]
  · simp only [remOtherPlaneExpr, otherPlane, if_neg h, rem_eval_C,
      rem_eval_slotSum, selectedSum]

private def remHistoryExpr : Fin 4 → Expr :=
  ![(3 : ℚ) • X 0, X 0 + X 1 + (3 : ℚ) • X 2,
    X 0 + X 1 + X 2 + X 3 + (3 : ℚ) • X 4,
    X 0 + X 1 + X 2 + X 3 + X 4 + X 5 + (3 : ℚ) • X 6]

private theorem rem_eval_history (j : Fin 4) (t : Point) :
    evaluate (remHistoryExpr j) t = history t j := by
  fin_cases j <;>
    norm_num only [remHistoryExpr, history, rem_eval_notation_add,
      rem_eval_notation_smul, evaluate, X] <;> first | rfl | ring1!

private def remPrefixSquareExpr (j : Fin 8) : Expr :=
  remSlotSumExpr (Finset.univ.filter (fun k : Fin 8 => k < j)) + (2 : ℚ) • X j

private def remSelectedSquareExpr (I : Finset (Fin 8)) (j : Fin 8) : Expr :=
  remSlotSumExpr I + remSlotSumExpr (Finset.univ.filter (fun k : Fin 8 => k < j ∧ k ∉ I)) +
    (2 : ℚ) • X j

private theorem rem_eval_prefixSquare (j : Fin 8) (t : Point) :
    evaluate (remPrefixSquareExpr j) t = prefixSquareExpr t j := by
  norm_num only [remPrefixSquareExpr, prefixSquareExpr, rem_eval_notation_add,
    rem_eval_notation_smul, evaluate, X, rem_eval_slotSum] <;> first | rfl | ring1!

private theorem rem_eval_selectedSquare (I : Finset (Fin 8)) (j : Fin 8) (t : Point) :
    evaluate (remSelectedSquareExpr I j) t = selectedSquareExpr I t j := by
  norm_num only [remSelectedSquareExpr, selectedSquareExpr, rem_eval_notation_add,
    rem_eval_notation_smul, evaluate, X, rem_eval_slotSum] <;> first | rfl | ring1!

private def remSideExpr : Cell → Expr
  | .ascending _ | .seed | .nine _ => (2 : ℚ) • (X 1 + X 2 - K (25 / 128))
  | .fiftyA => (2 : ℚ) • (K (25 / 128) - X 1 - X 2)
  | _ => K (25 / 128) - X 0

private theorem rem_eval_side (c : Cell) (t : Point) :
    evaluate (remSideExpr c) t = sideSlack c t := by
  cases c <;>
    norm_num only [remSideExpr, sideSlack, rem_eval_notation_add, rem_eval_notation_sub,
      rem_eval_notation_smul, evaluate, K, X, mu] <;> first | rfl | ring1!

private def remCommonExpr (c : Cell) : Fin 35 → Expr :=
  ![K (25 / 128) - X 0, X 2 - K (1 / 100), X 7 - K (53 / 13824),
    X 0 - X 1, X 1 - X 2, X 2 - X 3, X 3 - X 4, X 4 - X 5, X 5 - X 6, X 6 - X 7,
    remMinorantExpr c - remHistoryExpr 0, remMinorantExpr c - remHistoryExpr 1,
    remMinorantExpr c - remHistoryExpr 2, remMinorantExpr c - remHistoryExpr 3,
    remComparisonExpr c - (K (153 / 256) - (3 / 8 : ℚ) • X 2),
    remNewCapExpr c - remComparisonExpr c,
    remSlotSumExpr Finset.univ + (3 : ℚ) • X 7 - remNewCapExpr c,
    remOtherPlaneExpr c - K (1 / 1000000) - remNewCapExpr c,
    remNewCapExpr c - remPrefixSquareExpr 0, remNewCapExpr c - remPrefixSquareExpr 1,
    remNewCapExpr c - remPrefixSquareExpr 2, remNewCapExpr c - remPrefixSquareExpr 3,
    remNewCapExpr c - remPrefixSquareExpr 4, remNewCapExpr c - remPrefixSquareExpr 5,
    remNewCapExpr c - remPrefixSquareExpr 6, remNewCapExpr c - remPrefixSquareExpr 7,
    if 0 ∈ selected c then K (25 / 128) - X 0
      else remNewCapExpr c - remSelectedSquareExpr (selected c) 0,
    if 1 ∈ selected c then K (25 / 128) - X 0
      else remNewCapExpr c - remSelectedSquareExpr (selected c) 1,
    if 2 ∈ selected c then K (25 / 128) - X 0
      else remNewCapExpr c - remSelectedSquareExpr (selected c) 2,
    if 3 ∈ selected c then K (25 / 128) - X 0
      else remNewCapExpr c - remSelectedSquareExpr (selected c) 3,
    if 4 ∈ selected c then K (25 / 128) - X 0
      else remNewCapExpr c - remSelectedSquareExpr (selected c) 4,
    if 5 ∈ selected c then K (25 / 128) - X 0
      else remNewCapExpr c - remSelectedSquareExpr (selected c) 5,
    if 6 ∈ selected c then K (25 / 128) - X 0
      else remNewCapExpr c - remSelectedSquareExpr (selected c) 6,
    if 7 ∈ selected c then K (25 / 128) - X 0
      else remNewCapExpr c - remSelectedSquareExpr (selected c) 7,
    remSideExpr c]

private theorem rem_eval_common (c : Cell) (k : Fin 35) (t : Point) :
    evaluate (remCommonExpr c k) t = commonSlack c t k := by
  fin_cases k <;>
    norm_num only [remCommonExpr, commonSlack, rem_eval_notation_add, rem_eval_notation_sub,
      rem_eval_notation_smul, rem_eval_notation_ite, evaluate, K, X,
      rem_eval_minorant, rem_eval_history, rem_eval_comparison, rem_eval_newCap,
      rem_eval_otherPlane, rem_eval_slotSum, rem_eval_prefixSquare,
      rem_eval_selectedSquare, rem_eval_side, VariableEnvelope.B, cap, mu, eta, total]
    <;> first | rfl | ring1!

private def remBranchExpr (c : Cell) (m : ℕ) : Expr :=
  remComparisonExpr c -
    (if m ∈ leftMasks c then ascendingExpr m else descendingExpr m)

private theorem rem_eval_branch (c : Cell) (m : ℕ) (t : Point) :
    evaluate (remBranchExpr c m) t = comparison c t - oldPlane c m t := by
  by_cases h : m ∈ leftMasks c
  · simp only [remBranchExpr, oldPlane, if_pos h, rem_eval_notation_sub,
      rem_eval_comparison, rem_eval_ascending]
  · simp only [remBranchExpr, oldPlane, if_neg h, rem_eval_notation_sub,
      rem_eval_comparison, rem_eval_descending]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem rem_common_coeff_ascending :
    ∀ (i : Fin 14) (k : Fin 35) (j : Fin 9),
      row (Cell.ascending i) (commonRow (Cell.ascending i) k) j = coefficients (remCommonExpr (Cell.ascending i) k) j := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem rem_common_coeff_seed :
    ∀ (k : Fin 35) (j : Fin 9),
      row Cell.seed (commonRow Cell.seed k) j = coefficients (remCommonExpr Cell.seed k) j := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem rem_common_coeff_nine :
    ∀ (i : Fin 13) (k : Fin 35) (j : Fin 9),
      row (Cell.nine i) (commonRow (Cell.nine i) k) j = coefficients (remCommonExpr (Cell.nine i) k) j := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem rem_common_coeff_fiftyA :
    ∀ (k : Fin 35) (j : Fin 9),
      row Cell.fiftyA (commonRow Cell.fiftyA k) j = coefficients (remCommonExpr Cell.fiftyA k) j := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem rem_common_coeff_fiftyD :
    ∀ (k : Fin 35) (j : Fin 9),
      row Cell.fiftyD (commonRow Cell.fiftyD k) j = coefficients (remCommonExpr Cell.fiftyD k) j := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem rem_common_coeff_h5 :
    ∀ (i : Fin 7) (k : Fin 35) (j : Fin 9),
      row (Cell.h5 i) (commonRow (Cell.h5 i) k) j = coefficients (remCommonExpr (Cell.h5 i) k) j := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem rem_common_coeff_h7 :
    ∀ (i : Fin 10) (k : Fin 35) (j : Fin 9),
      row (Cell.h7 i) (commonRow (Cell.h7 i) k) j = coefficients (remCommonExpr (Cell.h7 i) k) j := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem rem_branch_coeff_ascending :
    ∀ (i : Fin 14) (k : Fin 62) (j : Fin 9),
      row (Cell.ascending i) (branchRow (Cell.ascending i) k) j = coefficients (remBranchExpr (Cell.ascending i) (branchMask (Cell.ascending i) k)) j := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem rem_branch_coeff_seed :
    ∀ (k : Fin 62) (j : Fin 9),
      row Cell.seed (branchRow Cell.seed k) j = coefficients (remBranchExpr Cell.seed (branchMask Cell.seed k)) j := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem rem_branch_coeff_nine :
    ∀ (i : Fin 13) (k : Fin 62) (j : Fin 9),
      row (Cell.nine i) (branchRow (Cell.nine i) k) j = coefficients (remBranchExpr (Cell.nine i) (branchMask (Cell.nine i) k)) j := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem rem_branch_coeff_fiftyA :
    ∀ (k : Fin 62) (j : Fin 9),
      row Cell.fiftyA (branchRow Cell.fiftyA k) j = coefficients (remBranchExpr Cell.fiftyA (branchMask Cell.fiftyA k)) j := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem rem_branch_coeff_fiftyD :
    ∀ (k : Fin 62) (j : Fin 9),
      row Cell.fiftyD (branchRow Cell.fiftyD k) j = coefficients (remBranchExpr Cell.fiftyD (branchMask Cell.fiftyD k)) j := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem rem_branch_coeff_h5 :
    ∀ (i : Fin 7) (k : Fin 62) (j : Fin 9),
      row (Cell.h5 i) (branchRow (Cell.h5 i) k) j = coefficients (remBranchExpr (Cell.h5 i) (branchMask (Cell.h5 i) k)) j := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem rem_branch_coeff_h7 :
    ∀ (i : Fin 10) (k : Fin 62) (j : Fin 9),
      row (Cell.h7 i) (branchRow (Cell.h7 i) k) j = coefficients (remBranchExpr (Cell.h7 i) (branchMask (Cell.h7 i) k)) j := by
  decide +kernel

private theorem rem_common_coefficients (c : Cell) (k : Fin 35) (j : Fin 9) :
    row c (commonRow c k) j = coefficients (remCommonExpr c k) j := by
  cases c with
  | ascending i => exact rem_common_coeff_ascending i k j
  | seed => exact rem_common_coeff_seed k j
  | nine i => exact rem_common_coeff_nine i k j
  | fiftyA => exact rem_common_coeff_fiftyA k j
  | fiftyD => exact rem_common_coeff_fiftyD k j
  | h5 i => exact rem_common_coeff_h5 i k j
  | h7 i => exact rem_common_coeff_h7 i k j

private theorem rem_branch_coefficients (c : Cell) (k : Fin 62) (j : Fin 9) :
    row c (branchRow c k) j = coefficients (remBranchExpr c (branchMask c k)) j := by
  cases c with
  | ascending i => exact rem_branch_coeff_ascending i k j
  | seed => exact rem_branch_coeff_seed k j
  | nine i => exact rem_branch_coeff_nine i k j
  | fiftyA => exact rem_branch_coeff_fiftyA k j
  | fiftyD => exact rem_branch_coeff_fiftyD k j
  | h5 i => exact rem_branch_coeff_h5 i k j
  | h7 i => exact rem_branch_coeff_h7 i k j

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem source_common_row (c : Cell) (k : Fin 35) (t : Point) :
    evalRow (row c (commonRow c k)) t = commonSlack c t k := by
  have hcoeff : row c (commonRow c k) = coefficients (remCommonExpr c k) :=
    funext (rem_common_coefficients c k)
  change evaluateCoefficients (row c (commonRow c k)) t = commonSlack c t k
  rw [hcoeff, evaluate_coefficients]
  exact rem_eval_common c k t

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem source_branch_row (c : Cell) (k : Fin 62) (t : Point) :
    evalRow (row c (branchRow c k)) t = comparison c t-oldPlane c (branchMask c k) t := by
  have hcoeff : row c (branchRow c k) = coefficients (remBranchExpr c (branchMask c k)) :=
    funext (rem_branch_coefficients c k)
  change evaluateCoefficients (row c (branchRow c k)) t =
    comparison c t - oldPlane c (branchMask c k) t
  rw [hcoeff, evaluate_coefficients]
  exact rem_eval_branch c (branchMask c k) t

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem winner_plane (c : Cell) (t : Point) :
    oldPlane c (winner c) t = comparison c t := by
  cases c with
  | ascending i =>
    fin_cases i <;>
    norm_num [row, commonRow, branchRow, branchMask, rowCount, evalRow, commonSlack,
      comparison, minorant, newCap, selected, selectedSum, otherPlane, descendingNew,
      sideSlack, history, total, eta, oldPlane, leftMasks, winner, subsetSum,
      prefixSquareExpr, selectedSquareExpr, A, C, VariableEnvelope.B, mu, cap,
      Fin.sum_univ_succ, Finset.sum_filter,
      P4AOriginalAscendingFourteenAffineSource.rows,
      P4AOriginalAscendingFourteenAffineSource.literalPool,
      P4AOriginalAscendingFourteenAffineSource.literalIndex,
      P4AOriginalAscendingFourteenAffineSource.leftMasks,
      P4AOriginalSeed7Unequal15Literal.seed7Rows,
      P4AOriginalSeed7Unequal15Literal.nineRows,
      P4AOriginalSeed7Unequal15Literal.fiftyAscRows,
      P4AOriginalSeed7Unequal15Literal.fiftyDescRows,
      P4AOriginalSeed7Unequal15Literal.seed7Left,
      P4AOriginalSeed7Unequal15Literal.nineLeft,
      P4AOriginalSeed7Unequal15Literal.fiftyAscLeft,
      P4AOriginalSeed7Unequal15Literal.fiftyDescLeft,
      P4AOriginalFirstFailureH5H7Literal.h5AffineRows,
      P4AOriginalFirstFailureH5H7Literal.h7AffineRows,
      P4AOriginalFirstFailureH5H7Literal.h5LeftMasks,
      P4AOriginalFirstFailureH5H7Literal.h7LeftMasks] <;>
    first | rfl | ring1!
  | seed =>
    norm_num [row, commonRow, branchRow, branchMask, rowCount, evalRow, commonSlack,
      comparison, minorant, newCap, selected, selectedSum, otherPlane, descendingNew,
      sideSlack, history, total, eta, oldPlane, leftMasks, winner, subsetSum,
      prefixSquareExpr, selectedSquareExpr, A, C, VariableEnvelope.B, mu, cap,
      Fin.sum_univ_succ, Finset.sum_filter,
      P4AOriginalAscendingFourteenAffineSource.rows,
      P4AOriginalAscendingFourteenAffineSource.literalPool,
      P4AOriginalAscendingFourteenAffineSource.literalIndex,
      P4AOriginalAscendingFourteenAffineSource.leftMasks,
      P4AOriginalSeed7Unequal15Literal.seed7Rows,
      P4AOriginalSeed7Unequal15Literal.nineRows,
      P4AOriginalSeed7Unequal15Literal.fiftyAscRows,
      P4AOriginalSeed7Unequal15Literal.fiftyDescRows,
      P4AOriginalSeed7Unequal15Literal.seed7Left,
      P4AOriginalSeed7Unequal15Literal.nineLeft,
      P4AOriginalSeed7Unequal15Literal.fiftyAscLeft,
      P4AOriginalSeed7Unequal15Literal.fiftyDescLeft,
      P4AOriginalFirstFailureH5H7Literal.h5AffineRows,
      P4AOriginalFirstFailureH5H7Literal.h7AffineRows,
      P4AOriginalFirstFailureH5H7Literal.h5LeftMasks,
      P4AOriginalFirstFailureH5H7Literal.h7LeftMasks] <;>
    first | rfl | ring1!
  | nine i =>
    fin_cases i <;>
    norm_num [row, commonRow, branchRow, branchMask, rowCount, evalRow, commonSlack,
      comparison, minorant, newCap, selected, selectedSum, otherPlane, descendingNew,
      sideSlack, history, total, eta, oldPlane, leftMasks, winner, subsetSum,
      prefixSquareExpr, selectedSquareExpr, A, C, VariableEnvelope.B, mu, cap,
      Fin.sum_univ_succ, Finset.sum_filter,
      P4AOriginalAscendingFourteenAffineSource.rows,
      P4AOriginalAscendingFourteenAffineSource.literalPool,
      P4AOriginalAscendingFourteenAffineSource.literalIndex,
      P4AOriginalAscendingFourteenAffineSource.leftMasks,
      P4AOriginalSeed7Unequal15Literal.seed7Rows,
      P4AOriginalSeed7Unequal15Literal.nineRows,
      P4AOriginalSeed7Unequal15Literal.fiftyAscRows,
      P4AOriginalSeed7Unequal15Literal.fiftyDescRows,
      P4AOriginalSeed7Unequal15Literal.seed7Left,
      P4AOriginalSeed7Unequal15Literal.nineLeft,
      P4AOriginalSeed7Unequal15Literal.fiftyAscLeft,
      P4AOriginalSeed7Unequal15Literal.fiftyDescLeft,
      P4AOriginalFirstFailureH5H7Literal.h5AffineRows,
      P4AOriginalFirstFailureH5H7Literal.h7AffineRows,
      P4AOriginalFirstFailureH5H7Literal.h5LeftMasks,
      P4AOriginalFirstFailureH5H7Literal.h7LeftMasks] <;>
    first | rfl | ring1!
  | fiftyA =>
    norm_num [row, commonRow, branchRow, branchMask, rowCount, evalRow, commonSlack,
      comparison, minorant, newCap, selected, selectedSum, otherPlane, descendingNew,
      sideSlack, history, total, eta, oldPlane, leftMasks, winner, subsetSum,
      prefixSquareExpr, selectedSquareExpr, A, C, VariableEnvelope.B, mu, cap,
      Fin.sum_univ_succ, Finset.sum_filter,
      P4AOriginalAscendingFourteenAffineSource.rows,
      P4AOriginalAscendingFourteenAffineSource.literalPool,
      P4AOriginalAscendingFourteenAffineSource.literalIndex,
      P4AOriginalAscendingFourteenAffineSource.leftMasks,
      P4AOriginalSeed7Unequal15Literal.seed7Rows,
      P4AOriginalSeed7Unequal15Literal.nineRows,
      P4AOriginalSeed7Unequal15Literal.fiftyAscRows,
      P4AOriginalSeed7Unequal15Literal.fiftyDescRows,
      P4AOriginalSeed7Unequal15Literal.seed7Left,
      P4AOriginalSeed7Unequal15Literal.nineLeft,
      P4AOriginalSeed7Unequal15Literal.fiftyAscLeft,
      P4AOriginalSeed7Unequal15Literal.fiftyDescLeft,
      P4AOriginalFirstFailureH5H7Literal.h5AffineRows,
      P4AOriginalFirstFailureH5H7Literal.h7AffineRows,
      P4AOriginalFirstFailureH5H7Literal.h5LeftMasks,
      P4AOriginalFirstFailureH5H7Literal.h7LeftMasks] <;>
    first | rfl | ring1!
  | fiftyD =>
    norm_num [row, commonRow, branchRow, branchMask, rowCount, evalRow, commonSlack,
      comparison, minorant, newCap, selected, selectedSum, otherPlane, descendingNew,
      sideSlack, history, total, eta, oldPlane, leftMasks, winner, subsetSum,
      prefixSquareExpr, selectedSquareExpr, A, C, VariableEnvelope.B, mu, cap,
      Fin.sum_univ_succ, Finset.sum_filter,
      P4AOriginalAscendingFourteenAffineSource.rows,
      P4AOriginalAscendingFourteenAffineSource.literalPool,
      P4AOriginalAscendingFourteenAffineSource.literalIndex,
      P4AOriginalAscendingFourteenAffineSource.leftMasks,
      P4AOriginalSeed7Unequal15Literal.seed7Rows,
      P4AOriginalSeed7Unequal15Literal.nineRows,
      P4AOriginalSeed7Unequal15Literal.fiftyAscRows,
      P4AOriginalSeed7Unequal15Literal.fiftyDescRows,
      P4AOriginalSeed7Unequal15Literal.seed7Left,
      P4AOriginalSeed7Unequal15Literal.nineLeft,
      P4AOriginalSeed7Unequal15Literal.fiftyAscLeft,
      P4AOriginalSeed7Unequal15Literal.fiftyDescLeft,
      P4AOriginalFirstFailureH5H7Literal.h5AffineRows,
      P4AOriginalFirstFailureH5H7Literal.h7AffineRows,
      P4AOriginalFirstFailureH5H7Literal.h5LeftMasks,
      P4AOriginalFirstFailureH5H7Literal.h7LeftMasks] <;>
    first | rfl | ring1!
  | h5 i =>
    fin_cases i <;>
    norm_num [row, commonRow, branchRow, branchMask, rowCount, evalRow, commonSlack,
      comparison, minorant, newCap, selected, selectedSum, otherPlane, descendingNew,
      sideSlack, history, total, eta, oldPlane, leftMasks, winner, subsetSum,
      prefixSquareExpr, selectedSquareExpr, A, C, VariableEnvelope.B, mu, cap,
      Fin.sum_univ_succ, Finset.sum_filter,
      P4AOriginalAscendingFourteenAffineSource.rows,
      P4AOriginalAscendingFourteenAffineSource.literalPool,
      P4AOriginalAscendingFourteenAffineSource.literalIndex,
      P4AOriginalAscendingFourteenAffineSource.leftMasks,
      P4AOriginalSeed7Unequal15Literal.seed7Rows,
      P4AOriginalSeed7Unequal15Literal.nineRows,
      P4AOriginalSeed7Unequal15Literal.fiftyAscRows,
      P4AOriginalSeed7Unequal15Literal.fiftyDescRows,
      P4AOriginalSeed7Unequal15Literal.seed7Left,
      P4AOriginalSeed7Unequal15Literal.nineLeft,
      P4AOriginalSeed7Unequal15Literal.fiftyAscLeft,
      P4AOriginalSeed7Unequal15Literal.fiftyDescLeft,
      P4AOriginalFirstFailureH5H7Literal.h5AffineRows,
      P4AOriginalFirstFailureH5H7Literal.h7AffineRows,
      P4AOriginalFirstFailureH5H7Literal.h5LeftMasks,
      P4AOriginalFirstFailureH5H7Literal.h7LeftMasks] <;>
    first | rfl | ring1!
  | h7 i =>
    fin_cases i <;>
    norm_num [row, commonRow, branchRow, branchMask, rowCount, evalRow, commonSlack,
      comparison, minorant, newCap, selected, selectedSum, otherPlane, descendingNew,
      sideSlack, history, total, eta, oldPlane, leftMasks, winner, subsetSum,
      prefixSquareExpr, selectedSquareExpr, A, C, VariableEnvelope.B, mu, cap,
      Fin.sum_univ_succ, Finset.sum_filter,
      P4AOriginalAscendingFourteenAffineSource.rows,
      P4AOriginalAscendingFourteenAffineSource.literalPool,
      P4AOriginalAscendingFourteenAffineSource.literalIndex,
      P4AOriginalAscendingFourteenAffineSource.leftMasks,
      P4AOriginalSeed7Unequal15Literal.seed7Rows,
      P4AOriginalSeed7Unequal15Literal.nineRows,
      P4AOriginalSeed7Unequal15Literal.fiftyAscRows,
      P4AOriginalSeed7Unequal15Literal.fiftyDescRows,
      P4AOriginalSeed7Unequal15Literal.seed7Left,
      P4AOriginalSeed7Unequal15Literal.nineLeft,
      P4AOriginalSeed7Unequal15Literal.fiftyAscLeft,
      P4AOriginalSeed7Unequal15Literal.fiftyDescLeft,
      P4AOriginalFirstFailureH5H7Literal.h5AffineRows,
      P4AOriginalFirstFailureH5H7Literal.h7AffineRows,
      P4AOriginalFirstFailureH5H7Literal.h5LeftMasks,
      P4AOriginalFirstFailureH5H7Literal.h7LeftMasks] <;>
    first | rfl | ring1!

-- END_GENERATED_ROW_IDENTITIES

theorem source_common_pos {c : Cell} {t : Point} (h : Source c t) (k : Fin 35) :
    0 < commonSlack c t k := by
  rw [← source_common_row]
  exact h (commonRow c k)

theorem branchMask_covers (c : Cell) (m : ℕ) (hm : m ∈ Finset.Icc 1 63)
    (hw : m ≠ winner c) : ∃ k : Fin 62, branchMask c k = m := by
  have hwlo : 1 < winner c := by
    cases c <;> norm_num [winner]
  have hwhi : winner c ≤ 63 := by
    cases c <;> norm_num [winner]
  obtain ⟨hm0, hm63⟩ := Finset.mem_Icc.mp hm
  by_cases hlt : m < winner c
  · refine ⟨⟨m - 1, by omega⟩, ?_⟩
    change (if (m - 1) + 1 < winner c then (m - 1) + 1 else (m - 1) + 2) = m
    have hif : (m - 1) + 1 < winner c := by omega
    rw [if_pos hif]
    omega
  · refine ⟨⟨m - 2, by omega⟩, ?_⟩
    change (if (m - 2) + 1 < winner c then (m - 2) + 1 else (m - 2) + 2) = m
    have hif : ¬ ((m - 2) + 1 < winner c) := by omega
    rw [if_neg hif]
    omega
theorem source_all_old_tents {c : Cell} {t : Point} (h : Source c t)
    (m : ℕ) (hm : m ∈ Finset.Icc 1 63) :
    v (subsetSum m t) ≤ comparison c t := by
  have hp : oldPlane c m t ≤ comparison c t := by
    by_cases hw : m = winner c
    · simpa only [hw,winner_plane] using (le_refl (comparison c t))
    · obtain ⟨k,hk⟩ := branchMask_covers c m hm hw
      have hb := h (branchRow c k)
      rw [source_branch_row,hk] at hb
      exact (sub_pos.mp hb).le
  rw [v_eq_min]
  unfold oldPlane at hp
  split_ifs at hp with hl
  · exact (min_le_left _ _).trans hp
  · exact (min_le_right _ _).trans hp

theorem source_basic {c : Cell} {t : Point} (h : Source c t) :
    t 0 < mu ∧ (1/100 : ℝ) < t 2 ∧ (53/13824 : ℝ) < t 7 ∧
    (∀ j : Fin 7, t j.succ < t j.castSucc) ∧
    (∀ j : Fin 4, history t j < minorant c t) ∧
    VariableEnvelope.B (t 2) < comparison c t ∧ comparison c t < newCap c t ∧
    newCap c t < total t+3*t 7 := by
  have hp := source_common_pos h
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [commonSlack] using sub_pos.mp (hp 0)
  · simpa [commonSlack] using sub_pos.mp (hp 1)
  · simpa [commonSlack] using sub_pos.mp (hp 2)
  · intro j
    have hh := hp (⟨3+j.val, by omega⟩ : Fin 35)
    have hid : commonSlack c t ⟨3+j.val, by omega⟩ = t j.castSucc-t j.succ := by
      fin_cases j <;> simp [commonSlack]
    rw [hid] at hh
    exact sub_pos.mp hh
  · intro j
    have hh := hp (⟨10+j.val, by omega⟩ : Fin 35)
    have hid : commonSlack c t ⟨10+j.val, by omega⟩ = minorant c t-history t j := by
      fin_cases j <;> simp [commonSlack]
    rw [hid] at hh
    exact sub_pos.mp hh
  · simpa [commonSlack] using sub_pos.mp (hp 14)
  · simpa [commonSlack] using sub_pos.mp (hp 15)
  · simpa [commonSlack] using sub_pos.mp (hp 16)

theorem source_full_selected {c : Cell} {t : Point} (h : Source c t) :
    (∀ j, prefixSquareExpr t j < newCap c t) ∧
    (∀ j ∉ selected c, selectedSquareExpr (selected c) t j < newCap c t) := by
  have hp := source_common_pos h
  constructor
  · intro j
    have hh := hp (⟨18+j.val, by omega⟩ : Fin 35)
    have hid : commonSlack c t ⟨18+j.val, by omega⟩ =
        newCap c t-prefixSquareExpr t j := by fin_cases j <;> simp [commonSlack]
    rw [hid] at hh
    exact sub_pos.mp hh
  · intro j hj
    have hh := hp (⟨26+j.val, by omega⟩ : Fin 35)
    have hid : commonSlack c t ⟨26+j.val, by omega⟩ =
        if j ∈ selected c then mu-t 0
        else newCap c t-selectedSquareExpr (selected c) t j := by
      fin_cases j <;> simp [commonSlack]
    rw [hid,if_neg hj] at hh
    exact sub_pos.mp hh

theorem source_selected_license {c : Cell} {t : Point} (h : Source c t) :
    newCap c t < v (selectedSum c t) := by
  have hp := source_common_pos h 17
  have he : 0 < eta := by norm_num [eta]
  rw [v_eq_min]
  dsimp [commonSlack,otherPlane] at hp
  unfold newCap at hp ⊢
  by_cases hd : descendingNew c = true
  · simp only [if_pos hd] at hp ⊢
    exact lt_min (by linarith) (by linarith)
  · simp only [if_neg hd] at hp ⊢
    exact lt_min (by linarith) (by linarith)

theorem source_newCap_eq_tent_buffer {c : Cell} {t : Point} (h : Source c t) :
    newCap c t = v (selectedSum c t)-eta := by
  have hp := source_common_pos h 17
  dsimp [commonSlack,otherPlane] at hp
  unfold newCap at hp ⊢
  rw [v_eq_min]
  by_cases hd : descendingNew c = true
  · simp only [if_pos hd] at hp ⊢
    rw [min_eq_right (by linarith)]
  · simp only [if_neg hd] at hp ⊢
    rw [min_eq_left (by linarith)]

theorem source_minorant_active {c : Cell} {t : Point} (h : Source c t) :
    minorant c t = v (t 0) ∨ minorant c t = v (t 1+t 2) := by
  have hs := source_common_pos h 34
  have hx := (source_basic h).1
  cases c with
  | ascending i =>
      right
      change C (t 1+t 2) = v (t 1+t 2)
      exact (v_eq_C (by dsimp [commonSlack,sideSlack] at hs; linarith)).symm
  | seed =>
      right
      change C (t 1+t 2) = v (t 1+t 2)
      exact (v_eq_C (by dsimp [commonSlack,sideSlack] at hs; linarith)).symm
  | nine i =>
      right
      change C (t 1+t 2) = v (t 1+t 2)
      exact (v_eq_C (by dsimp [commonSlack,sideSlack] at hs; linarith)).symm
  | fiftyA =>
      right
      change A (t 1+t 2) = v (t 1+t 2)
      exact (v_eq_A (by dsimp [commonSlack,sideSlack] at hs; linarith)).symm
  | fiftyD => exact Or.inl (v_eq_A hx.le).symm
  | h5 i => exact Or.inl (v_eq_A hx.le).symm
  | h7 i => exact Or.inl (v_eq_A hx.le).symm

theorem source_ordered {c : Cell} {t : Point} (h : Source c t) :
    Ordered (t 0) (t 1) (t 2) := by
  obtain ⟨hx,hz,_hr,ho,_⟩ := source_basic h
  exact ⟨by linarith, (ho 1).le, (ho 0).le, hx.le⟩

theorem source_minorant_le_original_ideal {c : Cell} {t : Point} (h : Source c t) :
    minorant c t ≤ actualExtendedThirdIdealCap (t 0) (t 1) (t 2) := by
  have ho := source_ordered h
  rw [actualExtendedThirdIdealCap_eq,if_pos ho.2.2.2,original_eq_six ho]
  have hb := source_minorant_active h
  apply le_min
  · have hv : minorant c t ≤ cap := by
      rcases hb with hb | hb <;> rw [hb] <;> exact v_le_cap _
    have hc : cap < thirdPrefixTheta := by norm_num [cap,thirdPrefixTheta]
    exact hv.trans hc.le
  · unfold six
    rcases hb with hb | hb
    · rw [hb]; exact le_max_left _ _
    · rw [hb]
      exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_of_le_right (le_max_right _ _))))

theorem source_histories_original_ideal {c : Cell} {t : Point} (h : Source c t) :
    ∀ j : Fin 4, history t j < actualExtendedThirdIdealCap (t 0) (t 1) (t 2) := by
  intro j
  exact ((source_basic h).2.2.2.2.1 j).trans_le (source_minorant_le_original_ideal h)

theorem source_original_ideal_le_comparison {c : Cell} {t : Point} (h : Source c t) :
    actualExtendedThirdIdealCap (t 0) (t 1) (t 2) ≤ comparison c t := by
  have ho := source_ordered h
  have h1 := source_all_old_tents h 1 (by decide)
  have h3 := source_all_old_tents h 3 (by decide)
  have h5 := source_all_old_tents h 5 (by decide)
  have h6 := source_all_old_tents h 6 (by decide)
  have h7 := source_all_old_tents h 7 (by decide)
  norm_num [subsetSum,Fin.sum_univ_succ,add_assoc] at h1 h3 h5 h6 h7
  have hw := (source_basic h).2.2.2.2.2.1
  rw [actualExtendedThirdIdealCap_eq,if_pos ho.2.2.2,original_eq_six ho]
  apply (min_le_right _ _).trans
  unfold six
  simpa only [add_assoc] using
    max_le h1 (max_le h3 (max_le h7 (max_le hw.le (max_le h5 h6))))

theorem source_physical_ceiling {c : Cell} {t : Point} (h : Source c t) :
    newCap c t < (153/256 : ℝ) :=
  (source_selected_license h).trans_le (v_le_cap _)

theorem source_integer_squares {c : Cell} {t : Point} (h : Source c t)
    (N : ℝ) (hN : 1 < N) (p : Fin 8 → ℕ)
    (hp : ∀ j, (p j : ℝ) ≤ N^t j) :
    (∀ j, ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j), p k : ℕ) : ℝ) *
      (p j : ℝ)^2 < N^newCap c t) ∧
    (∀ j ∉ selected c, ((∏ k ∈ selected c, p k : ℕ) : ℝ) *
      ((∏ k ∈ Finset.univ.filter (fun k : Fin 8 => k < j ∧ k ∉ selected c), p k : ℕ) : ℝ) *
      (p j : ℝ)^2 < N^newCap c t) := by
  obtain ⟨hf,hs⟩ := source_full_selected h
  exact ⟨fun j => prefixSquareExpr_actual_gate N hN p t hp j (hf j),
    fun j hj => selectedSquareExpr_actual_gate (selected c) N hN p t hp j (hs j hj)⟩

end
end ImbalancedChen.P4AOriginalRemainingEighthSources
