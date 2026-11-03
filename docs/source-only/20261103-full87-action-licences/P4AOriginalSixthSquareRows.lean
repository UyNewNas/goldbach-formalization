import ImbalancedChen.P1QuantizedActionLicense
import ImbalancedChen.P4AOriginalCompleteSixthChronology

/-!
SOURCE ONLY / UNCOMPILED / FINITE ROW CERTIFICATES UNEVALUATED.

The nineteen later actions previously had an upper-tent source theorem.
Here the missing FULL and NONSELECTED square rows are read from the SAME
original literal lists. Coordinate-chart pullback is explicit. No original
row array is copied, edited or replaced, and no new square licence is an
input of the source theorem. Finite coefficient identities still need Lean
elaboration and kernel checking; this file claims no numerical saving.
-/
namespace ImbalancedChen.P4AOriginalSixthSquareRows
noncomputable section
open scoped Classical BigOperators
open P1QuantizedActionLicense
open P4AOriginalSixthLaterLiteral (Cell Affine Point mapped mask descending rows)
open P4AOriginalSixthLaterSemantics (eval coordinates endpoint Source comparison selectedSum)
open Certificates.P2OriginalSixthElevenLogSemantics
  (bit eta fullSquare remainingSquare chart R0 S5 H5 descending33 ascending34)

/-- Original bit convention, unchanged at all stages. -/
def slots (m : ℕ) : Finset (Fin 6) := Finset.univ.filter fun i => bit m i.val

theorem sum_slots (m : ℕ) (t : Fin 6 → ℝ) :
    (∑ i ∈ slots m, t i) = Certificates.P2OriginalSixthElevenLogSemantics.selectedSum m t := by
  simp only [slots, Finset.sum_filter, Certificates.P2OriginalSixthElevenLogSemantics.selectedSum]

theorem full_dictionary (t : Fin 6 → ℝ) (j : Fin 6) :
    prefixSquareExpr t j = fullSquare j t := by
  simp only [prefixSquareExpr, Finset.sum_filter, fullSquare]

theorem not_mem_slots (m : ℕ) (j : Fin 6) :
    j ∉ slots m ↔ bit m j.val = false := by simp [slots]


theorem remaining_dictionary (m : ℕ) (t : Fin 6 → ℝ) (j : Fin 6) :
    selectedSquareExpr (slots m) t j = remainingSquare m j t := by
  simp only [selectedSquareExpr, sum_slots, Finset.sum_filter,
    remainingSquare, not_mem_slots]

/-- Coefficients in PHYSICAL coordinates; the mapped original source
stores the pullback under its exact inverse chart. -/
def endpointRow (c : Cell) : Affine :=
  let s : ℝ := if descending c then -3 / 2 else 1 / 2
  let a : ℝ := (if descending c then 57 / 64 else 1 / 2) - eta
  ![a, if bit (mask c) 0 then s else 0,
    if bit (mask c) 1 then s else 0,
    if bit (mask c) 2 then s else 0,
    if bit (mask c) 3 then s else 0,
    if bit (mask c) 4 then s else 0,
    if bit (mask c) 5 then s else 0]

def fullRow (j : Fin 6) : Affine :=
  fun i => if h : i.val = 0 then 0 else
    (if (i.val - 1) < j.val then 1 else 0) + (if i.val - 1 = j.val then 2 else 0)

def remainingRow (m : ℕ) (j : Fin 6) : Affine :=
  fun i => if h : i.val = 0 then 0 else
    (if bit m (i.val - 1) then 1 else 0) +
    (if i.val - 1 < j.val ∧ bit m (i.val - 1) = false then 1 else 0) +
    (if i.val - 1 = j.val then 2 else 0)

def rowSub (a b : Affine) : Affine := fun i => a i - b i

def encode (c : Cell) (a : Affine) : Affine :=
  if mapped c then
    ![a 0 + a 4 / 2, a 1 - a 4 / 2, a 2 - a 4, a 3 - a 4,
      -3 * a 4 / 2 + a 5 / 2, a 4 / 2 - a 5 / 2, a 6]
  else a

theorem eval_rowSub (a b : Affine) (t : Point) :
    eval (rowSub a b) t = eval a t - eval b t := by
  simp only [eval, rowSub, sub_mul, Finset.sum_sub_distrib]
  ring

theorem eval_encode (c : Cell) (a : Affine) (t : Point) :
    eval (encode c a) (coordinates c t) = eval a t := by
  cases hm : mapped c with
  | false => simp only [encode, coordinates, hm, Bool.false_eq_true, if_false]
  | true =>
    simp only [encode, coordinates, hm, Bool.true_eq_true, if_true]
    norm_num [eval, chart, R0, S5, H5, Fin.sum_univ_succ]
    <;> ring

theorem eval_endpointRow (c : Cell) (t : Point) :
    eval (endpointRow c) t = endpoint c t := by
  fin_cases c <;>
    norm_num [endpointRow, endpoint,
      selectedSum,
      descending, mask,
      Certificates.P2OriginalSixthElevenLogSemantics.selectedSum,
      bit,
      eval, Fin.sum_univ_succ] <;> ring

theorem eval_fullRow (j : Fin 6) (t : Point) :
    eval (fullRow j) t = fullSquare j t := by
  fin_cases j <;>
    norm_num [eval, fullRow, fullSquare, Fin.sum_univ_succ] <;> ring

theorem eval_remainingRow (m : ℕ) (j : Fin 6) (t : Point) :
    eval (remainingRow m j) t = remainingSquare m j t := by
  fin_cases j
  all_goals simp [eval, remainingRow, remainingSquare,
    Certificates.P2OriginalSixthElevenLogSemantics.selectedSum, Fin.sum_univ_succ, ite_mul, add_mul]
  all_goals ring

/-- Closed coefficient-certificate bodies. The original rows remain the
source of truth, including chart conventions, eta and each selected mask.
These tactics have NOT been evaluated in this packet. -/
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem full_row_mem (c : Cell) (j : Fin 6) :
    encode c (rowSub (endpointRow c) (fullRow j)) ∈ rows c := by
  fin_cases c <;> fin_cases j <;>
    norm_num [encode, rowSub, endpointRow, fullRow, mapped, mask,
      descending, bit, eta, rows, funext_iff, Fin.forall_fin_succ]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem remaining_row_mem (c : Cell) (j : Fin 6)
    (hj : bit (mask c) j.val = false) :
    encode c (rowSub (endpointRow c) (remainingRow (mask c) j)) ∈ rows c := by
  fin_cases c <;> fin_cases j <;>
    norm_num [mask, bit] at hj
  all_goals norm_num [encode, rowSub, endpointRow, remainingRow,
    mapped, mask, descending, bit, eta, rows,
    funext_iff, Fin.forall_fin_succ]

/-- All nineteen sources now supply both square families directly.
No current-parent, licence-record or actual-frontier premise is involved. -/
theorem later_source_squares (c : Cell) (t : Point) (hs : Source c t) :
    (∀ j, prefixSquareExpr t j < endpoint c t) ∧
    (∀ j ∉ slots (mask c),
      selectedSquareExpr (slots (mask c)) t j < endpoint c t) := by
  constructor
  · intro j
    have h := hs _ (full_row_mem c j)
    rw [eval_encode, eval_rowSub, eval_endpointRow, eval_fullRow] at h
    rw [full_dictionary]
    linarith
  · intro j hj
    have h := hs _ (remaining_row_mem c j ((not_mem_slots _ _).mp hj))
    rw [eval_encode, eval_rowSub, eval_endpointRow, eval_remainingRow] at h
    rw [remaining_dictionary]
    linarith

/-- The basic physical order rows are also original finite row entries,
not inequalities inferred from a guessed chart or archived gain. -/
def coordinateRow (i : Fin 6) : Affine :=
  fun j => if j.val = i.val + 1 then 1 else 0

def constantRow (x : ℝ) : Affine := ![x,0,0,0,0,0,0]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem basic_rows_mem (c : Cell) :
    encode c (rowSub (constantRow (25 / 128)) (coordinateRow 0)) ∈ rows c ∧
    encode c (rowSub (constantRow (1 / 50)) (coordinateRow 5)) ∈ rows c ∧
    encode c (rowSub (coordinateRow 5) (constantRow (53 / 4608))) ∈ rows c ∧
    ∀ j : Fin 5, encode c (rowSub (coordinateRow j.castSucc) (coordinateRow j.succ)) ∈ rows c := by
  fin_cases c
  all_goals norm_num [encode, rowSub, coordinateRow, constantRow, mapped,
    rows, funext_iff, Fin.forall_fin_succ]

theorem eval_coordinateRow (i : Fin 6) (t : Point) :
    eval (coordinateRow i) t = t i := by
  fin_cases i <;> norm_num [eval, coordinateRow, Fin.sum_univ_succ]

theorem eval_constantRow (x : ℝ) (t : Point) :
    eval (constantRow x) t = x := by simp [eval, constantRow, Fin.sum_univ_succ]

theorem later_source_basic (c : Cell) (t : Point) (hs : Source c t) :
    t 0 < (25 / 128 : ℝ) ∧ t 5 < (1 / 50 : ℝ) ∧
      (53 / 4608 : ℝ) < t 5 ∧ StrictAnti t := by
  have h := basic_rows_mem c
  have h0 := hs _ h.1
  have h5 := hs _ h.2.1
  have hlo := hs _ h.2.2.1
  simp only [eval_encode, eval_rowSub, eval_constantRow, eval_coordinateRow] at h0 h5 hlo
  refine ⟨by linarith,by linarith,by linarith,Fin.strictAnti_iff_succ_lt.mpr ?_⟩
  intro j
  have hj := hs _ (h.2.2.2 j)
  rw [eval_encode, eval_rowSub, eval_coordinateRow, eval_coordinateRow] at hj
  linarith

/-- The comparison charts have a genuine >1/2 floor on the original
source, including the descending33 comparison. -/
theorem later_comparison_half (c : Cell) (t : Point) (hs : Source c t) :
    (1 / 2 : ℝ) < comparison c t := by
  obtain ⟨h0,h5,hlo,ho⟩ := later_source_basic c t hs
  have h50 := ho.antitone (show (0 : Fin 6) ≤ 5 by decide)
  have h51 := ho.antitone (show (1 : Fin 6) ≤ 5 by decide)
  unfold comparison
  split_ifs <;> dsimp only [R0, descending33, ascending34] <;> linarith

end
end ImbalancedChen.P4AOriginalSixthSquareRows
