import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.Congr

/-! LOCAL DIAGNOSTIC ONLY. Exact copied Core definitions/proof pieces and
the exact current AuthorK6 statement/proof in an isolated namespace.
This module is not a production Saving19 owner or an acceptance receipt. -/
namespace P26LocalMomentStructural
noncomputable section
open scoped BigOperators

def duplicateH {A : Type*} [CommRing A] [Algebra ℚ A]
    (y : Fin 9 → A) (i : Fin 9) : ℕ → A
  | 0 => 1
  | k + 1 => ((k + 1 : ℚ)⁻¹) •
      ∑ j : Fin (k + 1),
        ((∑ r : Fin 9, y r ^ (j.val + 1)) + y i ^ (j.val + 1)) *
          duplicateH y i (k - j.val)
termination_by k => k
decreasing_by omega

def completeH {A : Type*} [CommRing A] : List A → ℕ → A
  | [], k => if k = 0 then 1 else 0
  | a :: as, k => ∑ j : Fin (k + 1), a ^ j.val * completeH as (k - j.val)

theorem completeH_cons_succ {A : Type*} [CommRing A]
    (a : A) (as : List A) (k : ℕ) :
    completeH (a :: as) (k + 1) =
      completeH as (k + 1) + a * completeH (a :: as) k := by
  simp only [completeH]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, Nat.sub_zero, one_mul, Fin.val_succ]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hs : k + 1 - (j.val + 1) = k - j.val := by omega
  rw [hs, pow_succ]
  ring

theorem ofFn_nine {A : Type*} (f : Fin 9 → A) :
    List.ofFn f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8] := by rfl

theorem ofFn_eight {A : Type*} (f : Fin 8 → A) :
    List.ofFn f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7] := by rfl

theorem rational_smul_self (q x : ℚ) : q • x = q * x := by rfl

theorem completeH_nil {A : Type*} [CommRing A] (k : ℕ) :
    completeH ([] : List A) k = (if k = 0 then 1 else 0) := by rfl

theorem completeH_zero {A : Type*} [CommRing A] (as : List A) :
    completeH as 0 = 1 := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [completeH, Fin.sum_univ_succ, ih]


def powerSum {A : Type*} [CommRing A] (as : List A) (k : ℕ) : A :=
  (as.map (fun a => a ^ k)).sum

theorem completeH_newton_small {A : Type*} [CommRing A]
    (as : List A) (k : ℕ) (hk : k ≤ 5) :
    ((k + 1 : ℕ) : A) * completeH as (k + 1) =
      ∑ j : Fin (k + 1), powerSum as (j.val + 1) * completeH as (k - j.val) := by
  induction as generalizing k with
  | nil => simp [completeH, powerSum]
  | cons a as ih =>
    have h0 := ih 0 (by decide)
    have h1 := ih 1 (by decide)
    have h2 := ih 2 (by decide)
    have h3 := ih 3 (by decide)
    have h4 := ih 4 (by decide)
    have h5 := ih 5 (by decide)
    norm_num [powerSum, completeH_zero, Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5
    interval_cases k
    · norm_num [powerSum, completeH_cons_succ, completeH_zero, Fin.sum_univ_succ]
      linear_combination h0
    · norm_num [powerSum, completeH_cons_succ, completeH_zero, Fin.sum_univ_succ]
      linear_combination h1 + a * h0
    · norm_num [powerSum, completeH_cons_succ, completeH_zero, Fin.sum_univ_succ]
      linear_combination h2 + a * h1 + a ^ 2 * h0
    · norm_num [powerSum, completeH_cons_succ, completeH_zero, Fin.sum_univ_succ]
      linear_combination h3 + a * h2 + a ^ 2 * h1 + a ^ 3 * h0
    · norm_num [powerSum, completeH_cons_succ, completeH_zero, Fin.sum_univ_succ]
      linear_combination h4 + a * h3 + a ^ 2 * h2 + a ^ 3 * h1 + a ^ 4 * h0
    · norm_num [powerSum, completeH_cons_succ, completeH_zero, Fin.sum_univ_succ]
      linear_combination h5 + a * h4 + a ^ 2 * h3 + a ^ 3 * h2 + a ^ 4 * h1 + a ^ 5 * h0

end
end P26LocalMomentStructural

#print axioms P26LocalMomentStructural.completeH_newton_small
