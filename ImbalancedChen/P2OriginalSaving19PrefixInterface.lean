import ImbalancedChen.P2Winner9HomogeneousRecurrence
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
Internal finite-evaluator interface for the manuscript's simplex moment law.
The existing Winner9 prefix evaluator and its correctness theorem are reused
unchanged. No numerical witness or new analytic assumption is introduced.
The rules for F are an interface; the Saving19 specialization discharges them
with its original completeH definition, rather than assuming a final moment.
-/
namespace ImbalancedChen.P2OriginalSaving19PrefixInterface

open scoped BigOperators
open P2Winner9HomogeneousRecurrence

/-- The existing table realizes any coefficient function with exactly the
original empty/cons equations. The bound is only a table bound. -/
theorem prefixCoefficient_cast_eq {A : Type*} [CommSemiring A]
    (F : List A → Nat → A)
    (empty_rule : ∀ k, F [] k = if k = 0 then 1 else 0)
    (cons_rule : ∀ a xs k, F (a :: xs) k =
      ∑ j : Fin (k + 1), a ^ j.val * F xs (k - j.val))
    {n bound : Nat} (y : Fin n → Nat) (k : Nat) (hk : k ≤ bound) :
    (((prefixCoefficients bound n y)[k]?.getD 0 : Nat) : A) =
      F (List.ofFn (fun i => (y i : A))) k := by
  have hcoeff : ∀ {n : Nat} (y : Fin n → Nat) (k : Nat), k ≤ bound →
      (boundedHomogeneous y bound k : A) =
        F (List.ofFn (fun i => (y i : A))) k := by
    intro n
    induction n with
    | zero =>
      intro y k h
      rw [← prefixCoefficients_correct bound 0 y k h]
      simp only [List.ofFn_zero, empty_rule]
      cases k with
      | zero => simp [prefixCoefficients]
      | succ k =>
        simp only [prefixCoefficients, List.ofFn_zero, List.foldr_nil,
          List.getElem?_cons_succ, List.getElem?_replicate_of_lt (by omega : k < bound),
          Option.getD_some, Nat.cast_zero, Nat.succ_ne_zero, if_false]
    | succ n ih =>
      intro y k h
      rw [split_coefficient y h, Nat.cast_sum, List.ofFn_succ, cons_rule]
      simp only [Nat.cast_mul, Nat.cast_pow]
      rw [Fin.sum_univ_eq_sum_range
        (fun j : Nat => (y 0 : A) ^ j *
          F (List.ofFn (fun i : Fin n => (y i.succ : A))) (k - j)) (k + 1)]
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih (fun i => y i.succ) (k - j) ((Nat.sub_le k j).trans h)]
  rw [prefixCoefficients_correct bound n y k hk]
  exact hcoeff y k hk

#print axioms prefixCoefficient_cast_eq

end ImbalancedChen.P2OriginalSaving19PrefixInterface
