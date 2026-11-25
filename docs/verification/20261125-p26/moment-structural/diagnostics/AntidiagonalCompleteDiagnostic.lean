import NewtonSmallDiagnostic
import FiniteSplitDiagnostic

namespace P26LocalMomentStructural
noncomputable section
open scoped BigOperators

theorem completeH_ofFn_eq_antidiagonal {A : Type*} [CommRing A]
    {n : ℕ} (y : Fin n → A) (k : ℕ) :
    completeH (List.ofFn y) k =
      ∑ e ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) k,
        ∏ r : Fin n, y r ^ e r := by
  classical
  induction n generalizing k with
  | zero =>
    change completeH ([] : List A) k =
      ∑ e ∈ Finset.piAntidiag (∅ : Finset (Fin 0)) k, ∏ r : Fin 0, y r ^ e r
    rw [completeH_nil, Finset.piAntidiag_empty]
    split_ifs <;> simp
  | succ n ih =>
    rw [List.ofFn_succ, completeH, sum_piAntidiag_univ_fin_succ]
    apply Finset.sum_congr rfl
    intro j _
    rw [ih (fun r => y r.succ) (k - j.val), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem completeH_cons_cons {A : Type*} [CommRing A]
    (a : A) (as : List A) (k : ℕ) :
    completeH (a :: a :: as) k =
      ∑ j : Fin (k + 1), ((j.val + 1 : ℕ) : A) * a ^ j.val * completeH as (k - j.val) := by
  induction k with
  | zero => simp [completeH_zero]
  | succ k ih =>
    rw [completeH_cons_succ, ih, completeH]
    rw [Fin.sum_univ_succ (fun j : Fin (k + 2) => a ^ j.val * completeH as (k + 1 - j.val))]
    rw [Fin.sum_univ_succ (fun j : Fin (k + 2) =>
      ((j.val + 1 : ℕ) : A) * a ^ j.val * completeH as (k + 1 - j.val))]
    simp only [Fin.val_zero, Fin.val_succ, Nat.sub_zero, zero_add, pow_zero, one_mul,
      Nat.cast_one, Nat.add_sub_add_right]
    rw [add_assoc, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem weighted_antidiagonal_zero_eq_completeH {A : Type*} [CommRing A]
    {n : ℕ} (y : Fin (n + 1) → A) (k : ℕ) :
    (∑ e ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (n + 1))) k,
      ((e 0 + 1 : ℕ) : A) * ∏ r : Fin (n + 1), y r ^ e r) =
      completeH (y 0 :: List.ofFn y) k := by
  classical
  rw [sum_piAntidiag_univ_fin_succ]
  simp only [Fin.cons_zero, Fin.prod_univ_succ, Fin.cons_succ]
  rw [List.ofFn_succ, completeH_cons_cons]
  apply Finset.sum_congr rfl
  intro j _
  rw [completeH_ofFn_eq_antidiagonal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

end
end P26LocalMomentStructural

#print axioms P26LocalMomentStructural.completeH_ofFn_eq_antidiagonal
#print axioms P26LocalMomentStructural.completeH_cons_cons
#print axioms P26LocalMomentStructural.weighted_antidiagonal_zero_eq_completeH
