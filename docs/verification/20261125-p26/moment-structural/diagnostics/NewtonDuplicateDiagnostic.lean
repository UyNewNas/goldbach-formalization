import NewtonSmallDiagnostic

namespace P26LocalMomentStructural
noncomputable section
open scoped BigOperators

theorem duplicateH_eq_completeH_small {A : Type*} [CommRing A] [Algebra ℚ A]
    (y : Fin 9 → A) (i : Fin 9) (k : ℕ) (hk : k ≤ 6) :
    duplicateH y i k = completeH (y i :: List.ofFn y) k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp only [duplicateH, completeH_zero]
    | succ k =>
      have hn := completeH_newton_small (y i :: List.ofFn y) k (by omega)
      have hs :
          (∑ j : Fin (k + 1),
            ((∑ r : Fin 9, y r ^ (j.val + 1)) + y i ^ (j.val + 1)) *
              completeH (y i :: List.ofFn y) (k - j.val)) =
          (k + 1 : ℚ) • completeH (y i :: List.ofFn y) (k + 1) := by
        simpa only [powerSum, List.map_cons, List.sum_cons, List.map_ofFn, List.sum_ofFn,
          Algebra.smul_def, map_add, map_natCast, map_one, Nat.cast_add, Nat.cast_one,
          Function.comp_def, add_comm]
          using hn.symm
      calc
        duplicateH y i (k + 1) =
            ((k + 1 : ℚ)⁻¹) •
              ∑ j : Fin (k + 1),
                ((∑ r : Fin 9, y r ^ (j.val + 1)) + y i ^ (j.val + 1)) *
                  completeH (y i :: List.ofFn y) (k - j.val) := by
          rw [duplicateH]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [ih (k - j.val) (by omega) (by omega)]
        _ = ((k + 1 : ℚ)⁻¹) •
            ((k + 1 : ℚ) • completeH (y i :: List.ofFn y) (k + 1)) := by rw [hs]
        _ = completeH (y i :: List.ofFn y) (k + 1) := by
          rw [smul_smul, inv_mul_cancel₀ (show (k + 1 : ℚ) ≠ 0 by positivity)]
          simp

theorem duplicateH_author_guard_6_structural (y : Fin 9 → ℚ) (i : Fin 9) :
    duplicateH y i 6 = ∑ j : Fin (6 + 1),
      completeH (List.ofFn y) (6 - j.val) * y i ^ j.val := by
  rw [duplicateH_eq_completeH_small y i 6 (by decide), completeH]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

end
end P26LocalMomentStructural

#print axioms P26LocalMomentStructural.duplicateH_eq_completeH_small
#print axioms P26LocalMomentStructural.duplicateH_author_guard_6_structural
