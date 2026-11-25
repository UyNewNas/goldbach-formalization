import NewtonDuplicateDiagnostic
import AntidiagonalCompleteDiagnostic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Factorization

namespace P26LocalMomentStructural
noncomputable section
open scoped BigOperators

/- Exact right-hand side of the accepted Core integratedPower_eq_factored. -/
def factoredIntegratedPower (y : Fin 9 → ℝ) (i : Fin 9) (k : ℕ) : ℝ :=
      ((k.factorial : ℝ) / ((k + 9).factorial : ℝ)) *
        ∑ e ∈ Finset.piAntidiag Finset.univ k,
          ((e i + 1 : ℕ) : ℝ) * ∏ r : Fin 9, y r ^ e r

theorem factoredIntegratedPower_newton_guard_zero (y : Fin 9 → ℝ)
    (k : ℕ) (hk : k ≤ 6) :
    factoredIntegratedPower y 0 k =
      duplicateH y 0 k / ((Nat.factorial 9 : ℝ) * ((9 + k).choose k : ℝ)) := by
  rw [factoredIntegratedPower, weighted_antidiagonal_zero_eq_completeH]
  rw [← duplicateH_eq_completeH_small y 0 k hk]
  interval_cases k <;>
    norm_num [Nat.factorial, Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial] <;> ring

theorem duplicateH_author_guard_structural (y : Fin 9 → ℚ) (i : Fin 9)
    (k : ℕ) (hk : k ≤ 6) :
    duplicateH y i k = ∑ j : Fin (k + 1),
      completeH (List.ofFn y) (k - j.val) * y i ^ j.val := by
  rw [duplicateH_eq_completeH_small y i k hk, completeH]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

end
end P26LocalMomentStructural

#print axioms P26LocalMomentStructural.factoredIntegratedPower_newton_guard_zero
#print axioms P26LocalMomentStructural.duplicateH_author_guard_structural
