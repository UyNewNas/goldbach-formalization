import ImbalancedChen.P2OriginalSixthHigherMomentsCore

/-! SOURCE_ONLY / UNCOMPILED.
Existing universal polynomial guards: integratedPower_newton_guard_5_4.
The existing a9a4e532 proof bodies are retained; this file changes only
compilation organization. No numerical row or new evaluator is introduced.
-/
namespace ImbalancedChen.P2OriginalSixthHigherMoments.ProofPieces
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2OriginalSixthSimplexMoments

theorem integratedPower_newton_guard_5_4 (y : Fin 7 → ℝ) :
    integratedPower y 4 5 = duplicateH y 4 5 /
      ((Nat.factorial 7 : ℝ) * ((7 + 5).choose 5 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Enumerate tuples without opening factorials, multinomial or Newton products.
  all_goals
    simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
      Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
      List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
      List.range_succ, List.range_zero,
      Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

end
end ImbalancedChen.P2OriginalSixthHigherMoments.ProofPieces
