import ImbalancedChen.P2OriginalSaving19HigherMomentsCore

/-! SOURCE_ONLY / UNCOMPILED CANDIDATE.
Universal polynomial guards: integratedPower_newton_guard_3_0.
Original Saving19 public definitions and statement types are retained.
Finite proof representation specializes the accepted Fin 7 donor.
No numerical witness, evaluator, assumption, or external estimate is added.
-/
namespace ImbalancedChen.P2OriginalSaving19HigherMoments.ProofPieces
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2OriginalSaving19SimplexMoments

theorem integratedPower_newton_guard_3_0 (y : Fin 9 → ℝ) :
    integratedPower y 0 3 = duplicateH y 0 3 /
      ((Nat.factorial 9 : ℝ) * ((9 + 3).choose 3 : ℝ)) := by
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
end ImbalancedChen.P2OriginalSaving19HigherMoments.ProofPieces
