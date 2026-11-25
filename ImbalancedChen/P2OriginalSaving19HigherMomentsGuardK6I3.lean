import ImbalancedChen.P2OriginalSaving19HigherMomentsCore

/-! SOURCE_ONLY / UNCOMPILED CANDIDATE.
Universal polynomial guards: integratedPower_newton_guard_6_3.
Original Saving19 public definitions and statement types are retained.
Finite proof representation specializes the accepted Fin 7 donor.
No numerical witness, evaluator, assumption, or external estimate is added.
-/
namespace ImbalancedChen.P2OriginalSaving19HigherMoments.ProofPieces
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2OriginalSaving19SimplexMoments

theorem integratedPower_newton_guard_6_3 (y : Fin 9 → ℝ) :
    integratedPower y 3 6 = duplicateH y 3 6 /
      ((Nat.factorial 9 : ℝ) * ((9 + 6).choose 6 : ℝ)) := by
  classical
  -- Phase 1: a previously structured coefficient proof removes all tuple factorials.
  rw [integratedPower_eq_factored]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Phase 2: enumerate only the finite tuple list; keep products/Newton opaque.
  simp [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple,
    Finset.Nat.antidiagonalTuple, Multiset.Nat.antidiagonalTuple,
    List.Nat.antidiagonalTuple, List.Nat.antidiagonal,
    List.range_succ, List.range_zero,
    Finset.sum_map, Finset.sum_cons, Finset.sum_singleton]
  -- Phase 3: expand the simple monomials and the existing Newton recurrence.
  norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
    Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
    rational_smul_real]
  <;> first | rfl | ring1!

end
end ImbalancedChen.P2OriginalSaving19HigherMoments.ProofPieces
