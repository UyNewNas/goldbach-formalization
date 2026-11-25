import ImbalancedChen.P2OriginalSaving19HigherMomentsCore

/-! SOURCE_ONLY / UNCOMPILED CANDIDATE.
Universal polynomial guards: integratedPower_newton_guard_0_5.
Original Saving19 public definitions and statement types are retained.
Finite proof representation specializes the accepted Fin 7 donor.
No numerical witness, evaluator, assumption, or external estimate is added.
-/
namespace ImbalancedChen.P2OriginalSaving19HigherMoments.ProofPieces
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2OriginalSaving19SimplexMoments

theorem integratedPower_newton_guard_0_5 (y : Fin 9 → ℝ) :
    integratedPower y 5 0 = duplicateH y 5 0 /
      ((Nat.factorial 9 : ℝ) * ((9 + 0).choose 0 : ℝ)) := by
  classical
  -- Reuse the accepted coefficient cancellation before any tuple enumeration.
  rw [integratedPower_eq_factored]
  all_goals
    norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  -- Degree zero was already enumerated by the preceding norm_num.
  -- The final stage contains only monomials and the original Newton recurrence.
  all_goals
    norm_num [duplicateH, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod,
      rational_smul_real]
    <;> first | rfl | ring1!

end
end ImbalancedChen.P2OriginalSaving19HigherMoments.ProofPieces
