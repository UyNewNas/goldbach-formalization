import ImbalancedChen.P2OriginalSixthHigherMomentsCore

/-! SOURCE_ONLY / UNCOMPILED.
Existing universal polynomial guards: duplicateH_author_guard_5.
The existing a9a4e532 proof bodies are retained; this file changes only
compilation organization. No numerical row or new evaluator is introduced.
-/
namespace ImbalancedChen.P2OriginalSixthHigherMoments.ProofPieces
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2OriginalSixthSimplexMoments

theorem duplicateH_author_guard_5 (y : Fin 7 → ℚ) (i : Fin 7) :
    duplicateH y i 5 = ∑ j : Fin (5 + 1),
      completeH (List.ofFn y) (5 - j.val) * y i ^ j.val := by
  norm_num [duplicateH, completeH_nil, completeH_cons_succ, completeH_zero, ofFn_seven, ofFn_six, Fin.sum_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod, rational_smul_self] <;> first | rfl | ring1!

end
end ImbalancedChen.P2OriginalSixthHigherMoments.ProofPieces
