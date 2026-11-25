import ImbalancedChen.P2OriginalSaving19HigherMomentsCore

/-! SOURCE_ONLY / UNCOMPILED CANDIDATE.
Author/Newton guard for degree 4; index stays arbitrary.
Original Saving19 public definitions and statement types are retained.
Finite proof representation specializes the accepted Fin 7 donor.
No numerical witness, evaluator, assumption, or external estimate is added.
-/
namespace ImbalancedChen.P2OriginalSaving19HigherMoments.ProofPieces
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2OriginalSaving19SimplexMoments

theorem duplicateH_author_guard_4 (y : Fin 9 → ℚ) (i : Fin 9) :
    duplicateH y i 4 = ∑ j : Fin (4 + 1),
      completeH (List.ofFn y) (4 - j.val) * y i ^ j.val := by
  norm_num [duplicateH, completeH_nil, completeH_cons_succ, completeH_zero, ofFn_nine, ofFn_eight, Fin.sum_univ_succ,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.val_zero, Fin.val_succ, Fin.val_mk, Fin.coe_ofNat_eq_mod, rational_smul_self] <;> first | rfl | ring1!

end
end ImbalancedChen.P2OriginalSaving19HigherMoments.ProofPieces
