import ImbalancedChen.P2OriginalSaving19HigherMomentsSymmetry
import ImbalancedChen.P2OriginalSaving19HigherMomentsGuardLowBoundary

/-!
SOURCE CANDIDATE / NOT COMPILED.
An arbitrary-index transport pilot using only the accepted degree-two
index-zero leaf. No higher-degree provider is imported or re-evaluated.
-/
namespace ImbalancedChen.P2OriginalSaving19HigherMoments.ProofPieces

noncomputable section

theorem integratedPower_newton_guard_2_all_indices
    (y : Fin 9 → ℝ) (i : Fin 9) :
    integratedPower y i 2 = duplicateH y i 2 /
      ((Nat.factorial 9 : ℝ) * ((9 + 2).choose 2 : ℝ)) := by
  simpa only [integratedPower_perm, duplicateH_perm, Equiv.swap_apply_left] using
    integratedPower_newton_guard_2_0 (y ∘ Equiv.swap (0 : Fin 9) i)

end
end ImbalancedChen.P2OriginalSaving19HigherMoments.ProofPieces
