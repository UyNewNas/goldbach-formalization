import ImbalancedChen.P2OriginalSaving19HigherMomentsSymmetry
import ImbalancedChen.P2OriginalSaving19HigherMomentsGuardLowBoundary
import ImbalancedChen.P2OriginalSaving19HigherMomentsGuardK3I0
import ImbalancedChen.P2OriginalSaving19HigherMomentsGuardK4I0
import ImbalancedChen.P2OriginalSaving19HigherMomentsGuardK5I0
import ImbalancedChen.P2OriginalSaving19HigherMomentsGuardK6I0

/-!
SOURCE CANDIDATE / NOT COMPILED.
The original k <= 6 guard follows from the existing seven index-zero
leaves and finite permutation transport. The guard is a conclusion;
no index-zero identity or final saving is a theorem parameter.
-/
namespace ImbalancedChen.P2OriginalSaving19HigherMoments.ProofPieces

noncomputable section

theorem integratedPower_newton_guard_via_index_zero
    (y : Fin 9 → ℝ) (i : Fin 9) (k : ℕ) (hk : k ≤ 6) :
    integratedPower y i k =
      duplicateH y i k / ((9.factorial : ℝ) * ((9 + k).choose k : ℝ)) := by
  interval_cases k
  · simpa only [integratedPower_perm, duplicateH_perm, Equiv.swap_apply_left] using
      integratedPower_newton_guard_0_0 (y ∘ Equiv.swap (0 : Fin 9) i)
  · simpa only [integratedPower_perm, duplicateH_perm, Equiv.swap_apply_left] using
      integratedPower_newton_guard_1_0 (y ∘ Equiv.swap (0 : Fin 9) i)
  · simpa only [integratedPower_perm, duplicateH_perm, Equiv.swap_apply_left] using
      integratedPower_newton_guard_2_0 (y ∘ Equiv.swap (0 : Fin 9) i)
  · simpa only [integratedPower_perm, duplicateH_perm, Equiv.swap_apply_left] using
      integratedPower_newton_guard_3_0 (y ∘ Equiv.swap (0 : Fin 9) i)
  · simpa only [integratedPower_perm, duplicateH_perm, Equiv.swap_apply_left] using
      integratedPower_newton_guard_4_0 (y ∘ Equiv.swap (0 : Fin 9) i)
  · simpa only [integratedPower_perm, duplicateH_perm, Equiv.swap_apply_left] using
      integratedPower_newton_guard_5_0 (y ∘ Equiv.swap (0 : Fin 9) i)
  · simpa only [integratedPower_perm, duplicateH_perm, Equiv.swap_apply_left] using
      integratedPower_newton_guard_6_0 (y ∘ Equiv.swap (0 : Fin 9) i)

end
end ImbalancedChen.P2OriginalSaving19HigherMoments.ProofPieces
