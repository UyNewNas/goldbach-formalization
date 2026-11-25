import ImbalancedChen.P2OriginalSaving19HigherMomentsCore
import ImbalancedChen.P2OriginalSaving19MomentFiniteReindex

/-!
SOURCE CANDIDATE / NOT COMPILED.
Finite reindexing of the existing nine-node moment polynomial and its
Newton recurrence. No tuple enumeration, archived witness, or estimate is
introduced. The coefficient formula is supplied by the accepted Core.
-/
namespace ImbalancedChen.P2OriginalSaving19HigherMoments.ProofPieces

noncomputable section
open scoped BigOperators

/-- Reindex the exact factored moment sum by e ↦ e ∘ σ.symm. -/
theorem integratedPower_perm (σ : Equiv.Perm (Fin 9))
    (y : Fin 9 → ℝ) (i : Fin 9) (k : ℕ) :
    integratedPower (y ∘ σ) i k = integratedPower y (σ i) k := by
  classical
  rw [integratedPower_eq_factored, integratedPower_eq_factored]
  congr 1
  exact weighted_antidiagonal_sum_perm σ y (fun n => ((n + 1 : ℕ) : ℝ)) i k

/-- Each power sum is invariant under the same permutation, so the
existing Newton recurrence is equivariant at every recursive degree. -/
theorem duplicateH_perm {A : Type*} [CommRing A] [Algebra ℚ A]
    (σ : Equiv.Perm (Fin 9)) (y : Fin 9 → A) (i : Fin 9) (k : ℕ) :
    duplicateH (y ∘ σ) i k = duplicateH y (σ i) k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simp only [duplicateH]
    | succ k =>
      rw [duplicateH, duplicateH]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      have hs :
          (∑ r : Fin 9, (y ∘ σ) r ^ (j.val + 1)) =
            ∑ r : Fin 9, y r ^ (j.val + 1) :=
        Equiv.sum_comp σ (fun r : Fin 9 => y r ^ (j.val + 1))
      rw [hs, ih (k - j.val) (by omega)]
      rfl

end
end ImbalancedChen.P2OriginalSaving19HigherMoments.ProofPieces
