import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
SOURCE CANDIDATE / NO P1 ACCEPTANCE CLAIM.
Finite reindexing only. This module imports no project analytic supplier
and enumerates no antidiagonal tuples. The weight is arbitrary; the Core
wrapper uses w n = (n + 1 : ℕ), cast to the original real coefficient.
-/
namespace ImbalancedChen.P2OriginalSaving19HigherMoments.ProofPieces

noncomputable section
open scoped BigOperators

private theorem mem_piAntidiag_comp (σ : Equiv.Perm (Fin 9))
    {e : Fin 9 → ℕ} {k : ℕ}
    (he : e ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 9)) k) :
    e ∘ σ ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 9)) k := by
  classical
  refine Finset.mem_piAntidiag.mpr ⟨?_, fun r _ => Finset.mem_univ r⟩
  exact (Equiv.sum_comp σ e).trans (Finset.mem_piAntidiag.mp he).1

/-- The exponent tuple on the left is sent to e ∘ σ.symm on the right. -/
theorem weighted_antidiagonal_sum_perm {A : Type*}
    [AddCommMonoid A] [CommMonoid A]
    (σ : Equiv.Perm (Fin 9)) (y : Fin 9 → A) (w : ℕ → A)
    (i : Fin 9) (k : ℕ) :
    (∑ e ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 9)) k,
      w (e i) * ∏ r : Fin 9, (y ∘ σ) r ^ e r) =
    ∑ e ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 9)) k,
      w (e (σ i)) * ∏ r : Fin 9, y r ^ e r := by
  classical
  refine Finset.sum_bij (fun e _ => e ∘ σ.symm) ?_ ?_ ?_ ?_
  · intro e he
    exact mem_piAntidiag_comp σ.symm he
  · intro e₁ _ e₂ _ h
    funext r
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
      congrFun h (σ r)
  · intro e he
    refine ⟨e ∘ σ, mem_piAntidiag_comp σ he, ?_⟩
    funext r
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  · intro e _
    have hp :
        (∏ r : Fin 9, (y ∘ σ) r ^ e r) =
          ∏ r : Fin 9, y r ^ (e ∘ σ.symm) r := by
      simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
        Equiv.prod_comp σ (fun r : Fin 9 => y r ^ e (σ.symm r))
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
      congrArg (fun z : A => w (e i) * z) hp

end
end ImbalancedChen.P2OriginalSaving19HigherMoments.ProofPieces
