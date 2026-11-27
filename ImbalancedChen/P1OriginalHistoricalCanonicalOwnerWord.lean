import ImbalancedChen.P1OriginalHistoricalRoughOwnerPartition
import Mathlib.Data.List.Sort

/-!
UNCOMPILED CANDIDATE. No Lean/kernel acceptance is claimed.
The actual historical prefix is an initial segment of the canonical descending
prime word, not just a collection of prime divisors. This is intended to connect
the accepted rough owner to later fixed whole-atom coordinate words.
-/
namespace ImbalancedChen.P1OriginalHistoricalCanonicalOwnerWord
noncomputable section
open Classical

theorem selected_remaining_sublist {α : Type*}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (pre carrier : List α) (positive : Bool) (mass : ℝ)
    (state : FirstExitDepthState α)
    (hs : state ∈ p1SignedExitStates retained h pre positive mass carrier) :
    List.Sublist (state.selectedPrefix.reverse ++ state.remaining) (pre.reverse ++ carrier) := by
  induction carrier generalizing pre positive mass with
  | nil => simp [p1SignedExitStates] at hs
  | cons p ps ih =>
    have hskip (ht : state ∈ p1SignedExitStates retained h pre positive mass ps) :
        List.Sublist (state.selectedPrefix.reverse ++ state.remaining) (pre.reverse ++ p :: ps) :=
      (ih pre positive mass ht).trans
        ((List.Sublist.refl _).append (List.sublist_cons_self p ps))
    by_cases hp : retained (!positive) (p :: pre) = true
    · rw [p1SignedExitStates, if_pos hp, List.mem_append] at hs
      rcases hs with ht | ht
      · exact hskip ht
      · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
          ih (p :: pre) (!positive) (mass * h p) ht
    · rw [p1SignedExitStates, if_neg hp, List.mem_append] at hs
      rcases hs with ht | ht
      · exact hskip ht
      · simp only [List.mem_singleton] at ht
        subst state
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
          (List.Sublist.refl (pre.reverse ++ p :: ps))

open P1OriginalHistoricalRoughOwnerPartition (Realizes owner owner_spec)

theorem realized_canonical_word
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (state : FirstExitDepthState ℕ) (b : ℕ)
    (hr : Realizes old fresh N cap w z state b) :
    ∃ tail : List ℕ,
      b.primeFactorsList.reverse = state.selectedPrefix.reverse ++ tail ∧
      List.Sublist tail state.remaining ∧
      ((old state.selectedPrefix = true ∧
        FirstExitValidSelection (oddFirstExitPolicy old)
          state.selectedPrefix state.positive tail) ∨
       (fresh state.selectedPrefix = true ∧
        FirstExitValidSelection (oddFirstExitPolicy fresh)
          state.selectedPrefix state.positive tail)) := by
  obtain ⟨hs, _, _, _, _, tail, hprod, ht, hv⟩ := hr
  have hwhole := selected_remaining_sublist
    (p1CommonAdmissionPolicy (oddFirstExitPolicy old) (oddFirstExitPolicy fresh))
    (fun _ => 1) [] (roughPrimeUniverse N cap w z) true 1 state hs
  simp only [List.reverse_nil, List.nil_append] at hwhole
  have hsub : List.Sublist (state.selectedPrefix.reverse ++ tail) (roughPrimeUniverse N cap w z) :=
    ((List.Sublist.refl _).append ht).trans hwhole
  have hp : ∀ p ∈ state.selectedPrefix.reverse ++ tail, p.Prime := by
    intro p hm
    exact mem_roughPrimeUniverse_prime (hsub.subset hm)
  have he : (state.selectedPrefix.reverse ++ tail).prod = b := by
    simpa only [List.prod_append, List.prod_reverse] using hprod.symm
  have hperm := Nat.primeFactorsList_unique he hp
  have hperm' : (state.selectedPrefix.reverse ++ tail).Perm b.primeFactorsList.reverse :=
    hperm.trans (List.reverse_perm _).symm
  have hsort : (state.selectedPrefix.reverse ++ tail).Pairwise (· ≥ ·) :=
    ((roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub).imp
      (fun hab => Nat.le_of_lt hab)
  have hcanonical : b.primeFactorsList.reverse.Pairwise (· ≥ ·) := by
    simpa only [List.pairwise_reverse] using (Nat.primeFactorsList_sorted b).pairwise
  have hword := List.Perm.eq_of_pairwise' hsort hcanonical hperm'
  exact ⟨tail, hword.symm, ht, hv⟩

theorem owner_prefix_is_canonical
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (b : ℕ)
    (hb : b ∈ P1OriginalHistoricalRoughOwnerPartition.changedRough old fresh N cap w z) :
    (owner old fresh N cap w z b).selectedPrefix.reverse.IsPrefix b.primeFactorsList.reverse := by
  obtain ⟨tail, he, _, _⟩ := realized_canonical_word old fresh N cap w z
    (owner old fresh N cap w z b) b (owner_spec old fresh N cap w z b hb)
  exact ⟨tail, he.symm⟩

end
end ImbalancedChen.P1OriginalHistoricalCanonicalOwnerWord
