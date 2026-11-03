import ImbalancedChen.FirstExitValidSelection
import ImbalancedChen.FirstExitFrontierInvariants

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.
Constructive reverse admission into the literal stopped occurrence LIST.
The depth is exactly the incoming length plus the chosen length. No
frontier membership, mass formula or remaining-carrier identity is input.
-/
namespace ImbalancedChen.P1ActualFrontierReverseAdmission
noncomputable section
open scoped Classical List BigOperators

/-- A valid ordered sublist reaches its exact selected rank. Unlike a
terminal-leaf witness, the resulting state stops before scanning its suffix. -/
theorem exists_frontier_of_validSelection
    {α : Type*} (parent : Bool → List α → Bool) (weight : α → ℝ)
    {chosen carrier : List α} (hsub : chosen <+ carrier)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (hvalid : FirstExitValidSelection parent pre positive chosen) :
    ∃ state ∈ firstExitDepthFrontier (pre.length + chosen.length) parent weight
      pre positive mass carrier, state.selectedPrefix = chosen.reverse ++ pre := by
  induction hsub generalizing pre positive mass with
  | slnil =>
      refine ⟨⟨pre, positive, mass, []⟩, ?_, by simp⟩
      simp only [List.length_nil, Nat.add_zero,
        firstExitDepthFrontier_of_rank_le_length _ _ _ _ _ _ _ le_rfl,
        List.mem_singleton]
  | @cons chosen carrier p hsub ih =>
      by_cases hz : chosen = []
      · subst chosen
        refine ⟨⟨pre, positive, mass, p :: carrier⟩, ?_, by simp⟩
        simp only [List.length_nil, Nat.add_zero,
          firstExitDepthFrontier_of_rank_le_length _ _ _ _ _ _ _ le_rfl,
          List.mem_singleton]
      · obtain ⟨state, hs, heq⟩ := ih pre positive mass hvalid
        have hn : ¬ pre.length + chosen.length ≤ pre.length := by
          have hp : 0 < chosen.length := List.length_pos.mpr hz
          omega
        refine ⟨state, ?_, heq⟩
        rw [firstExitDepthFrontier, if_neg hn]
        exact List.mem_append_left _ hs
  | @cons_cons chosen carrier p hsub ih =>
      obtain ⟨htest, htail⟩ := hvalid
      obtain ⟨state, hs, heq⟩ := ih (p :: pre) (!positive) (mass * weight p) htail
      refine ⟨state, ?_, ?_⟩
      · have hn : ¬ pre.length + (p :: chosen).length ≤ pre.length := by
          simp only [List.length_cons]
          omega
        rw [firstExitDepthFrontier, if_neg hn, if_pos htest]
        apply List.mem_append_right
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hs
      · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using heq

/-- Two strictly decreasing natural lists have the same relative order.
Thus literal pointwise inclusion constructs a sublist, not just a Finset. -/
theorem decreasing_sublist_of_subset (xs ys : List ℕ)
    (hx : xs.Pairwise (· > ·)) (hy : ys.Pairwise (· > ·))
    (hmem : ∀ p ∈ xs, p ∈ ys) : xs <+ ys := by
  induction ys generalizing xs with
  | nil =>
      cases xs with
      | nil => exact List.Sublist.refl []
      | cons a as => have h := hmem a (by simp); simp at h
  | cons b bs ih =>
      cases xs with
      | nil => exact List.nil_sublist _
      | cons a as =>
          have hx' := List.pairwise_cons.mp hx
          have hy' := List.pairwise_cons.mp hy
          by_cases hab : a = b
          · subst b
            apply List.Sublist.cons_cons
            apply ih as hx'.2 hy'.2
            intro p hp
            have h := hmem p (List.mem_cons_of_mem a hp)
            rcases List.mem_cons.mp h with h | h
            · subst p
              exact (lt_irrefl a (hx'.1 a hp)).elim
            · exact h
          · apply List.Sublist.cons
            apply ih (a :: as) hx hy'.2
            intro p hp
            have h := hmem p hp
            rcases List.mem_cons.mp h with h | h
            · subst p
              have ha : a ∈ bs := (List.mem_cons.mp (hmem a (by simp))).resolve_left hab
              have hba : a < b := hy'.1 a ha
              rcases List.mem_cons.mp hp with h | h
              · exact (hab h.symm).elim
              · exact (lt_asymm hba (hx'.1 b h)).elim
            · exact h

/-- Actual prime/deletion/half-open bounds supply the real carrier.
The enumeration bound is discharged from z <= cap. -/
theorem valid_prime_history_reaches_frontier
    (parent : Bool → List ℕ → Bool) (weight : ℕ → ℝ)
    (N cap : ℕ) (w z : ℝ) (hzcap : z ≤ (cap : ℝ))
    (pre : List ℕ) (hsort : pre.Pairwise (· < ·))
    (hp : ∀ p ∈ pre, p.Prime ∧ ¬p ∣ N ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z)
    (hvalid : FirstExitValidSelection parent [] true pre.reverse) :
    ∃ state ∈ firstExitDepthFrontier pre.length parent weight [] true 1
      (roughPrimeUniverse N cap w z), state.selectedPrefix = pre := by
  have hsub : pre.reverse <+ roughPrimeUniverse N cap w z := by
    apply decreasing_sublist_of_subset
    · simpa only [List.pairwise_reverse] using hsort
    · exact roughPrimeUniverse_pairwise_gt N cap w z
    · intro p hmem
      exact (mem_roughPrimeUniverse_iff_of_cutoff_le_cap hzcap).mpr
        (hp p (List.mem_reverse.mp hmem))
  obtain ⟨state, hs, heq⟩ := exists_frontier_of_validSelection parent weight
    hsub [] true 1 hvalid
  exact ⟨state, by simpa using hs, by simpa using heq⟩

end
end ImbalancedChen.P1ActualFrontierReverseAdmission
