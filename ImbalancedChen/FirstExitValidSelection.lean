import ImbalancedChen.FirstExitGenericModuli

/-!
# Constructive retained selections

An ordered chosen sublist is valid exactly when each successive selected
prefix passes the actual policy. This module constructs the corresponding
retained leaf, and recovers a valid chosen sublist from every retained leaf.
It is finite tree algebra and imposes no density or distribution hypothesis.
-/

namespace ImbalancedChen

open scoped List

/-- Chosen labels are listed in their processing order; the incoming prefix
is stored in the tree's reverse processing order. -/
def FirstExitValidSelection {α : Type*}
    (retained : Bool → List α → Bool) (pre : List α) (positive : Bool) : List α → Prop
  | [] => True
  | p :: ps => retained (!positive) (p :: pre) = true ∧
      FirstExitValidSelection retained (p :: pre) (!positive) ps

theorem exists_firstExitRetainedLeaf_of_validSelection
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    {chosen remaining : List α} (hsub : chosen <+ remaining)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (hvalid : FirstExitValidSelection retained pre positive chosen) :
    ∃ leaf ∈ firstExitRetainedLeaves retained h pre positive mass remaining,
      leaf.selected = chosen.reverse ++ pre := by
  induction hsub generalizing pre positive mass with
  | slnil =>
      exact ⟨⟨pre, positive, mass⟩, by simp [firstExitRetainedLeaves], by simp⟩
  | cons p hsub ih =>
      obtain ⟨leaf, hleaf, heq⟩ := ih pre positive mass hvalid
      refine ⟨leaf, ?_, heq⟩
      rw [firstExitRetainedLeaves]
      exact List.mem_append_left _ hleaf
  | cons_cons p hsub ih =>
      obtain ⟨hleafTest, htail⟩ := hvalid
      obtain ⟨leaf, hleaf, heq⟩ := ih (p :: pre) (!positive) (mass * h p) htail
      refine ⟨leaf, ?_, ?_⟩
      · rw [firstExitRetainedLeaves, if_pos hleafTest]
        exact List.mem_append_right _ hleaf
      · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using heq

theorem exists_validSelection_of_mem_firstExitRetainedLeaves
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ)
    (leaf : FirstExitLeaf α)
    (hleaf : leaf ∈ firstExitRetainedLeaves retained h pre positive mass remaining) :
    ∃ chosen : List α, chosen <+ remaining ∧
      FirstExitValidSelection retained pre positive chosen ∧
        leaf.selected = chosen.reverse ++ pre := by
  induction remaining generalizing pre positive mass with
  | nil =>
      simp only [firstExitRetainedLeaves, List.mem_singleton] at hleaf
      subst leaf
      exact ⟨[], List.Sublist.refl [], trivial, by simp⟩
  | cons p ps ih =>
      rw [firstExitRetainedLeaves, List.mem_append] at hleaf
      rcases hleaf with hskip | hselect
      · obtain ⟨chosen, hsub, hvalid, heq⟩ := ih pre positive mass hskip
        exact ⟨chosen, hsub.cons p, hvalid, heq⟩
      · by_cases hp : retained (!positive) (p :: pre) = true
        · rw [if_pos hp] at hselect
          obtain ⟨chosen, hsub, hvalid, heq⟩ :=
            ih (p :: pre) (!positive) (mass * h p) hselect
          refine ⟨p :: chosen, hsub.cons_cons p, ⟨hp, hvalid⟩, ?_⟩
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using heq
        · simp only [if_neg hp, List.not_mem_nil] at hselect

/-- At the root, the actual retained modulus support is precisely the
products of valid chosen sublists. This supplies both directions. -/
theorem mem_firstExitRetainedModuli_iff_validSelection
    (retained : Bool → List ℕ → Bool) (carrier : List ℕ) (d : ℕ) :
    d ∈ firstExitRetainedModuli retained carrier ↔
      ∃ chosen : List ℕ, chosen <+ carrier ∧
        FirstExitValidSelection retained [] true chosen ∧ chosen.prod = d := by
  classical
  unfold firstExitRetainedModuli firstExitRootLeaves
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨leaf, hleaf, hprod⟩
    obtain ⟨chosen, hsub, hvalid, heq⟩ :=
      exists_validSelection_of_mem_firstExitRetainedLeaves retained (fun _ => 1)
        [] carrier true 1 leaf hleaf
    refine ⟨chosen, hsub, hvalid, ?_⟩
    simpa only [heq, List.append_nil, List.prod_reverse] using hprod
  · rintro ⟨chosen, hsub, hvalid, hprod⟩
    obtain ⟨leaf, hleaf, heq⟩ := exists_firstExitRetainedLeaf_of_validSelection
      retained (fun _ => 1) hsub [] true 1 hvalid
    exact ⟨leaf, hleaf, by simpa only [heq, List.append_nil, List.prod_reverse] using hprod⟩

end ImbalancedChen
