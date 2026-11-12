import ImbalancedChen.P4AOriginalFull87ThreeClassLeafInvoices

/-! Recover the actual carrier on the indicated side of each paid occurrence.
The public signed conservation law for pairedCopies identifies its two
nonnegative occurrence counts, avoiding access to its private erasure helper. -/
namespace ImbalancedChen.P4AOriginalFull87FrontierLeafMembership
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87UnmatchedPhysicalLeaves (pairedCopies pairedCopies_signed)
open P4AOriginalFull87ExclusiveLeafSignedCut (firstDisagreementLeaves)

/-- A match comes from both input lists; each unmatched copy comes from the
input on the indicated side. The source lists need not be duplicate-free. -/
theorem copies_mem {α : Type*} [DecidableEq α] (xs ys : List α) (s : α) :
    (s ∈ (pairedCopies xs ys).1 → s ∈ xs ∧ s ∈ ys) ∧
    (s ∈ (pairedCopies xs ys).2.1 → s ∈ xs) ∧
    (s ∈ (pairedCopies xs ys).2.2 → s ∈ ys) := by
  let f (x : α) : ℝ := if x = s then 1 else 0
  let count (l : List α) : ℝ := (l.map f).sum
  have hc (l : List α) : 0 ≤ count l ∧ (0 < count l ↔ s ∈ l) := by
    induction l with
    | nil => simp [count]
    | cons x tail ih =>
      have add : count (x :: tail) = f x + count tail := by simp [count]
      by_cases hx : x = s
      · subst x
        have hf : f s = 1 := by simp [f]
        rw [add,hf]
        constructor
        · linarith [ih.1]
        · exact ⟨fun _ => by simp,fun _ => by linarith [ih.1]⟩
      · have hf : f x = 0 := by simp [f,hx]
        rw [add,hf,zero_add]
        simpa [Ne.symm hx] using ih
  have zsum (l : List α) : (l.map (fun _ => (0 : ℝ))).sum = 0 := by
    induction l with
    | nil => rfl
    | cons x tail ih => simp [ih]
  let m := (pairedCopies xs ys).1
  let r := (pairedCopies xs ys).2.1
  let l := (pairedCopies xs ys).2.2
  have left : count xs = count m + count r := by
    simpa only [sub_zero,zsum] using pairedCopies_signed f (fun _ => (0 : ℝ)) xs ys
  have both : count xs - count ys = count r - count l := by
    simpa only [sub_self,zsum,zero_add] using pairedCopies_signed f f xs ys
  have right : count ys = count m + count l := by linarith only [left,both]
  refine ⟨?_,?_,?_⟩
  · intro hm
    have h := (hc m).2.mpr hm
    exact ⟨(hc xs).2.mp (by linarith [left,(hc r).1]),
      (hc ys).2.mp (by linarith [right,(hc l).1])⟩
  · intro hr
    exact (hc xs).2.mp (by linarith [left,(hc r).2.mpr hr,(hc m).1])
  · intro hl
    exact (hc ys).2.mp (by linarith [right,(hc l).2.mpr hl,(hc m).1])

/-- The first disagreement tag remembers the side whose actual subtree was
taken. A common skip or take preserves this membership at the preceding node. -/
theorem tagged_leaf_mem {α : Type*} (R S : Bool → List α → Bool)
    (weight : α → ℝ) (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) :
    ∀ tag ∈ firstDisagreementLeaves R S weight pre positive mass remaining,
      tag.2 ∈ firstExitRetainedLeaves (if tag.1 then R else S)
        weight pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil => simp [firstDisagreementLeaves]
  | cons p ps ih =>
    intro tag htag
    rw [firstDisagreementLeaves,List.mem_append] at htag
    rcases htag with hskip | htake
    · rw [firstExitRetainedLeaves]
      exact List.mem_append_left _ (ih pre positive mass tag hskip)
    · by_cases hR : R (!positive) (p :: pre) = true
      · by_cases hS : S (!positive) (p :: pre) = true
        · simp only [if_pos hR,if_pos hS] at htake
          have hnext := ih (p :: pre) (!positive) (mass * weight p) tag htake
          have hgate : (if tag.1 then R else S) (!positive) (p :: pre) = true := by
            cases ht : tag.1 <;> simp [ht,hR,hS]
          rw [firstExitRetainedLeaves,if_pos hgate]
          exact List.mem_append_right _ hnext
        · simp only [if_pos hR,if_neg hS,List.mem_map] at htake
          obtain ⟨leaf,hm,rfl⟩ := htake
          change leaf ∈ firstExitRetainedLeaves R weight pre positive mass (p :: ps)
          rw [firstExitRetainedLeaves,if_pos hR]
          exact List.mem_append_right _ hm
      · by_cases hS : S (!positive) (p :: pre) = true
        · simp only [if_neg hR,if_pos hS,List.mem_map] at htake
          obtain ⟨leaf,hm,rfl⟩ := htake
          change leaf ∈ firstExitRetainedLeaves S weight pre positive mass (p :: ps)
          rw [firstExitRetainedLeaves,if_pos hS]
          exact List.mem_append_right _ hm
        · simp only [if_neg hR,if_neg hS,List.not_mem_nil] at htake

end
end ImbalancedChen.P4AOriginalFull87FrontierLeafMembership
