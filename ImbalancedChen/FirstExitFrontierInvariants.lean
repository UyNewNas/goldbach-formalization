import ImbalancedChen.FirstExitDepthSplice
import ImbalancedChen.RoughPrimeUniverse

/-!
# Actual histories and carriers at a retained-rank frontier

The selected history, sign and unsigned mass are inherited from the literal
parent recursion. At a positive selected rank the frontier stops immediately
after its last selection. Thus, in a decreasing prime universe, the remaining
list is exactly the same target-deleted, capped universe strictly below that
last selected prime. No carrier identity or continuation formula is assumed.
-/

namespace ImbalancedChen

noncomputable section

open scoped List

/-- At an attained rank the frontier contains the incoming state unchanged. -/
theorem firstExitDepthFrontier_of_rank_le_length
    {α : Type*} (k : ℕ) (parent : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ)
    (hk : k ≤ pre.length) :
    firstExitDepthFrontier k parent h pre positive mass remaining =
      [{selectedPrefix := pre, positive := positive, mass := mass, remaining := remaining}] := by
  cases remaining <;> simp [firstExitDepthFrontier, hk]

/-- Skipping the remaining labels turns an actual frontier state into an
actual retained terminal leaf of the same original tree. -/
theorem firstExitDepthFrontier_toLeaf_mem
    {α : Type*} (k : ℕ) (parent : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ)
    (state : FirstExitDepthState α)
    (hstate : state ∈ firstExitDepthFrontier k parent h pre positive mass remaining) :
    ({selected := state.selectedPrefix, positive := state.positive, mass := state.mass} :
      FirstExitLeaf α) ∈ firstExitRetainedLeaves parent h pre positive mass remaining := by
  induction remaining generalizing pre positive mass with
  | nil =>
      by_cases hk : k ≤ pre.length
      · simp only [firstExitDepthFrontier, if_pos hk, List.mem_singleton] at hstate
        subst state
        exact firstExitRetainedLeaves_skipAll_mem parent h pre [] positive mass
      · simp [firstExitDepthFrontier, hk] at hstate
  | cons p ps ih =>
      by_cases hk : k ≤ pre.length
      · rw [firstExitDepthFrontier_of_rank_le_length k parent h pre (p :: ps)
          positive mass hk, List.mem_singleton] at hstate
        subst state
        exact firstExitRetainedLeaves_skipAll_mem parent h pre (p :: ps) positive mass
      · by_cases hr : parent (!positive) (p :: pre) = true
        · rw [firstExitDepthFrontier, if_neg hk, if_pos hr, List.mem_append] at hstate
          rw [firstExitRetainedLeaves, if_pos hr, List.mem_append]
          rcases hstate with hskip | hselect
          · exact Or.inl (ih pre positive mass hskip)
          · exact Or.inr (ih (p :: pre) (!positive) (mass * h p) hselect)
        · rw [firstExitDepthFrontier, if_neg hk, if_neg hr, List.append_nil] at hstate
          rw [firstExitRetainedLeaves, if_neg hr, List.append_nil]
          exact ih pre positive mass hstate

/-- The remaining labels are included together with the selected history;
this retains their actual processing order, not just set containment. -/
theorem firstExitDepthFrontier_selected_remaining_sublist
    {α : Type*} (k : ℕ) (parent : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ)
    (state : FirstExitDepthState α)
    (hstate : state ∈ firstExitDepthFrontier k parent h pre positive mass remaining) :
    state.selectedPrefix.reverse ++ state.remaining <+ pre.reverse ++ remaining := by
  induction remaining generalizing pre positive mass with
  | nil =>
      by_cases hk : k ≤ pre.length
      · simp only [firstExitDepthFrontier, if_pos hk, List.mem_singleton] at hstate
        subst state
        exact List.Sublist.refl _
      · simp [firstExitDepthFrontier, hk] at hstate
  | cons p ps ih =>
      by_cases hk : k ≤ pre.length
      · rw [firstExitDepthFrontier_of_rank_le_length k parent h pre (p :: ps)
          positive mass hk, List.mem_singleton] at hstate
        subst state
        exact List.Sublist.refl _
      · have hskip (hs : state ∈ firstExitDepthFrontier k parent h pre positive mass ps) :
            state.selectedPrefix.reverse ++ state.remaining <+ pre.reverse ++ p :: ps :=
          (ih pre positive mass hs).trans
            ((List.Sublist.refl _).append (List.sublist_cons_self p ps))
        by_cases hr : parent (!positive) (p :: pre) = true
        · rw [firstExitDepthFrontier, if_neg hk, if_pos hr, List.mem_append] at hstate
          rcases hstate with hs | hs
          · exact hskip hs
          · simpa [List.reverse_cons, List.append_assoc] using
              ih (p :: pre) (!positive) (mass * h p) hs
        · rw [firstExitDepthFrontier, if_neg hk, if_neg hr, List.append_nil] at hstate
          exact hskip hstate

/-- A frontier reached from strictly below its rank has a last selected
label, and the unprocessed carrier is the exact suffix following that label. -/
theorem firstExitDepthFrontier_exists_last_selection
    {α : Type*} (k : ℕ) (parent : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ)
    (hpre : pre.length < k) (state : FirstExitDepthState α)
    (hstate : state ∈ firstExitDepthFrontier k parent h pre positive mass remaining) :
    ∃ before q tail, remaining = before ++ q :: state.remaining ∧
      state.selectedPrefix = q :: tail := by
  induction remaining generalizing pre positive mass with
  | nil => simp [firstExitDepthFrontier, Nat.not_le_of_gt hpre] at hstate
  | cons p ps ih =>
      have hk : ¬k ≤ pre.length := Nat.not_le_of_gt hpre
      have hskip (hs : state ∈ firstExitDepthFrontier k parent h pre positive mass ps) :
          ∃ before q tail, p :: ps = before ++ q :: state.remaining ∧
            state.selectedPrefix = q :: tail := by
        obtain ⟨before, q, tail, hrem, hsel⟩ := ih pre positive mass hpre hs
        exact ⟨p :: before, q, tail, by simp [hrem], hsel⟩
      by_cases hr : parent (!positive) (p :: pre) = true
      · rw [firstExitDepthFrontier, if_neg hk, if_pos hr, List.mem_append] at hstate
        rcases hstate with hs | hs
        · exact hskip hs
        · by_cases hnext : k ≤ (p :: pre).length
          · rw [firstExitDepthFrontier_of_rank_le_length k parent h (p :: pre) ps
              (!positive) (mass * h p) hnext, List.mem_singleton] at hs
            subst state
            exact ⟨[], p, pre, rfl, rfl⟩
          · obtain ⟨before, q, tail, hrem, hsel⟩ :=
              ih (p :: pre) (!positive) (mass * h p) (Nat.lt_of_not_ge hnext) hs
            exact ⟨p :: before, q, tail, by simp [hrem], hsel⟩
      · rw [firstExitDepthFrontier, if_neg hk, if_neg hr, List.append_nil] at hstate
        exact hskip hstate

theorem mem_firstExitDepthFrontier_mass_eq_selected_prod
    {α : Type*} (k : ℕ) (parent : Bool → List α → Bool) (h : α → ℝ)
    (carrier : List α) (state : FirstExitDepthState α)
    (hstate : state ∈ firstExitDepthFrontier k parent h [] true 1 carrier) :
    state.mass = (state.selectedPrefix.map h).prod := by
  exact firstExitRetainedLeaves_mass_eq_selected_prod parent h [] carrier true 1
    (by simp) _ (firstExitDepthFrontier_toLeaf_mem k parent h [] carrier true 1 state hstate)

theorem mem_firstExitDepthFrontier_positive_eq_evenListLength
    {α : Type*} (k : ℕ) (parent : Bool → List α → Bool) (h : α → ℝ)
    (carrier : List α) (state : FirstExitDepthState α)
    (hstate : state ∈ firstExitDepthFrontier k parent h [] true 1 carrier) :
    state.positive = evenListLength state.selectedPrefix := by
  exact firstExitRetainedLeaves_positive_eq_evenListLength parent h [] carrier true 1
    rfl _ (firstExitDepthFrontier_toLeaf_mem k parent h [] carrier true 1 state hstate)

theorem mem_firstExitDepthFrontier_selected_reverse_sublist
    {α : Type*} (k : ℕ) (parent : Bool → List α → Bool) (h : α → ℝ)
    (carrier : List α) (state : FirstExitDepthState α)
    (hstate : state ∈ firstExitDepthFrontier k parent h [] true 1 carrier) :
    state.selectedPrefix.reverse <+ carrier := by
  simpa using firstExitRetainedLeaves_selected_reverse_sublist parent h [] carrier true 1
    _ (firstExitDepthFrontier_toLeaf_mem k parent h [] carrier true 1 state hstate)

/-- Every previously selected label is strictly larger than every remaining
label when the original carrier is strictly decreasing. -/
theorem mem_firstExitDepthFrontier_selected_gt_remaining
    (k : ℕ) (parent : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (hcarrier : carrier.Pairwise (· > ·))
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k parent h [] true 1 carrier) :
    ∀ p ∈ state.selectedPrefix, ∀ q ∈ state.remaining, q < p := by
  have hsub : state.selectedPrefix.reverse ++ state.remaining <+ carrier := by
    simpa using firstExitDepthFrontier_selected_remaining_sublist
      k parent h [] carrier true 1 state hstate
  have hpair := List.pairwise_append.mp (hcarrier.sublist hsub)
  intro p hp q hq
  exact hpair.2.2 p (by simpa using hp) q hq

/-- In a decreasing list, the suffix immediately after a label contains
exactly all labels strictly below it, in the original order. -/
theorem decreasingList_suffix_eq_filter_lt (before after : List ℕ) (q : ℕ)
    (hcarrier : (before ++ q :: after).Pairwise (· > ·)) :
    after = (before ++ q :: after).filter (fun p => p < q) := by
  have hp := List.pairwise_append.mp hcarrier
  have hbefore : before.filter (fun p => p < q) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hpmem
    have hqp : q < p := hp.2.2 p hpmem q (by simp)
    simpa using (show ¬p < q by omega)
  have hafter : after.filter (fun p => p < q) = after := by
    apply List.filter_eq_self.mpr
    intro p hpmem
    exact decide_eq_true ((List.pairwise_cons.mp hp.2.1).1 p hpmem)
  simp [List.filter_append, hbefore, hafter]

/-- The last selected label and the exact smaller-label suffix are recovered
from the actual root frontier, rather than supplied as hypotheses. -/
theorem mem_firstExitDepthFrontier_remaining_eq_filter
    (k : ℕ) (hk : 0 < k) (parent : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (hcarrier : carrier.Pairwise (· > ·))
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k parent h [] true 1 carrier) :
    ∃ q tail, state.selectedPrefix = q :: tail ∧ q ∈ carrier ∧
      state.remaining = carrier.filter (fun p => p < q) := by
  obtain ⟨before, q, tail, hrem, hsel⟩ :=
    firstExitDepthFrontier_exists_last_selection k parent h [] carrier true 1 hk state hstate
  refine ⟨q, tail, hsel, ?_, ?_⟩
  · simp [hrem]
  · rw [hrem] at hcarrier ⊢
    exact decreasingList_suffix_eq_filter_lt before state.remaining q hcarrier

/-- Restricting the actual capped carrier below one of its primes preserves
the target exclusions, strict endpoint, and decreasing enumeration. -/
theorem roughPrimeUniverse_filter_lt_eq
    (N cap : ℕ) (w z : ℝ) (q : ℕ) (hq : (q : ℝ) ≤ z) :
    (roughPrimeUniverse N cap w z).filter (fun p => p < q) =
      roughPrimeUniverse N cap w (q : ℝ) := by
  classical
  have hgt := (roughPrimeUniverse_pairwise_gt N cap w z).filter (fun p => p < q)
  have hset : ((roughPrimeUniverse N cap w z).filter (fun p => p < q)).toFinset =
      roughPrimeFinset N cap w (q : ℝ) := by
    ext p
    simp only [List.mem_toFinset, List.mem_filter, mem_roughPrimeUniverse,
      decide_eq_true_eq, mem_roughPrimeFinset]
    constructor
    · rintro ⟨hp, hpq⟩
      exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, by exact_mod_cast hpq⟩
    · intro hp
      exact ⟨⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.trans_le hq⟩,
        by exact_mod_cast hp.2.2.2.2⟩
  unfold roughPrimeUniverse
  rw [← hset]
  exact ((List.toFinset_sort (r := (· ≥ ·)) hgt.nodup).mpr
    (hgt.imp fun h => h.le)).symm

/-- An actual prime frontier has the literal strict residual prime carrier
below its last chosen prime. This also works with a truncated enumeration cap. -/
theorem mem_firstExitDepthFrontier_roughPrime_remaining
    (k : ℕ) (hk : 0 < k) (parent : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (N cap : ℕ) (w z : ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k parent h [] true 1
      (roughPrimeUniverse N cap w z)) :
    ∃ q tail, state.selectedPrefix = q :: tail ∧
      q ∈ roughPrimeUniverse N cap w z ∧
      state.remaining = roughPrimeUniverse N cap w (q : ℝ) := by
  obtain ⟨q, tail, hsel, hq, hrem⟩ := mem_firstExitDepthFrontier_remaining_eq_filter
    k hk parent h (roughPrimeUniverse N cap w z)
    (roughPrimeUniverse_pairwise_gt N cap w z) state hstate
  exact ⟨q, tail, hsel, hq, hrem.trans
    (roughPrimeUniverse_filter_lt_eq N cap w z q (mem_roughPrimeUniverse_upper hq).le)⟩

end

end ImbalancedChen
