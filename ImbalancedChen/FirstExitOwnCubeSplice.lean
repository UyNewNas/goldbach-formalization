import ImbalancedChen.FirstExitDepthSplice

/-!
# Exact replacement at a selected prefix's own admission test

To change the test at rank `r + 1`, stop at the common parent frontier of
rank `r`. Every possible next selected label is then enumerated, including
labels whose branches the old policy rejects. Each candidate records the
whole inherited history, the flipped sign, the multiplied mass, and the
literal unprocessed suffix.

The new and old admission indicators remain attached to their respective
continuations. Those continuations need not agree. This is a finite exact
identity, without sign, primality, ordering or analytic assumptions.
-/

namespace ImbalancedChen

noncomputable section

/-- All possible next selections after skipping any number of labels.
Enumeration is independent of both old and new admission policies. -/
def firstExitNextSelectionCandidates {α : Type*} (h : α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ) :
    List α → List (FirstExitDepthState α)
  | [] => []
  | q :: qs =>
      {selectedPrefix := q :: pre, positive := !positive,
        mass := mass * h q, remaining := qs} ::
      firstExitNextSelectionCandidates h pre positive mass qs

/-- Every candidate is one more selected label, regardless of how many
unselected labels precede it in the carrier. -/
theorem firstExitNextSelectionCandidates_selected_length
    {α : Type*} (h : α → ℝ) (pre remaining : List α)
    (positive : Bool) (mass : ℝ) (state : FirstExitDepthState α)
    (hstate : state ∈ firstExitNextSelectionCandidates h pre positive mass remaining) :
    state.selectedPrefix.length = pre.length + 1 := by
  induction remaining with
  | nil => simp [firstExitNextSelectionCandidates] at hstate
  | cons q qs ih =>
      simp only [firstExitNextSelectionCandidates, List.mem_cons] at hstate
      rcases hstate with hfirst | hlater
      · subst state
        rfl
      · exact ih hlater

/-- The existing tree polynomial is its skip-all value plus its admitted
next-selection continuations. The histories and suffixes are literal data. -/
theorem firstExitRetainedPolynomial_eq_skipAll_add_nextSelections
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial retained h pre positive mass remaining =
      signedTreeCoefficient positive mass +
        ((firstExitNextSelectionCandidates h pre positive mass remaining).map
          (fun state => if retained state.positive state.selectedPrefix = true then
            firstExitRetainedPolynomial retained h state.selectedPrefix state.positive
              state.mass state.remaining else 0)).sum := by
  induction remaining with
  | nil => simp [firstExitRetainedPolynomial, firstExitNextSelectionCandidates]
  | cons q qs ih =>
      simp only [firstExitRetainedPolynomial, firstExitNextSelectionCandidates,
        List.map_cons, List.sum_cons]
      rw [ih]
      ring

/-- The skip-all term cancels, but both admission indicators and both
policy-specific continuations remain visible in the exact difference. -/
theorem firstExitRetainedPolynomial_sub_eq_nextSelection_sum
    {α : Type*} (newPolicy oldPolicy : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial newPolicy h pre positive mass remaining -
      firstExitRetainedPolynomial oldPolicy h pre positive mass remaining =
        ((firstExitNextSelectionCandidates h pre positive mass remaining).map
          (fun state =>
            (if newPolicy state.positive state.selectedPrefix = true then
              firstExitRetainedPolynomial newPolicy h state.selectedPrefix state.positive
                state.mass state.remaining else 0) -
            (if oldPolicy state.positive state.selectedPrefix = true then
              firstExitRetainedPolynomial oldPolicy h state.selectedPrefix state.positive
                state.mass state.remaining else 0))).sum := by
  have hsum (states : List (FirstExitDepthState α)) :
      (states.map (fun state => if newPolicy state.positive state.selectedPrefix = true then
        firstExitRetainedPolynomial newPolicy h state.selectedPrefix state.positive
          state.mass state.remaining else 0)).sum -
      (states.map (fun state => if oldPolicy state.positive state.selectedPrefix = true then
        firstExitRetainedPolynomial oldPolicy h state.selectedPrefix state.positive
          state.mass state.remaining else 0)).sum =
      (states.map (fun state =>
        (if newPolicy state.positive state.selectedPrefix = true then
          firstExitRetainedPolynomial newPolicy h state.selectedPrefix state.positive
            state.mass state.remaining else 0) -
        (if oldPolicy state.positive state.selectedPrefix = true then
          firstExitRetainedPolynomial oldPolicy h state.selectedPrefix state.positive
            state.mass state.remaining else 0))).sum := by
    induction states with
    | nil => simp
    | cons state states ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [← ih]
        ring
  rw [firstExitRetainedPolynomial_eq_skipAll_add_nextSelections,
    firstExitRetainedPolynomial_eq_skipAll_add_nextSelections,
    add_sub_add_left_eq_sub]
  exact hsum _

/-- Both policies inherit exactly the same parent decisions through rank
`r`. Every branch ending before that rank cancels through the shared terminal
polynomial; each frontier state's skip-all term then cancels separately.
The remaining terms include every new-admitted/old-rejected candidate. -/
theorem firstExitRetainedPolynomial_depthSplice_sub_eq_nextSelection_sum
    {α : Type*} (r : ℕ) (parent newPolicy oldPolicy : Bool → List α → Bool)
    (h : α → ℝ) (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial (firstExitDepthSplicePolicy r parent newPolicy)
        h pre positive mass remaining -
      firstExitRetainedPolynomial (firstExitDepthSplicePolicy r parent oldPolicy)
        h pre positive mass remaining =
      ((firstExitDepthFrontier r parent h pre positive mass remaining).map
        (fun frontier =>
          ((firstExitNextSelectionCandidates h frontier.selectedPrefix
            frontier.positive frontier.mass frontier.remaining).map
              (fun candidate =>
                (if newPolicy candidate.positive candidate.selectedPrefix = true then
                  firstExitRetainedPolynomial newPolicy h candidate.selectedPrefix
                    candidate.positive candidate.mass candidate.remaining else 0) -
                (if oldPolicy candidate.positive candidate.selectedPrefix = true then
                  firstExitRetainedPolynomial oldPolicy h candidate.selectedPrefix
                    candidate.positive candidate.mass candidate.remaining else 0))).sum)).sum := by
  have hsum (states : List (FirstExitDepthState α)) :
      (states.map (fun state => firstExitRetainedPolynomial newPolicy h state.selectedPrefix
        state.positive state.mass state.remaining)).sum -
      (states.map (fun state => firstExitRetainedPolynomial oldPolicy h state.selectedPrefix
        state.positive state.mass state.remaining)).sum =
      (states.map (fun state => firstExitRetainedPolynomial newPolicy h state.selectedPrefix
        state.positive state.mass state.remaining -
          firstExitRetainedPolynomial oldPolicy h state.selectedPrefix
            state.positive state.mass state.remaining)).sum := by
    induction states with
    | nil => simp
    | cons state states ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [← ih]
        ring
  rw [firstExitRetainedPolynomial_depthSplice_eq_terminal_add_frontier,
    firstExitRetainedPolynomial_depthSplice_eq_terminal_add_frontier,
    add_sub_add_left_eq_sub, hsum]
  simp_rw [firstExitRetainedPolynomial_sub_eq_nextSelection_sum]

/-- Root form for changing rank `r + 1`'s own test and its later policy.
The common frontier is the parent's retained rank `r`, never the old rank
`r + 1` frontier, so restored branches cannot be lost. -/
theorem firstExitRetainedPolynomial_ownCubeSplice_root_sub_eq
    {α : Type*} (r : ℕ) (parent newPolicy oldPolicy : Bool → List α → Bool)
    (h : α → ℝ) (carrier : List α) :
    firstExitRetainedPolynomial (firstExitDepthSplicePolicy r parent newPolicy)
        h [] true 1 carrier -
      firstExitRetainedPolynomial (firstExitDepthSplicePolicy r parent oldPolicy)
        h [] true 1 carrier =
      ((firstExitDepthFrontier r parent h [] true 1 carrier).map
        (fun frontier =>
          ((firstExitNextSelectionCandidates h frontier.selectedPrefix
            frontier.positive frontier.mass frontier.remaining).map
              (fun candidate =>
                (if newPolicy candidate.positive candidate.selectedPrefix = true then
                  firstExitRetainedPolynomial newPolicy h candidate.selectedPrefix
                    candidate.positive candidate.mass candidate.remaining else 0) -
                (if oldPolicy candidate.positive candidate.selectedPrefix = true then
                  firstExitRetainedPolynomial oldPolicy h candidate.selectedPrefix
                    candidate.positive candidate.mass candidate.remaining else 0))).sum)).sum :=
  firstExitRetainedPolynomial_depthSplice_sub_eq_nextSelection_sum
    r parent newPolicy oldPolicy h [] carrier true 1

end

end ImbalancedChen
