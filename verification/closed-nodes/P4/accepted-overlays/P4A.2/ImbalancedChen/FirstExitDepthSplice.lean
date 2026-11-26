import ImbalancedChen.FirstExitTree

/-!
# Exact replacement below a retained selected-rank frontier

The parent policy decides every selection through rank `k`, including the
test that admits rank `k` itself. Only subsequent selections use the
replacement policy. A frontier state stores the actual selected history,
incoming sign, unsigned mass and the unprocessed carrier. Its continuation
may inspect the entire inherited history.

The stopped terminal polynomial records branches that exhaust the carrier
before reaching rank `k`. These branches are identical for both policies
and cancel explicitly in the final difference identity. No positivity,
prime-carrier or analytic hypothesis is used.

This is an update after a retained rank, such as after a retained eighth
prefix. It does not move or replace that prefix's own admission test. In
particular, a fourth-own-cube update made before the fourth test requires
a different splice location or an additional before-test identity.
-/

namespace ImbalancedChen

noncomputable section

/-- The exact state of a retained branch when the selected rank is reached. -/
@[ext] structure FirstExitDepthState (α : Type*) where
  selectedPrefix : List α
  positive : Bool
  mass : ℝ
  remaining : List α

/-- Parent tests admit ranks through `k`; later tests use the replacement. -/
def firstExitDepthSplicePolicy {α : Type*} (k : ℕ)
    (parent replacement : Bool → List α → Bool)
    (positive : Bool) (selectedPrefix : List α) : Bool :=
  if selectedPrefix.length ≤ k then parent positive selectedPrefix
  else replacement positive selectedPrefix

@[simp] theorem firstExitDepthSplicePolicy_self {α : Type*} (k : ℕ)
    (parent : Bool → List α → Bool) :
    firstExitDepthSplicePolicy k parent parent = parent := by
  funext positive selectedPrefix
  simp [firstExitDepthSplicePolicy]

/-- The finite parent frontier. Reaching rank `k` stops the scan immediately,
so the remaining smaller labels are retained as part of the state. -/
noncomputable def firstExitDepthFrontier {α : Type*} (k : ℕ)
    (parent : Bool → List α → Bool) (h : α → ℝ)
    (selectedPrefix : List α) (positive : Bool) (mass : ℝ) :
    List α → List (FirstExitDepthState α)
  | [] =>
      if k ≤ selectedPrefix.length then
        [{selectedPrefix := selectedPrefix, positive := positive, mass := mass, remaining := []}]
      else []
  | p :: ps =>
      if k ≤ selectedPrefix.length then
        [{selectedPrefix := selectedPrefix, positive := positive, mass := mass,
          remaining := p :: ps}]
      else
        firstExitDepthFrontier k parent h selectedPrefix positive mass ps ++
          if parent (Bool.not positive) (p :: selectedPrefix) = true then
            firstExitDepthFrontier k parent h (p :: selectedPrefix) (Bool.not positive)
              (mass * h p) ps
          else []

/-- Signed terminal values of branches ending before the frontier. Branches
that reach the frontier contribute zero here and are continued separately. -/
noncomputable def firstExitDepthTerminalPolynomial {α : Type*} (k : ℕ)
    (parent : Bool → List α → Bool) (h : α → ℝ)
    (selectedPrefix : List α) (positive : Bool) (mass : ℝ) : List α → ℝ
  | [] => if k ≤ selectedPrefix.length then 0 else signedTreeCoefficient positive mass
  | p :: ps =>
      if k ≤ selectedPrefix.length then 0
      else
        firstExitDepthTerminalPolynomial k parent h selectedPrefix positive mass ps +
          if parent (Bool.not positive) (p :: selectedPrefix) = true then
            firstExitDepthTerminalPolynomial k parent h (p :: selectedPrefix)
              (Bool.not positive) (mass * h p) ps
          else 0

/-- Every returned state has exactly the selected rank, provided the scan
starts at or before that rank. No exhausted lower-rank branch is returned. -/
theorem firstExitDepthFrontier_selected_length
    {α : Type*} (k : ℕ) (parent : Bool → List α → Bool) (h : α → ℝ)
    (selectedPrefix remaining : List α) (positive : Bool) (mass : ℝ)
    (hpre : selectedPrefix.length ≤ k) :
    ∀ state ∈ firstExitDepthFrontier k parent h selectedPrefix positive mass remaining,
      state.selectedPrefix.length = k := by
  induction remaining generalizing selectedPrefix positive mass with
  | nil =>
      intro state hstate
      by_cases hk : k ≤ selectedPrefix.length
      · simp only [firstExitDepthFrontier, if_pos hk, List.mem_singleton] at hstate
        subst state
        exact Nat.le_antisymm hpre hk
      · simp [firstExitDepthFrontier, hk] at hstate
  | cons p ps ih =>
      intro state hstate
      by_cases hk : k ≤ selectedPrefix.length
      · simp only [firstExitDepthFrontier, if_pos hk, List.mem_singleton] at hstate
        subst state
        exact Nat.le_antisymm hpre hk
      · have hnext : (p :: selectedPrefix).length ≤ k := by
          simpa only [List.length_cons] using Nat.succ_le_of_lt (Nat.lt_of_not_ge hk)
        by_cases hr : parent (Bool.not positive) (p :: selectedPrefix) = true
        · rw [firstExitDepthFrontier, if_neg hk, if_pos hr, List.mem_append] at hstate
          rcases hstate with hskip | hselect
          · exact ih selectedPrefix positive mass hpre state hskip
          · exact ih (p :: selectedPrefix) (Bool.not positive) (mass * h p) hnext state hselect
        · rw [firstExitDepthFrontier, if_neg hk, if_neg hr, List.append_nil] at hstate
          exact ih selectedPrefix positive mass hpre state hstate

/-- At or beyond the frontier, all future selected prefixes use the
replacement policy; the existing history and incoming sign are preserved. -/
theorem firstExitRetainedPolynomial_depthSplice_eq_of_rank_le_length
    {α : Type*} (k : ℕ) (parent replacement : Bool → List α → Bool) (h : α → ℝ)
    (selectedPrefix remaining : List α) (positive : Bool) (mass : ℝ)
    (hk : k ≤ selectedPrefix.length) :
    firstExitRetainedPolynomial (firstExitDepthSplicePolicy k parent replacement)
        h selectedPrefix positive mass remaining =
      firstExitRetainedPolynomial replacement h selectedPrefix positive mass remaining := by
  induction remaining generalizing selectedPrefix positive mass with
  | nil => rfl
  | cons p ps ih =>
      have hnext : k < (p :: selectedPrefix).length := by
        simpa only [List.length_cons] using Nat.lt_succ_of_le hk
      simp only [firstExitRetainedPolynomial, firstExitDepthSplicePolicy,
        if_neg (Nat.not_le_of_gt hnext)]
      rw [ih selectedPrefix positive mass hk,
        ih (p :: selectedPrefix) (Bool.not positive) (mass * h p) hnext.le]

/-- Exact stopped decomposition of the existing retained polynomial.
Only the same parent frontier is used, independently of the replacement. -/
theorem firstExitRetainedPolynomial_depthSplice_eq_terminal_add_frontier
    {α : Type*} (k : ℕ) (parent replacement : Bool → List α → Bool) (h : α → ℝ)
    (selectedPrefix remaining : List α) (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial (firstExitDepthSplicePolicy k parent replacement)
        h selectedPrefix positive mass remaining =
      firstExitDepthTerminalPolynomial k parent h selectedPrefix positive mass remaining +
        ((firstExitDepthFrontier k parent h selectedPrefix positive mass remaining).map
          (fun state => firstExitRetainedPolynomial replacement h state.selectedPrefix
            state.positive state.mass state.remaining)).sum := by
  induction remaining generalizing selectedPrefix positive mass with
  | nil =>
      by_cases hk : k ≤ selectedPrefix.length <;>
        simp [firstExitRetainedPolynomial, firstExitDepthTerminalPolynomial,
          firstExitDepthFrontier, hk]
  | cons p ps ih =>
      by_cases hk : k ≤ selectedPrefix.length
      · rw [firstExitRetainedPolynomial_depthSplice_eq_of_rank_le_length
          k parent replacement h selectedPrefix (p :: ps) positive mass hk]
        simp only [firstExitDepthTerminalPolynomial, firstExitDepthFrontier, if_pos hk,
          List.map_singleton, List.sum_singleton, zero_add]
      · have hnext : (p :: selectedPrefix).length ≤ k := by
          simpa only [List.length_cons] using Nat.succ_le_of_lt (Nat.lt_of_not_ge hk)
        have htest : firstExitDepthSplicePolicy k parent replacement
            (Bool.not positive) (p :: selectedPrefix) =
          parent (Bool.not positive) (p :: selectedPrefix) := by
          simp only [firstExitDepthSplicePolicy, if_pos hnext]
        simp only [firstExitRetainedPolynomial, htest, firstExitDepthTerminalPolynomial,
          firstExitDepthFrontier, if_neg hk]
        by_cases hr : parent (Bool.not positive) (p :: selectedPrefix) = true
        · rw [if_pos hr, if_pos hr, if_pos hr, List.map_append, List.sum_append,
            ih selectedPrefix positive mass,
            ih (p :: selectedPrefix) (Bool.not positive) (mass * h p)]
          ring
        · simp only [if_neg hr, add_zero, List.append_nil]
          exact ih selectedPrefix positive mass

/-- The parent polynomial has the identical stopped terminal term and the
identical frontier, continued with its original policy. -/
theorem firstExitRetainedPolynomial_eq_terminal_add_frontier
    {α : Type*} (k : ℕ) (parent : Bool → List α → Bool) (h : α → ℝ)
    (selectedPrefix remaining : List α) (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial parent h selectedPrefix positive mass remaining =
      firstExitDepthTerminalPolynomial k parent h selectedPrefix positive mass remaining +
        ((firstExitDepthFrontier k parent h selectedPrefix positive mass remaining).map
          (fun state => firstExitRetainedPolynomial parent h state.selectedPrefix
            state.positive state.mass state.remaining)).sum := by
  simpa only [firstExitDepthSplicePolicy_self] using
    firstExitRetainedPolynomial_depthSplice_eq_terminal_add_frontier
      k parent parent h selectedPrefix remaining positive mass

/-- Exact replacement difference below a fixed selected-rank frontier.
Branches ending before the frontier cancel through their common explicit
terminal polynomial. Each remaining summand uses the actual parent state. -/
theorem firstExitRetainedPolynomial_depthSplice_sub_eq_frontier_sum
    {α : Type*} (k : ℕ) (parent replacement : Bool → List α → Bool) (h : α → ℝ)
    (selectedPrefix remaining : List α) (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial (firstExitDepthSplicePolicy k parent replacement)
        h selectedPrefix positive mass remaining -
      firstExitRetainedPolynomial parent h selectedPrefix positive mass remaining =
        ((firstExitDepthFrontier k parent h selectedPrefix positive mass remaining).map
          (fun state => firstExitRetainedPolynomial replacement h state.selectedPrefix
              state.positive state.mass state.remaining -
            firstExitRetainedPolynomial parent h state.selectedPrefix
              state.positive state.mass state.remaining)).sum := by
  have hsum (states : List (FirstExitDepthState α)) :
      (states.map (fun state => firstExitRetainedPolynomial replacement h state.selectedPrefix
          state.positive state.mass state.remaining)).sum -
        (states.map (fun state => firstExitRetainedPolynomial parent h state.selectedPrefix
          state.positive state.mass state.remaining)).sum =
        (states.map (fun state => firstExitRetainedPolynomial replacement h state.selectedPrefix
            state.positive state.mass state.remaining -
          firstExitRetainedPolynomial parent h state.selectedPrefix
            state.positive state.mass state.remaining)).sum := by
    induction states with
    | nil => simp
    | cons state states ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [← ih]
        ring
  rw [firstExitRetainedPolynomial_depthSplice_eq_terminal_add_frontier,
    firstExitRetainedPolynomial_eq_terminal_add_frontier k parent h
      selectedPrefix remaining positive mass]
  rw [add_sub_add_left_eq_sub]
  exact hsum _

/-- Root form of the exact replacement identity, with no caller-supplied
frontier or continuation identity assumptions. -/
theorem firstExitRetainedPolynomial_depthSplice_root_sub_eq_frontier_sum
    {α : Type*} (k : ℕ) (parent replacement : Bool → List α → Bool)
    (h : α → ℝ) (carrier : List α) :
    firstExitRetainedPolynomial (firstExitDepthSplicePolicy k parent replacement)
        h [] true 1 carrier - firstExitRetainedPolynomial parent h [] true 1 carrier =
      ((firstExitDepthFrontier k parent h [] true 1 carrier).map
        (fun state => firstExitRetainedPolynomial replacement h state.selectedPrefix
            state.positive state.mass state.remaining -
          firstExitRetainedPolynomial parent h state.selectedPrefix
            state.positive state.mass state.remaining)).sum :=
  firstExitRetainedPolynomial_depthSplice_sub_eq_frontier_sum
    k parent replacement h [] carrier true 1

end

end ImbalancedChen
