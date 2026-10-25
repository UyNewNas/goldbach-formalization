import ImbalancedChen.P1SignedExitPartition
import ImbalancedChen.FirstExitFrontierInvariants

/-!
Strict triangular support of the actual signed first-exit recursion.

The policy and prime weight are fixed throughout every continuation. An
edge means membership in `p1SignedExitStates`, with the inherited history,
sign, mass and remaining carrier supplied literally to that recursion.
The finite path bound uses no analytic density or distribution premise.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

/-- Selected history and unprocessed labels keep their joint processing
order at a rejected selection, including all earlier skipped labels. -/
theorem p0SignedExit_selected_remaining_sublist
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (pre carrier : List α) (positive : Bool) (mass : ℝ)
    (state : FirstExitDepthState α)
    (hstate : state ∈ p1SignedExitStates retained h pre positive mass carrier) :
    state.selectedPrefix.reverse ++ state.remaining <+ pre.reverse ++ carrier := by
  induction carrier generalizing pre positive mass with
  | nil => simp [p1SignedExitStates] at hstate
  | cons p ps ih =>
      have hskip (hs : state ∈ p1SignedExitStates retained h pre positive mass ps) :
          state.selectedPrefix.reverse ++ state.remaining <+ pre.reverse ++ p :: ps :=
        (ih pre positive mass hs).trans
          ((List.Sublist.refl _).append (List.sublist_cons_self p ps))
      by_cases ht : retained (!positive) (p :: pre) = true
      · rw [p1SignedExitStates, if_pos ht, List.mem_append] at hstate
        rcases hstate with hs | hs
        · exact hskip hs
        · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
            ih (p :: pre) (!positive) (mass * h p) hs
      · rw [p1SignedExitStates, if_neg ht, List.mem_append] at hstate
        rcases hstate with hs | hs
        · exact hskip hs
        · simp only [List.mem_singleton] at hs
          subst state
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
            (List.Sublist.refl (pre.reverse ++ p :: ps))

/-- An actual signed exit preserves the strict triangular prime domain:
every selected prime is larger than every unprocessed prime. -/
theorem p0SignedExit_selected_gt_remaining
    (retained : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (pre carrier : List ℕ) (positive : Bool) (mass : ℝ)
    (hsort : (pre.reverse ++ carrier).Pairwise (· > ·))
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ p1SignedExitStates retained h pre positive mass carrier) :
    (state.selectedPrefix.reverse ++ state.remaining).Pairwise (· > ·) ∧
      ∀ p ∈ state.selectedPrefix, ∀ q ∈ state.remaining, q < p := by
  have hs := hsort.sublist
    (p0SignedExit_selected_remaining_sublist retained h pre carrier positive mass state hstate)
  refine ⟨hs, ?_⟩
  have happ := List.pairwise_append.mp hs
  intro p hp q hq
  exact happ.2.2 p (by simpa using hp) q hq

/-- The rejected prime has exactly its original strict smaller-prime
carrier, retaining the target exclusions and the original lower cutoff. -/
theorem p0SignedExit_roughPrime_remaining
    (retained : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (N cap : ℕ) (w z : ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ p1SignedExitStates retained h [] true 1
      (roughPrimeUniverse N cap w z)) :
    ∃ q tail, state.selectedPrefix = q :: tail ∧
      q ∈ roughPrimeUniverse N cap w z ∧
      state.remaining = roughPrimeUniverse N cap w (q : ℝ) := by
  obtain ⟨before, q, tail, hcarrier, hsel⟩ :=
    p1_mem_exitStates_carrier_decomposition retained h []
      (roughPrimeUniverse N cap w z) true 1 state hstate
  have hsort := roughPrimeUniverse_pairwise_gt N cap w z
  have hq : q ∈ roughPrimeUniverse N cap w z := by simp [hcarrier]
  have hrem : state.remaining = (roughPrimeUniverse N cap w z).filter (fun p => p < q) := by
    rw [hcarrier] at hsort ⊢
    exact decreasingList_suffix_eq_filter_lt before state.remaining q hsort
  refine ⟨q, tail, hsel, hq, ?_⟩
  rw [hrem, roughPrimeUniverse_filter_lt_eq N cap w z q
    (mem_roughPrimeUniverse_upper hq).le]

/-- A continuation edge is the actual same-policy signed-exit call from
the complete inherited state. It does not reset its prefix, sign or mass. -/
def P0CausalExitEdge {α : Type*}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (source target : FirstExitDepthState α) : Prop :=
  target ∈ p1SignedExitStates retained h source.selectedPrefix source.positive
    source.mass source.remaining

/-- Both triangular directions follow from the literal finite recursion,
even with repeated labels or signed weights. -/
theorem p0CausalExitEdge_strict {α : Type*}
    {retained : Bool → List α → Bool} {h : α → ℝ}
    {source target : FirstExitDepthState α}
    (hedge : P0CausalExitEdge retained h source target) :
    source.selectedPrefix.length < target.selectedPrefix.length ∧
      target.remaining.length < source.remaining.length := by
  have hr := p1_mem_exitStates_rank_bound retained h source.selectedPrefix source.remaining
    source.positive source.mass target hedge
  exact ⟨hr.1, by omega⟩

/-- A finite chain records actual continuation calls; the length counts
edges, so zero edges preserve the entire initial state. -/
inductive P0CausalExitPath {α : Type*}
    (retained : Bool → List α → Bool) (h : α → ℝ) :
    ℕ → FirstExitDepthState α → FirstExitDepthState α → Prop
  | nil (state) : P0CausalExitPath retained h 0 state state
  | cons {k source middle target}
      (edge : P0CausalExitEdge retained h source middle)
      (tail : P0CausalExitPath retained h k middle target) :
      P0CausalExitPath retained h (k + 1) source target

/-- Each edge spends at least one unprocessed label and gains at least
one selected rank. This quantitatively excludes arbitrarily long chains. -/
theorem p0CausalExitPath_length_budget {α : Type*}
    {retained : Bool → List α → Bool} {h : α → ℝ}
    {k : ℕ} {source target : FirstExitDepthState α}
    (hpath : P0CausalExitPath retained h k source target) :
    source.selectedPrefix.length + k ≤ target.selectedPrefix.length ∧
      target.remaining.length + k ≤ source.remaining.length := by
  induction hpath with
  | nil state => simp
  | @cons k source middle target edge tail ih =>
      have he := p0CausalExitEdge_strict edge
      constructor <;> omega

/-- A positive-length same-policy continuation cannot return to the same
state. The strict direction is determined by its actual remaining carrier. -/
theorem p0CausalExitPath_no_cycle {α : Type*}
    {retained : Bool → List α → Bool} {h : α → ℝ}
    {k : ℕ} (hk : 0 < k) (state : FirstExitDepthState α) :
    ¬ P0CausalExitPath retained h k state state := by
  intro hp
  have hb := (p0CausalExitPath_length_budget hp).2
  omega

/-- A continuation path from an actual original root exit has fewer
edges than original prime labels, independently of its policy or weights. -/
theorem p0CausalExitPath_root_length_lt {α : Type*}
    (retained : Bool → List α → Bool) (h : α → ℝ) (carrier : List α)
    {source target : FirstExitDepthState α} {k : ℕ}
    (hroot : source ∈ p1SignedExitStates retained h [] true 1 carrier)
    (hpath : P0CausalExitPath retained h k source target) : k < carrier.length := by
  have hr := p1_mem_exitStates_rank_bound retained h [] carrier true 1 source hroot
  have hp := (p0CausalExitPath_length_budget hpath).2
  simp only [List.length_nil, Nat.zero_add] at hr
  omega

/-- Complete processing-order support is inherited along an entire
continuation path, before any passage to logarithmic coordinates. -/
theorem p0CausalExitPath_sublist {α : Type*}
    {retained : Bool → List α → Bool} {h : α → ℝ}
    {k : ℕ} {source target : FirstExitDepthState α}
    (hpath : P0CausalExitPath retained h k source target) :
    target.selectedPrefix.reverse ++ target.remaining <+
      source.selectedPrefix.reverse ++ source.remaining := by
  induction hpath with
  | nil state => exact List.Sublist.refl _
  | @cons k source middle target edge tail ih =>
      exact ih.trans (p0SignedExit_selected_remaining_sublist retained h
        source.selectedPrefix source.remaining source.positive source.mass middle edge)

/-- All future states remain on the same strict ordered prime triangle;
in particular no continuation can cross an earlier selected prime. -/
theorem p0CausalExitPath_ordered
    {retained : Bool → List ℕ → Bool} {h : ℕ → ℝ}
    {k : ℕ} {source target : FirstExitDepthState ℕ}
    (hsort : (source.selectedPrefix.reverse ++ source.remaining).Pairwise (· > ·))
    (hpath : P0CausalExitPath retained h k source target) :
    (target.selectedPrefix.reverse ++ target.remaining).Pairwise (· > ·) ∧
      ∀ p ∈ target.selectedPrefix, ∀ q ∈ target.remaining, q < p := by
  have hs := hsort.sublist (p0CausalExitPath_sublist hpath)
  refine ⟨hs, ?_⟩
  have happ := List.pairwise_append.mp hs
  intro p hp q hq
  exact happ.2.2 p (by simpa using hp) q hq

/-- A finite weighted transition matrix has support only on actual
continuation edges of this one policy and this one prime weight. Coefficients
may be signed; triangular support alone drives the nilpotence theorem. -/
def p0CausalExitKernel {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (states : Fin n → FirstExitDepthState α) (coefficient : Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  if P0CausalExitEdge retained h (states i) (states j) then coefficient i j else 0

/-- Literal repeated application of the finite signed transition matrix,
with the same state assignment, policy and weight at every step. -/
def p0CausalExitIterate {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (states : Fin n → FirstExitDepthState α) (coefficient : Fin n → Fin n → ℝ)
    (f : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0, i => f i
  | k + 1, i => ∑ j, p0CausalExitKernel retained h states coefficient i j *
      p0CausalExitIterate retained h states coefficient f k j

/-- A row vanishes after more transitions than there are actual remaining
labels. This is an exact finite identity with no norm or spectral premise. -/
theorem p0CausalExitIterate_zero_of_remaining_lt {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (states : Fin n → FirstExitDepthState α) (coefficient : Fin n → Fin n → ℝ)
    (f : Fin n → ℝ) (k : ℕ) :
    ∀ i, (states i).remaining.length < k →
      p0CausalExitIterate retained h states coefficient f k i = 0 := by
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
      intro i hi
      change (∑ j, p0CausalExitKernel retained h states coefficient i j *
        p0CausalExitIterate retained h states coefficient f k j) = 0
      apply Finset.sum_eq_zero
      intro j _
      by_cases he : P0CausalExitEdge retained h (states i) (states j)
      · have hdrop := (p0CausalExitEdge_strict he).2
        rw [ih j (by omega), mul_zero]
      · simp only [p0CausalExitKernel, if_neg he, zero_mul]

/-- For any finite selection of actual original exits, the original
carrier length is a uniform nilpotence index. Neither the number of rows
nor a numerical coefficient bound is used. -/
theorem p0CausalExitIterate_root_zero {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ) (carrier : List α)
    (states : Fin n → FirstExitDepthState α)
    (hstates : ∀ i, states i ∈ p1SignedExitStates retained h [] true 1 carrier)
    (coefficient : Fin n → Fin n → ℝ) (f : Fin n → ℝ) :
    p0CausalExitIterate retained h states coefficient f carrier.length = fun _ => 0 := by
  funext i
  apply p0CausalExitIterate_zero_of_remaining_lt retained h states coefficient f
  have hr := p1_mem_exitStates_rank_bound retained h [] carrier true 1 (states i) (hstates i)
  simp only [List.length_nil, Nat.zero_add] at hr
  omega

end

end ImbalancedChen
