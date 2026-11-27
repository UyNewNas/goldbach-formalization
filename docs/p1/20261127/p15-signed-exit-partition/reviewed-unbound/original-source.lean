import ImbalancedChen.FirstExitHistoricalLevels
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Signed first exits partitioned by their actual rank and retained history

Source-only candidate. Every rejected selection is recorded once, with its
incoming signed mass and its actual unprocessed carrier. No positivity or
old-admission filter is introduced. The finite bucket keys are taken from
the actual exit list; only keys, never occurrences of exits, are deduplicated.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Rejected selections below a retained incoming node. A record contains
the rejected prefix, its sign and mass, and exactly the tail after selection. -/
def p1SignedExitStates {α : Type*}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ) :
    List α → List (FirstExitDepthState α)
  | [] => []
  | p :: ps =>
      p1SignedExitStates retained h pre positive mass ps ++
        if retained (!positive) (p :: pre) = true then
          p1SignedExitStates retained h (p :: pre) (!positive) (mass * h p) ps
        else [{selectedPrefix := p :: pre, positive := !positive,
          mass := mass * h p, remaining := ps}]

/-- The sign is the negative of the rejected coefficient, as in
`firstExitCorrection`; the Euler product uses the recorded remaining list. -/
def p1SignedExitValue {α : Type*} (h : α → ℝ)
    (state : FirstExitDepthState α) : ℝ :=
  -signedTreeCoefficient state.positive state.mass *
    (state.remaining.map (fun p => 1 - h p)).prod

theorem p1_firstExitCorrection_eq_exitStates_sum
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (pre carrier : List α) (positive : Bool) (mass : ℝ) :
    firstExitCorrection retained h pre positive mass carrier =
      ((p1SignedExitStates retained h pre positive mass carrier).map
        (p1SignedExitValue h)).sum := by
  induction carrier generalizing pre positive mass with
  | nil => simp [firstExitCorrection, p1SignedExitStates]
  | cons p ps ih =>
      by_cases ht : retained (!positive) (p :: pre) = true
      · simp [firstExitCorrection, p1SignedExitStates, ht, ih]
      · simp [firstExitCorrection, p1SignedExitStates, p1SignedExitValue, ht, ih]

/-- Every enumerated exit is actually rejected by this policy. -/
theorem p1_mem_exitStates_rejected
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (pre carrier : List α) (positive : Bool) (mass : ℝ)
    (state : FirstExitDepthState α)
    (hstate : state ∈ p1SignedExitStates retained h pre positive mass carrier) :
    retained state.positive state.selectedPrefix ≠ true := by
  induction carrier generalizing pre positive mass with
  | nil => simp [p1SignedExitStates] at hstate
  | cons p ps ih =>
      by_cases ht : retained (!positive) (p :: pre) = true
      · rw [p1SignedExitStates, if_pos ht, List.mem_append] at hstate
        rcases hstate with hskip | hselect
        · exact ih pre positive mass hskip
        · exact ih (p :: pre) (!positive) (mass * h p) hselect
      · rw [p1SignedExitStates, if_neg ht, List.mem_append] at hstate
        rcases hstate with hskip | hexit
        · exact ih pre positive mass hskip
        · simp only [List.mem_singleton] at hexit
          subst state
          exact ht

/-- The parent of an exit is retained, provided the incoming node is
retained. This justifies grouping by ancestors of the parent, rather than
incorrectly treating the rejected selection as retained history. -/
theorem p1_mem_exitStates_parent_retained
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (pre carrier : List α) (positive : Bool) (mass : ℝ)
    (hpre : retained positive pre = true) (state : FirstExitDepthState α)
    (hstate : state ∈ p1SignedExitStates retained h pre positive mass carrier) :
    retained (!state.positive) state.selectedPrefix.tail = true := by
  induction carrier generalizing pre positive mass with
  | nil => simp [p1SignedExitStates] at hstate
  | cons p ps ih =>
      by_cases ht : retained (!positive) (p :: pre) = true
      · rw [p1SignedExitStates, if_pos ht, List.mem_append] at hstate
        rcases hstate with hskip | hselect
        · exact ih pre positive mass hpre hskip
        · exact ih (p :: pre) (!positive) (mass * h p) ht hselect
      · rw [p1SignedExitStates, if_neg ht, List.mem_append] at hstate
        rcases hstate with hskip | hexit
        · exact ih pre positive mass hpre hskip
        · simp only [List.mem_singleton] at hexit
          subst state
          simpa using hpre

/-- The recorded carrier is the literal suffix after an actual selected
label. In particular it cannot be replaced by a guessed cutoff carrier. -/
theorem p1_mem_exitStates_carrier_decomposition
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (pre carrier : List α) (positive : Bool) (mass : ℝ)
    (state : FirstExitDepthState α)
    (hstate : state ∈ p1SignedExitStates retained h pre positive mass carrier) :
    ∃ processed : List α, ∃ p : α, ∃ parent : List α,
      carrier = processed ++ p :: state.remaining ∧ state.selectedPrefix = p :: parent := by
  induction carrier generalizing pre positive mass with
  | nil => simp [p1SignedExitStates] at hstate
  | cons p ps ih =>
      have lift (hx : ∃ processed : List α, ∃ q : α, ∃ parent : List α,
          ps = processed ++ q :: state.remaining ∧ state.selectedPrefix = q :: parent) :
          ∃ processed : List α, ∃ q : α, ∃ parent : List α,
            p :: ps = processed ++ q :: state.remaining ∧
              state.selectedPrefix = q :: parent := by
        obtain ⟨processed, q, parent, htail, hprefix⟩ := hx
        exact ⟨p :: processed, q, parent, by simpa [htail], hprefix⟩
      by_cases ht : retained (!positive) (p :: pre) = true
      · rw [p1SignedExitStates, if_pos ht, List.mem_append] at hstate
        rcases hstate with hskip | hselect
        · exact lift (ih pre positive mass hskip)
        · exact lift (ih (p :: pre) (!positive) (mass * h p) hselect)
      · rw [p1SignedExitStates, if_neg ht, List.mem_append] at hstate
        rcases hstate with hskip | hexit
        · exact lift (ih pre positive mass hskip)
        · simp only [List.mem_singleton] at hexit
          subst state
          exact ⟨[], p, pre, rfl, rfl⟩

/-- Finite rank support comes from the real recursion, including skipped
labels, without requiring distinct labels or positivity of their weights. -/
theorem p1_mem_exitStates_rank_bound
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (pre carrier : List α) (positive : Bool) (mass : ℝ)
    (state : FirstExitDepthState α)
    (hstate : state ∈ p1SignedExitStates retained h pre positive mass carrier) :
    pre.length < state.selectedPrefix.length ∧
      state.selectedPrefix.length + state.remaining.length ≤ pre.length + carrier.length := by
  induction carrier generalizing pre positive mass with
  | nil => simp [p1SignedExitStates] at hstate
  | cons p ps ih =>
      by_cases ht : retained (!positive) (p :: pre) = true
      · rw [p1SignedExitStates, if_pos ht, List.mem_append] at hstate
        rcases hstate with hskip | hselect
        · have hh := ih pre positive mass hskip
          simp only [List.length_cons] at *
          omega
        · have hh := ih (p :: pre) (!positive) (mass * h p) hselect
          simp only [List.length_cons] at *
          omega
      · rw [p1SignedExitStates, if_neg ht, List.mem_append] at hstate
        rcases hstate with hskip | hexit
        · have hh := ih pre positive mass hskip
          simp only [List.length_cons] at *
          omega
        · simp only [List.mem_singleton] at hexit
          subst state
          simp only [List.length_cons]
          omega

/-- Actual history parity and prime-weight product are propagated all the
way to rejected selections, not only to retained leaves. -/
theorem p1_mem_exitStates_sign_mass
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (pre carrier : List α) (positive : Bool) (mass : ℝ)
    (hsign : positive = evenListLength pre) (hmass : mass = (pre.map h).prod)
    (state : FirstExitDepthState α)
    (hstate : state ∈ p1SignedExitStates retained h pre positive mass carrier) :
    state.positive = evenListLength state.selectedPrefix ∧
      state.mass = (state.selectedPrefix.map h).prod := by
  induction carrier generalizing pre positive mass with
  | nil => simp [p1SignedExitStates] at hstate
  | cons p ps ih =>
      have hsign' : (!positive) = evenListLength (p :: pre) := by
        rw [hsign]
        rfl
      have hmass' : mass * h p = ((p :: pre).map h).prod := by
        simp [hmass, mul_comm]
      by_cases ht : retained (!positive) (p :: pre) = true
      · rw [p1SignedExitStates, if_pos ht, List.mem_append] at hstate
        rcases hstate with hskip | hselect
        · exact ih pre positive mass hsign hmass hskip
        · exact ih (p :: pre) (!positive) (mass * h p) hsign' hmass' hselect
      · rw [p1SignedExitStates, if_neg ht, List.mem_append] at hstate
        rcases hstate with hskip | hexit
        · exact ih pre positive mass hsign hmass hskip
        · simp only [List.mem_singleton] at hexit
          subst state
          exact ⟨hsign', hmass'⟩

/-- Splicing below a retained rank changes the correction by the sum of
correction differences on the same actual frontier. The unrestricted Euler
products cancel state by state, with their recorded sign and remaining list. -/
theorem p1_firstExitCorrection_depthSplice_sub_eq_frontier_sum
    {α : Type*} (k : ℕ) (parent replacement : Bool → List α → Bool)
    (h : α → ℝ) (pre carrier : List α) (positive : Bool) (mass : ℝ) :
    firstExitCorrection (firstExitDepthSplicePolicy k parent replacement)
        h pre positive mass carrier - firstExitCorrection parent h pre positive mass carrier =
      ((firstExitDepthFrontier k parent h pre positive mass carrier).map
        (fun state => firstExitCorrection replacement h state.selectedPrefix
            state.positive state.mass state.remaining -
          firstExitCorrection parent h state.selectedPrefix
            state.positive state.mass state.remaining)).sum := by
  have hroot :
      firstExitCorrection (firstExitDepthSplicePolicy k parent replacement)
          h pre positive mass carrier - firstExitCorrection parent h pre positive mass carrier =
        firstExitRetainedPolynomial (firstExitDepthSplicePolicy k parent replacement)
          h pre positive mass carrier -
        firstExitRetainedPolynomial parent h pre positive mass carrier := by
    rw [firstExitRetainedPolynomial_eq_product_add_correction,
      firstExitRetainedPolynomial_eq_product_add_correction]
    ring
  rw [hroot, firstExitRetainedPolynomial_depthSplice_sub_eq_frontier_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro state _hstate
  rw [firstExitRetainedPolynomial_eq_product_add_correction,
    firstExitRetainedPolynomial_eq_product_add_correction]
  ring

/-- A multiplicity-preserving list sum can be grouped by any covering
finite key set. No `Nodup` premise on the states is needed. -/
private theorem p1_sum_finite_fibres
    {σ κ : Type*} [DecidableEq κ] (key : σ → κ) (f : σ → ℝ)
    (keys : Finset κ) (states : List σ) :
    (∀ s ∈ states, key s ∈ keys) →
      (∑ c ∈ keys, ((states.filter (fun s => decide (key s = c))).map f).sum) =
        (states.map f).sum := by
  induction states with
  | nil => intro _; simp
  | cons s states ih =>
      intro hcover
      have htail : ∀ t ∈ states, key t ∈ keys :=
        fun t ht => hcover t (List.mem_cons_of_mem s ht)
      have hfilter (c : κ) :
          (((s :: states).filter (fun t => decide (key t = c))).map f).sum =
            (if key s = c then f s else 0) +
              ((states.filter (fun t => decide (key t = c))).map f).sum := by
        by_cases hc : key s = c <;> simp [hc]
      simp_rw [hfilter]
      rw [Finset.sum_add_distrib, ih htail]
      have hhead : (∑ c ∈ keys, if key s = c then f s else 0) = f s := by
        rw [Finset.sum_eq_single_of_mem (key s) (hcover s (by simp))]
        · simp
        · intro c _hc hne
          simp [Ne.symm hne]
      rw [hhead]
      rfl

/-- The first coordinate is the actual rejected rank. The second is the
rank-`k` ancestor of the actual retained parent (reverse-stored history). -/
def p1SignedExitHistoryKey {α : Type*} (k : ℕ) (state : FirstExitDepthState α) :
    ℕ × List α :=
  (state.selectedPrefix.length, rosserAncestor k state.selectedPrefix.tail)

def p1SignedExitHistoryKeys {α : Type*} [DecidableEq α]
    (k : ℕ) (states : List (FirstExitDepthState α)) : Finset (ℕ × List α) :=
  (states.map (p1SignedExitHistoryKey k)).toFinset

/-- The exact correction grouped by actual rank and retained historical
ancestor. Both signs and every actual residual Euler carrier are retained. -/
theorem p1_firstExitCorrection_eq_rank_history_partition
    {α : Type*} [DecidableEq α] (k : ℕ)
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (pre carrier : List α) (positive : Bool) (mass : ℝ) :
    firstExitCorrection retained h pre positive mass carrier =
      let states := p1SignedExitStates retained h pre positive mass carrier
      ∑ c ∈ p1SignedExitHistoryKeys k states,
        ((states.filter (fun state => decide (p1SignedExitHistoryKey k state = c))).map
          (p1SignedExitValue h)).sum := by
  dsimp only
  rw [p1_firstExitCorrection_eq_exitStates_sum]
  symm
  apply p1_sum_finite_fibres
  intro state hstate
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨state, hstate, rfl⟩)

/-- The same root product-plus-correction identity now exposes a finite
partition, rather than concealing signs or replacing tails by root carriers. -/
theorem p1_retainedPolynomial_eq_product_add_rank_history_partition
    {α : Type*} [DecidableEq α] (k : ℕ)
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (pre carrier : List α) (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial retained h pre positive mass carrier =
      signedTreeCoefficient positive mass * (carrier.map (fun p => 1 - h p)).prod +
        (let states := p1SignedExitStates retained h pre positive mass carrier
         ∑ c ∈ p1SignedExitHistoryKeys k states,
           ((states.filter (fun state => decide (p1SignedExitHistoryKey k state = c))).map
             (p1SignedExitValue h)).sum) := by
  rw [firstExitRetainedPolynomial_eq_product_add_correction,
    p1_firstExitCorrection_eq_rank_history_partition k]

/-- Actual historical tree specialization: the target deletion, enumeration
cap, strict rough cutoff, and both coefficient signs are unchanged. No level
monotonicity or analytic density estimate is needed for this finite identity. -/
theorem p1_actualThirdCappedCorrection_eq_rank_history_partition
    (k : ℕ) (base : Bool → List ℕ → Bool) (Q3 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ) :
    firstExitCorrection (thirdCappedUpperPolicy base Q3)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      let states := p1SignedExitStates (thirdCappedUpperPolicy base Q3)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z)
      ∑ c ∈ p1SignedExitHistoryKeys k states,
        ((states.filter (fun state => decide (p1SignedExitHistoryKey k state = c))).map
          (fun state => -signedTreeCoefficient state.positive state.mass *
            (state.remaining.map (fun p : ℕ => 1 - 1 / ((p : ℝ) - 1))).prod)).sum := by
  exact p1_firstExitCorrection_eq_rank_history_partition k
    (thirdCappedUpperPolicy base Q3) (fun p : ℕ => 1 / ((p : ℝ) - 1))
    [] (roughPrimeUniverse N cap 0 z) true 1

end

end ImbalancedChen
