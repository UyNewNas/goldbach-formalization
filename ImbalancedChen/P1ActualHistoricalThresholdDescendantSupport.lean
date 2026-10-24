import ImbalancedChen.P1ActualHistoricalThirdRoughThreshold
import ImbalancedChen.P1SignedExitPolicyComparison
import ImbalancedChen.PrimeHistoryLogCoordinates
import ImbalancedChen.ActualFrozenFrontierDensity

/-!
# Threshold-strip support at actual descendants and first disagreements

The two rank-four frontiers need not coincide. Each actual frontier and each
of its fifth candidates receives a pointwise frozen-ancestor support theorem.
The comparison of entire trees instead uses the signed task's actual common
admission tree and its first different admissions. No common later frontier,
policy monotonicity, or analytic residual estimate is assumed.

Imports with P1 names are candidate adoption paths. Source only.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical List BigOperators
open Set

namespace HistoricalThirdCoarse.P1ThresholdDescendant
open P1ActualTuple P1ActualPartition P1ActualThreshold P1ThirdFallbackSupport

def primeWeight (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1)

def ancestorTuple (pre : List ℕ) : Fin 3 → ℕ :=
  primeHistoryTuple 3 (rosserAncestor 3 pre)

def ancestorLog (N : ℕ) (pre : List ℕ) : Fin 3 → ℝ :=
  primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 pre)

/-- This reads the actual oldest three selections, without reordering them. -/
def ancestorSupport (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (N : ℕ) (pre : List ℕ) : Prop :=
  ancestorLog N pre ∈ thresholdStrip omega omega' ∩ jointCells e chi m

theorem ancestorLog_eq_tupleLog (N : ℕ) (pre : List ℕ) :
    ancestorLog N pre = actualPrimeTupleLog N (ancestorTuple pre) := by rfl

private theorem history_ancestorTuple (pre : List ℕ) (hlen : 3 ≤ pre.length) :
    history (ancestorTuple pre) = rosserAncestor 3 pre := by
  have ha : (rosserAncestor 3 pre).length = 3 := by
    rw [rosserAncestor_length]
    omega
  have hh := primeHistoryTuple_reverse_ofFn ha
  simpa [ancestorTuple, history, List.ofFn_succ] using hh

private theorem ancestorTuple_positive (pre : List ℕ) (hlen : 3 ≤ pre.length)
    (hpos : ∀ p ∈ pre, 0 < p) : ∀ i, 0 < ancestorTuple pre i := by
  intro i
  unfold ancestorTuple
  rw [primeHistoryTuple_ancestor (k := pre.length) (history := pre) rfl hlen i]
  exact primeHistoryTuple_pos rfl hpos _

theorem ancestorSupport_append (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (N : ℕ) (later pre : List ℕ) (hlen : 3 ≤ pre.length) :
    ancestorSupport e chi m omega omega' N (later ++ pre) ↔
      ancestorSupport e chi m omega omega' N pre := by
  unfold ancestorSupport ancestorLog
  rw [rosserAncestor_append 3 later pre hlen]

theorem frozenLevel_sub_append (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (N : ℕ) (later pre : List ℕ) (hlen : 3 ≤ pre.length) :
    frozenLevel e chi m omega (N : ℝ) (later ++ pre) -
        frozenLevel e chi m omega' (N : ℝ) (later ++ pre) =
      frozenLevel e chi m omega (N : ℝ) pre - frozenLevel e chi m omega' (N : ℝ) pre := by
  rw [frozenLevel_append e chi m omega (N : ℝ) later pre hlen,
    frozenLevel_append e chi m omega' (N : ℝ) later pre hlen]

private theorem frozenLevel_eq_at_short_history (e chi : ℝ) (m : ℕ)
    (omega omega' : ℝ) (N : ℕ) (pre : List ℕ) (hlen : ¬3 ≤ pre.length) :
    frozenLevel e chi m omega (N : ℝ) pre = frozenLevel e chi m omega' (N : ℝ) pre := by
  have ha (w : ℝ) : ¬active w (N : ℝ) (rosserAncestor 3 pre) := by
    intro h
    have hh := h.1
    rw [rosserAncestor_length] at hh
    omega
  unfold frozenLevel
  rw [rawLevel_inactive e chi m omega (N : ℝ) _ (ha omega),
    rawLevel_inactive e chi m omega' (N : ℝ) _ (ha omega')]

/-- Level equality off the actual frozen ancestor strip, including histories
too short to have activated the third selector. -/
theorem frozenLevel_eq_off_support (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (horder : omega ≤ omega') (N : ℕ) (hN : 1 < N) (pre : List ℕ)
    (hpos : ∀ p ∈ pre, 0 < p)
    (hs : ¬ancestorSupport e chi m omega omega' N pre) :
    frozenLevel e chi m omega (N : ℝ) pre = frozenLevel e chi m omega' (N : ℝ) pre := by
  by_cases hlen : 3 ≤ pre.length
  · have hp := ancestorTuple_positive pre hlen hpos
    by_cases ht : ancestorLog N pre ∈ thresholdStrip omega omega'
    · have ho : actualPrimeTupleLog N (ancestorTuple pre) ∉ jointCells e chi m := by
        intro h
        exact hs ⟨ht, h⟩
      have hh := rawLevel_eq_outside_cells e chi m omega omega' N (ancestorTuple pre) ho
      simpa only [frozenLevel, history_ancestorTuple pre hlen] using hh
    · have hh := rawLevel_eq_off_strip e chi m omega omega' horder N hN
        (ancestorTuple pre) hp ht
      simpa only [frozenLevel, history_ancestorTuple pre hlen] using hh
  · exact frozenLevel_eq_at_short_history e chi m omega omega' N pre hlen

theorem frozenLevel_ne_support (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (horder : omega ≤ omega') (N : ℕ) (hN : 1 < N) (pre : List ℕ)
    (hpos : ∀ p ∈ pre, 0 < p)
    (hne : frozenLevel e chi m omega (N : ℝ) pre ≠
      frozenLevel e chi m omega' (N : ℝ) pre) :
    ancestorSupport e chi m omega omega' N pre := by
  by_contra hs
  exact hne (frozenLevel_eq_off_support e chi m omega omega' horder N hN pre hpos hs)

theorem policy_eq_off_support (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (horder : omega ≤ omega') (N : ℕ) (hN : 1 < N) (pre : List ℕ)
    (hpos : ∀ p ∈ pre, 0 < p) (positive : Bool)
    (hs : ¬ancestorSupport e chi m omega omega' N pre) :
    policy e chi m omega (N : ℝ) positive pre =
      policy e chi m omega' (N : ℝ) positive pre := by
  by_cases hshort : pre.length ≤ 2
  · rw [policy_through_two e chi m omega (N : ℝ) positive pre hshort,
      policy_through_two e chi m omega' (N : ℝ) positive pre hshort]
  · have hl := frozenLevel_eq_off_support e chi m omega omega' horder N hN pre hpos hs
    simp only [policy, thirdCappedUpperPolicy, firstExitDepthSplicePolicy,
      if_neg hshort, frozenParityRosserPolicy, ancestorFrozenPolicy]
    change ordinaryParityRosserPolicy false (frozenLevel e chi m omega (N : ℝ) pre)
        positive pre =
      ordinaryParityRosserPolicy false (frozenLevel e chi m omega' (N : ℝ) pre) positive pre
    rw [hl]

theorem policy_ne_support (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (horder : omega ≤ omega') (N : ℕ) (hN : 1 < N) (pre : List ℕ)
    (hpos : ∀ p ∈ pre, 0 < p) (positive : Bool)
    (hne : policy e chi m omega (N : ℝ) positive pre ≠
      policy e chi m omega' (N : ℝ) positive pre) :
    ancestorSupport e chi m omega omega' N pre := by
  by_contra hs
  exact hne (policy_eq_off_support e chi m omega omega' horder N hN pre hpos positive hs)

theorem later_policy_eq_off_ancestor_support (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (horder : omega ≤ omega') (N : ℕ) (hN : 1 < N) (later pre : List ℕ)
    (hlen : 3 ≤ pre.length) (hpos : ∀ p ∈ later ++ pre, 0 < p) (positive : Bool)
    (hs : ¬ancestorSupport e chi m omega omega' N pre) :
    policy e chi m omega (N : ℝ) positive (later ++ pre) =
      policy e chi m omega' (N : ℝ) positive (later ++ pre) := by
  apply policy_eq_off_support e chi m omega omega' horder N hN (later ++ pre) hpos positive
  intro h
  exact hs ((ancestorSupport_append e chi m omega omega' N later pre hlen).mp h)

/-- The original rank-two frontier really is shared. No later frontier equality
is inferred from this finite depth-splice identity. -/
theorem rank_two_frontier_common (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (N cap : ℕ) (z : ℝ) :
    firstExitDepthFrontier 2 (policy e chi m omega (N : ℝ)) primeWeight [] true 1
        (roughPrimeUniverse N cap 0 z) =
      firstExitDepthFrontier 2 (policy e chi m omega' (N : ℝ)) primeWeight [] true 1
        (roughPrimeUniverse N cap 0 z) := by
  simp only [policy, thirdCappedUpperPolicy]
  rw [firstExitDepthFrontier_depthSplice_eq 2 2 le_rfl,
    firstExitDepthFrontier_depthSplice_eq 2 2 le_rfl]

private theorem frontier_positive (e chi : ℝ) (m : ℕ) (w : ℝ)
    (N cap : ℕ) (z : ℝ) (k : ℕ) (state : FirstExitDepthState ℕ)
    (hs : state ∈ firstExitDepthFrontier k (policy e chi m w (N : ℝ)) primeWeight
      [] true 1 (roughPrimeUniverse N cap 0 z)) : ∀ p ∈ state.selectedPrefix, 0 < p := by
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist k
    (policy e chi m w (N : ℝ)) primeWeight (roughPrimeUniverse N cap 0 z) state hs
  intro p hp
  exact (mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp))).pos

/-- Either actual tree's rank-four history inherits the same oldest-three
support criterion. Membership on both sides is never required. -/
theorem rank_four_difference_support (e chi : ℝ) (m : ℕ) (omega omega' w : ℝ)
    (horder : omega ≤ omega') (N cap : ℕ) (hN : 1 < N) (z : ℝ)
    (state : FirstExitDepthState ℕ)
    (hs : state ∈ firstExitDepthFrontier 4 (policy e chi m w (N : ℝ)) primeWeight
      [] true 1 (roughPrimeUniverse N cap 0 z))
    (hd : frozenLevel e chi m omega (N : ℝ) state.selectedPrefix ≠
        frozenLevel e chi m omega' (N : ℝ) state.selectedPrefix ∨
      policy e chi m omega (N : ℝ) false state.selectedPrefix ≠
        policy e chi m omega' (N : ℝ) false state.selectedPrefix) :
    ancestorSupport e chi m omega omega' N state.selectedPrefix := by
  have hp := frontier_positive e chi m w N cap z 4 state hs
  rcases hd with hl | ht
  · exact frozenLevel_ne_support e chi m omega omega' horder N hN _ hp hl
  · exact policy_ne_support e chi m omega omega' horder N hN _ hp false ht

/-- The literal next-selection record keeps the frontier's oldest three.
This includes candidates rejected by either threshold's own fifth test. -/
theorem fifth_candidate_same_ancestor (e chi : ℝ) (m : ℕ) (omega omega' w : ℝ)
    (N cap : ℕ) (z : ℝ) (frontier candidate : FirstExitDepthState ℕ)
    (hf : frontier ∈ firstExitDepthFrontier 4 (policy e chi m w (N : ℝ)) primeWeight
      [] true 1 (roughPrimeUniverse N cap 0 z))
    (hc : candidate ∈ firstExitNextSelectionCandidates primeWeight frontier.selectedPrefix
      frontier.positive frontier.mass frontier.remaining) :
    rosserAncestor 3 candidate.selectedPrefix = rosserAncestor 3 frontier.selectedPrefix ∧
      (ancestorSupport e chi m omega omega' N candidate.selectedPrefix ↔
        ancestorSupport e chi m omega omega' N frontier.selectedPrefix) := by
  have hlen := firstExitDepthFrontier_selected_length 4 (policy e chi m w (N : ℝ))
    primeWeight [] (roughPrimeUniverse N cap 0 z) true 1 (by simp) frontier hf
  obtain ⟨before, q, after, hremaining, hstate⟩ :=
    (mem_firstExitNextSelectionCandidates_iff primeWeight frontier.selectedPrefix
      frontier.remaining frontier.positive frontier.mass candidate).mp hc
  have ha : rosserAncestor 3 candidate.selectedPrefix = rosserAncestor 3 frontier.selectedPrefix := by
    rw [hstate]
    exact rosserAncestor_cons 3 q frontier.selectedPrefix (by omega)
  exact ⟨ha, by simp only [ancestorSupport, ancestorLog, ha]⟩

theorem fifth_candidate_difference_support (e chi : ℝ) (m : ℕ) (omega omega' w : ℝ)
    (horder : omega ≤ omega') (N cap : ℕ) (hN : 1 < N) (z : ℝ)
    (frontier candidate : FirstExitDepthState ℕ)
    (hf : frontier ∈ firstExitDepthFrontier 4 (policy e chi m w (N : ℝ)) primeWeight
      [] true 1 (roughPrimeUniverse N cap 0 z))
    (hc : candidate ∈ firstExitNextSelectionCandidates primeWeight frontier.selectedPrefix
      frontier.positive frontier.mass frontier.remaining)
    (hd : frozenLevel e chi m omega (N : ℝ) candidate.selectedPrefix ≠
        frozenLevel e chi m omega' (N : ℝ) candidate.selectedPrefix ∨
      policy e chi m omega (N : ℝ) candidate.positive candidate.selectedPrefix ≠
        policy e chi m omega' (N : ℝ) candidate.positive candidate.selectedPrefix) :
    ancestorSupport e chi m omega omega' N candidate.selectedPrefix := by
  obtain ⟨_, _, _, _, _, _, _, hprime⟩ :=
    actualPrimeNextSelection_geometry 4 (policy e chi m w (N : ℝ)) N cap z frontier hf candidate hc
  have hp : ∀ p ∈ candidate.selectedPrefix, 0 < p := fun p hp => (hprime p hp).pos
  rcases hd with hl | ht
  · exact frozenLevel_ne_support e chi m omega omega' horder N hN _ hp hl
  · exact policy_ne_support e chi m omega omega' horder N hN _ hp candidate.positive ht

theorem retained_history_difference_support (e chi : ℝ) (m : ℕ) (omega omega' w : ℝ)
    (horder : omega ≤ omega') (N cap : ℕ) (hN : 1 < N) (z : ℝ)
    (leaf : FirstExitLeaf ℕ)
    (hs : leaf ∈ firstExitRootLeaves (policy e chi m w (N : ℝ)) primeWeight
      (roughPrimeUniverse N cap 0 z))
    (hd : frozenLevel e chi m omega (N : ℝ) leaf.selected ≠
        frozenLevel e chi m omega' (N : ℝ) leaf.selected ∨
      policy e chi m omega (N : ℝ) leaf.positive leaf.selected ≠
        policy e chi m omega' (N : ℝ) leaf.positive leaf.selected) :
    ancestorSupport e chi m omega omega' N leaf.selected := by
  have hprime := mem_firstExitRootLeaves_selected_prime (policy e chi m w (N : ℝ))
    primeWeight (roughPrimeUniverse N cap 0 z)
    (fun p hp => mem_roughPrimeUniverse_prime hp) leaf hs
  have hp : ∀ p ∈ leaf.selected, 0 < p := fun p hp => (hprime p hp).pos
  rcases hd with hl | ht
  · exact frozenLevel_ne_support e chi m omega omega' horder N hN _ hp hl
  · exact policy_ne_support e chi m omega omega' horder N hN _ hp leaf.positive ht

/-- The actual signed reciprocal-prime residual expression at a fixed history.
It is not an identification of two different complete frontier sums. -/
def residualDifference (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (N cap : ℕ) (pre : List ℕ) : ℝ :=
  actualFrozenFrontierDensityTerm false N cap (frozenLevel e chi m omega (N : ℝ)) pre -
    actualFrozenFrontierDensityTerm false N cap (frozenLevel e chi m omega' (N : ℝ)) pre

theorem residualDifference_zero_off_support (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (horder : omega ≤ omega') (N cap : ℕ) (hN : 1 < N) (pre : List ℕ)
    (hpos : ∀ p ∈ pre, 0 < p) (hs : ¬ancestorSupport e chi m omega omega' N pre) :
    residualDifference e chi m omega omega' N cap pre = 0 := by
  have hh := frozenLevel_eq_off_support e chi m omega omega' horder N hN pre hpos hs
  simp only [residualDifference, actualFrozenFrontierDensityTerm, hh, sub_self]

theorem residualDifference_ne_support (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (horder : omega ≤ omega') (N cap : ℕ) (hN : 1 < N) (pre : List ℕ)
    (hpos : ∀ p ∈ pre, 0 < p)
    (hne : residualDifference e chi m omega omega' N cap pre ≠ 0) :
    ancestorSupport e chi m omega omega' N pre := by
  by_contra hs
  exact hne (residualDifference_zero_off_support e chi m omega omega' horder N cap hN pre hpos hs)

private theorem residual_list_sum_filter (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (horder : omega ≤ omega') (N cap : ℕ) (hN : 1 < N)
    (states : List (FirstExitDepthState ℕ))
    (hpos : ∀ s ∈ states, ∀ p ∈ s.selectedPrefix, 0 < p)
    (F : FirstExitDepthState ℕ → ℝ) :
    (states.map (fun s => F s * residualDifference e chi m omega omega' N cap s.selectedPrefix)).sum =
      ((states.filter (fun s => decide (ancestorSupport e chi m omega omega' N s.selectedPrefix))).map
        (fun s => F s * residualDifference e chi m omega omega' N cap s.selectedPrefix)).sum := by
  induction states with
  | nil => simp
  | cons s states ih =>
      have ht := ih (fun t ht => hpos t (by simp [ht]))
      by_cases hs : ancestorSupport e chi m omega omega' N s.selectedPrefix
      · simp [hs, ht]
      · have hz := residualDifference_zero_off_support e chi m omega omega' horder N cap hN
          s.selectedPrefix (hpos s (by simp)) hs
        simp [hs, hz, ht]

/-- The residual-expression difference localizes on each tree's own rank-four
frontier, separately for any choice w of the tree being enumerated. -/
theorem rank_four_residual_sum_filter (e chi : ℝ) (m : ℕ) (omega omega' w : ℝ)
    (horder : omega ≤ omega') (N cap : ℕ) (hN : 1 < N) (z : ℝ)
    (F : FirstExitDepthState ℕ → ℝ) :
    let states := firstExitDepthFrontier 4 (policy e chi m w (N : ℝ)) primeWeight
      [] true 1 (roughPrimeUniverse N cap 0 z)
    (states.map (fun s => F s * residualDifference e chi m omega omega' N cap s.selectedPrefix)).sum =
      ((states.filter (fun s => decide (ancestorSupport e chi m omega omega' N s.selectedPrefix))).map
        (fun s => F s * residualDifference e chi m omega omega' N cap s.selectedPrefix)).sum := by
  dsimp only
  apply residual_list_sum_filter e chi m omega omega' horder N cap hN
  intro s hs
  exact frontier_positive e chi m w N cap z 4 s hs

private theorem candidates_positive (e chi : ℝ) (m : ℕ) (w : ℝ)
    (N cap : ℕ) (z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitFrontierCandidates 4 (policy e chi m w (N : ℝ)) primeWeight
      (roughPrimeUniverse N cap 0 z)) : ∀ p ∈ s.selectedPrefix, 0 < p := by
  have hm : s.selectedPrefix.reverse ∈
      (firstExitFrontierCandidates 4 (policy e chi m w (N : ℝ)) primeWeight
        (roughPrimeUniverse N cap 0 z)).map (fun t => t.selectedPrefix.reverse) :=
    List.mem_map.mpr ⟨s, hs, rfl⟩
  have hh := (mem_firstExitFrontierCandidates_history_iff 4
    (policy e chi m w (N : ℝ)) primeWeight (roughPrimeUniverse N cap 0 z)
    s.selectedPrefix.reverse).mp hm
  intro p hp
  exact (mem_roughPrimeUniverse_prime (hh.1.subset (List.mem_reverse.mpr hp))).pos

theorem fifth_candidate_residual_sum_filter (e chi : ℝ) (m : ℕ) (omega omega' w : ℝ)
    (horder : omega ≤ omega') (N cap : ℕ) (hN : 1 < N) (z : ℝ)
    (F : FirstExitDepthState ℕ → ℝ) :
    let states := firstExitFrontierCandidates 4 (policy e chi m w (N : ℝ)) primeWeight
      (roughPrimeUniverse N cap 0 z)
    (states.map (fun s => F s * residualDifference e chi m omega omega' N cap s.selectedPrefix)).sum =
      ((states.filter (fun s => decide (ancestorSupport e chi m omega omega' N s.selectedPrefix))).map
        (fun s => F s * residualDifference e chi m omega omega' N cap s.selectedPrefix)).sum := by
  dsimp only
  apply residual_list_sum_filter e chi m omega omega' horder N cap hN
  intro s hs
  exact candidates_positive e chi m w N cap z s hs

/-! Entire-tree comparison uses the signed first-disagreement tree. -/

def differenceStates (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (N cap : ℕ) (z : ℝ) : List (FirstExitDepthState ℕ) :=
  p1SignedExitStates (p1CommonAdmissionPolicy (policy e chi m omega' (N : ℝ))
    (policy e chi m omega (N : ℝ))) primeWeight [] true 1 (roughPrimeUniverse N cap 0 z)

private theorem exitStates_positive (P : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (pre carrier : List ℕ) (positive : Bool) (mass : ℝ)
    (hpre : ∀ p ∈ pre, 0 < p) (hcarrier : ∀ p ∈ carrier, 0 < p)
    (s : FirstExitDepthState ℕ) (hs : s ∈ p1SignedExitStates P h pre positive mass carrier) :
    ∀ p ∈ s.selectedPrefix, 0 < p := by
  induction carrier generalizing pre positive mass with
  | nil => simp [p1SignedExitStates] at hs
  | cons q qs ih =>
      have hq := hcarrier q (by simp)
      have hqs : ∀ p ∈ qs, 0 < p := fun p hp => hcarrier p (by simp [hp])
      have hnext : ∀ p ∈ q :: pre, 0 < p := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hq
        · exact hpre p hp
      by_cases ht : P (!positive) (q :: pre) = true
      · rw [p1SignedExitStates, if_pos ht, List.mem_append] at hs
        rcases hs with hs | hs
        · exact ih pre positive mass hpre hqs hs
        · exact ih (q :: pre) (!positive) (mass * h q) hnext hqs hs
      · rw [p1SignedExitStates, if_neg ht, List.mem_append] at hs
        rcases hs with hs | hs
        · exact ih pre positive mass hpre hqs hs
        · simp only [List.mem_singleton] at hs
          subst s
          exact hnext

theorem first_different_admission_support (e chi : ℝ) (m : ℕ) (omega omega' : ℝ)
    (horder : omega ≤ omega') (N cap : ℕ) (hN : 1 < N) (z : ℝ)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ (differenceStates e chi m omega omega' N cap z).filter
        (p1AdmissionOnly (policy e chi m omega (N : ℝ)) (policy e chi m omega' (N : ℝ))) ∨
      s ∈ (differenceStates e chi m omega omega' N cap z).filter
        (p1AdmissionOnly (policy e chi m omega' (N : ℝ)) (policy e chi m omega (N : ℝ)))) :
    ancestorSupport e chi m omega omega' N s.selectedPrefix := by
  have hp (hm : s ∈ differenceStates e chi m omega omega' N cap z) :
      ∀ p ∈ s.selectedPrefix, 0 < p :=
    exitStates_positive _ primeWeight [] (roughPrimeUniverse N cap 0 z) true 1
      (by simp) (fun p hp => (mem_roughPrimeUniverse_prime hp).pos) s hm
  rcases hs with hl | hh
  · obtain ⟨hm, ha, hr⟩ := p1_mem_admissionOnly_tests _ _ _ s hl
    apply policy_ne_support e chi m omega omega' horder N hN _ (hp hm) s.positive
    rw [ha, hr]
    decide
  · obtain ⟨hm, ha, hr⟩ := p1_mem_admissionOnly_tests _ _ _ s hh
    apply policy_ne_support e chi m omega omega' horder N hN _ (hp hm) s.positive
    rw [hr, ha]
    decide

/-- Complete tree difference with the real two directional continuations.
Each first differing admission is localized to the same oldest-three strip.
No equality of the two rank-four frontiers is used. -/
theorem polynomial_sub_eq_supported_first_admissions
    (e chi : ℝ) (m : ℕ) (omega omega' : ℝ) (horder : omega ≤ omega')
    (N cap : ℕ) (hN : 1 < N) (z : ℝ) :
    firstExitRetainedPolynomial (policy e chi m omega (N : ℝ)) primeWeight [] true 1
        (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (policy e chi m omega' (N : ℝ)) primeWeight [] true 1
        (roughPrimeUniverse N cap 0 z) =
    let states := differenceStates e chi m omega omega' N cap z
    ((((states.filter (p1AdmissionOnly (policy e chi m omega (N : ℝ))
      (policy e chi m omega' (N : ℝ)))).filter
        (fun s => decide (ancestorSupport e chi m omega omega' N s.selectedPrefix))).map
          (fun s => firstExitRetainedPolynomial (policy e chi m omega (N : ℝ)) primeWeight
            s.selectedPrefix s.positive s.mass s.remaining)).sum) -
    ((((states.filter (p1AdmissionOnly (policy e chi m omega' (N : ℝ))
      (policy e chi m omega (N : ℝ)))).filter
        (fun s => decide (ancestorSupport e chi m omega omega' N s.selectedPrefix))).map
          (fun s => firstExitRetainedPolynomial (policy e chi m omega' (N : ℝ)) primeWeight
            s.selectedPrefix s.positive s.mass s.remaining)).sum) := by
  dsimp only
  have hl : ((differenceStates e chi m omega omega' N cap z).filter
      (p1AdmissionOnly (policy e chi m omega (N : ℝ)) (policy e chi m omega' (N : ℝ)))).filter
        (fun s => decide (ancestorSupport e chi m omega omega' N s.selectedPrefix)) =
      (differenceStates e chi m omega omega' N cap z).filter
        (p1AdmissionOnly (policy e chi m omega (N : ℝ)) (policy e chi m omega' (N : ℝ))) := by
    apply List.filter_eq_self.mpr
    intro s hs
    simpa only [decide_eq_true_eq] using
      first_different_admission_support e chi m omega omega' horder N cap hN z s (Or.inl hs)
  have hh : ((differenceStates e chi m omega omega' N cap z).filter
      (p1AdmissionOnly (policy e chi m omega' (N : ℝ)) (policy e chi m omega (N : ℝ)))).filter
        (fun s => decide (ancestorSupport e chi m omega omega' N s.selectedPrefix)) =
      (differenceStates e chi m omega omega' N cap z).filter
        (p1AdmissionOnly (policy e chi m omega' (N : ℝ)) (policy e chi m omega (N : ℝ))) := by
    apply List.filter_eq_self.mpr
    intro s hs
    simpa only [decide_eq_true_eq] using
      first_different_admission_support e chi m omega omega' horder N cap hN z s (Or.inr hs)
  rw [hl, hh]
  exact p1_policy_sub_eq_first_different_admissions
    (policy e chi m omega' (N : ℝ)) (policy e chi m omega (N : ℝ)) primeWeight
    [] (roughPrimeUniverse N cap 0 z) true 1

end HistoricalThirdCoarse.P1ThresholdDescendant
end
end ImbalancedChen
