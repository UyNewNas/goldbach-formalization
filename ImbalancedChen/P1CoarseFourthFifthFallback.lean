import ImbalancedChen.HistoricalThirdFallbackSupportP1
import ImbalancedChen.FirstExitHistoricalLevels

/-!
This source consumes the sibling first draft, whose proposed adoption path is
ImbalancedChen/HistoricalThirdFallbackSupportP1.lean. It does not replace the
historical coarse policy by the ordinary constant-level dictionary.

Arbitrary Q4/Q5 preserve T3's rank-four frontier and its earlier admissions.
They do NOT in general preserve the later odd tests outside third support.
Only the concrete inherited choice Q4 = Q5 = actual frozenLevel is identified
with T3 globally. A complete historical Q4/Q5 table is still missing.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical BigOperators
open HistoricalThirdCoarse P1ThirdFallbackSupport

namespace P1CoarseFourthFifthFallback

theorem frozenSupported_cons (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (q : ℕ) (pre : List ℕ) (hlen : 3 ≤ pre.length) :
    frozenSupported e chi m omega N (q :: pre) ↔
      frozenSupported e chi m omega N pre := by
  unfold frozenSupported
  rw [rosserAncestor_cons 3 q pre hlen]

theorem not_frozenSupported_of_inactive (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (pre : List ℕ) (ha : ¬ active omega N (rosserAncestor 3 pre)) :
    ¬ frozenSupported e chi m omega N pre := by
  intro hs
  exact ha hs.1

theorem not_frozenSupported_of_outside (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (pre : List ℕ)
    (hout : ∀ j ∈ cells e chi m,
      primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) ∉
        logPrimeMeshCell 0 (19 / 96) m j) :
    ¬ frozenSupported e chi m omega N pre := by
  rintro ⟨_, j, hj, ht⟩
  exact hout j hj ht

/-- Skipping and selecting later primes cannot change a third ancestor. -/
theorem retained_subtree_fallback (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (h : ℕ → ℝ) (pre carrier : List ℕ) (positive : Bool) (mass : ℝ)
    (hlen : 3 ≤ pre.length) (hs : ¬ frozenSupported e chi m omega N pre) :
    firstExitRetainedPolynomial (policy e chi m omega N) h pre positive mass carrier =
      firstExitRetainedPolynomial (initialPolicy e m N) h pre positive mass carrier := by
  induction carrier generalizing pre positive mass with
  | nil => rfl
  | cons q qs ih =>
      have hnext : 3 ≤ (q :: pre).length := by simp only [List.length_cons]; omega
      have hsnext : ¬ frozenSupported e chi m omega N (q :: pre) := by
        rw [frozenSupported_cons e chi m omega N q pre hlen]
        exact hs
      have hp := policy_fallback e chi m omega N (!positive) (q :: pre) hsnext
      simp only [firstExitRetainedPolynomial, hp]
      rw [ih pre positive mass hlen hs,
        ih (q :: pre) (!positive) (mass * h q) hnext hsnext]

/-- This is equality of full depth states, including signs, mass and remainder. -/
theorem depth_frontier_fallback (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (k : ℕ) (h : ℕ → ℝ) (pre carrier : List ℕ) (positive : Bool) (mass : ℝ)
    (hlen : 3 ≤ pre.length) (hs : ¬ frozenSupported e chi m omega N pre) :
    firstExitDepthFrontier k (policy e chi m omega N) h pre positive mass carrier =
      firstExitDepthFrontier k (initialPolicy e m N) h pre positive mass carrier := by
  induction carrier generalizing pre positive mass with
  | nil => rfl
  | cons q qs ih =>
      by_cases hk : k ≤ pre.length
      · simp only [firstExitDepthFrontier, if_pos hk]
      · have hnext : 3 ≤ (q :: pre).length := by simp only [List.length_cons]; omega
        have hsnext : ¬ frozenSupported e chi m omega N (q :: pre) := by
          rw [frozenSupported_cons e chi m omega N q pre hlen]
          exact hs
        have hp := policy_fallback e chi m omega N (!positive) (q :: pre) hsnext
        simp only [firstExitDepthFrontier, if_neg hk, hp]
        rw [ih pre positive mass hlen hs,
          ih (q :: pre) (!positive) (mass * h q) hnext hsnext]

theorem fourth_through_four (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (Q4 : List ℕ → ℝ) (positive : Bool) (pre : List ℕ) (hlen : pre.length ≤ 4) :
    fourthCappedUpperPolicy (initialPolicy e m N) (rawLevel e chi m omega N) Q4
        positive pre = policy e chi m omega N positive pre := by
  simpa only [fourthCappedUpperPolicy, firstExitDepthSplicePolicy, if_pos hlen]

theorem fifth_through_four (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (Q5 : List ℕ → ℝ) (positive : Bool) (pre : List ℕ) (hlen : pre.length ≤ 4) :
    fifthCappedUpperPolicy (initialPolicy e m N) (rawLevel e chi m omega N) Q5
        positive pre = policy e chi m omega N positive pre := by
  simpa only [fifthCappedUpperPolicy, firstExitDepthSplicePolicy, if_pos hlen]

theorem fourth_fallback_through_four (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (Q4 : List ℕ → ℝ) (positive : Bool) (pre : List ℕ) (hlen : pre.length ≤ 4)
    (hs : ¬ frozenSupported e chi m omega N pre) :
    fourthCappedUpperPolicy (initialPolicy e m N) (rawLevel e chi m omega N) Q4
        positive pre = initialPolicy e m N positive pre := by
  rw [fourth_through_four e chi m omega N Q4 positive pre hlen]
  exact policy_fallback e chi m omega N positive pre hs

theorem fifth_fallback_through_four (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (Q5 : List ℕ → ℝ) (positive : Bool) (pre : List ℕ) (hlen : pre.length ≤ 4)
    (hs : ¬ frozenSupported e chi m omega N pre) :
    fifthCappedUpperPolicy (initialPolicy e m N) (rawLevel e chi m omega N) Q5
        positive pre = initialPolicy e m N positive pre := by
  rw [fifth_through_four e chi m omega N Q5 positive pre hlen]
  exact policy_fallback e chi m omega N positive pre hs

/-- Inactive even-parity tests do not inspect an arbitrary fourth level. -/
theorem fourth_even (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (Q4 : List ℕ → ℝ) (pre : List ℕ) :
    fourthCappedUpperPolicy (initialPolicy e m N) (rawLevel e chi m omega N) Q4
        true pre = true := by
  by_cases hlen : pre.length ≤ 4
  · rw [fourth_through_four e chi m omega N Q4 true pre hlen]
    exact policy_even e chi m omega N pre
  · simp [fourthCappedUpperPolicy, firstExitDepthSplicePolicy, hlen,
      frozenParityRosserPolicy, ancestorFrozenPolicy, ordinaryParityRosserPolicy,
      oddFirstExitPolicy]

theorem fifth_even (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (Q5 : List ℕ → ℝ) (pre : List ℕ) :
    fifthCappedUpperPolicy (initialPolicy e m N) (rawLevel e chi m omega N) Q5
        true pre = true := by
  by_cases hlen : pre.length ≤ 4
  · rw [fifth_through_four e chi m omega N Q5 true pre hlen]
    exact policy_even e chi m omega N pre
  · simp [fifthCappedUpperPolicy, firstExitDepthSplicePolicy, hlen,
      frozenParityRosserPolicy, ancestorFrozenPolicy, ordinaryParityRosserPolicy,
      oddFirstExitPolicy]

/-- Every fourth replacement uses the literal coarse T3 parent frontier. -/
theorem fourth_frontier_four (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (Q4 : List ℕ → ℝ) (h : ℕ → ℝ) (pre carrier : List ℕ)
    (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 4
        (fourthCappedUpperPolicy (initialPolicy e m N) (rawLevel e chi m omega N) Q4)
        h pre positive mass carrier =
      firstExitDepthFrontier 4 (policy e chi m omega N) h pre positive mass carrier := by
  exact fourthCappedUpperPolicy_frontier_four (initialPolicy e m N)
    (rawLevel e chi m omega N) Q4 h pre carrier positive mass

theorem fifth_frontier_four (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (Q5 : List ℕ → ℝ) (h : ℕ → ℝ) (pre carrier : List ℕ)
    (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 4
        (fifthCappedUpperPolicy (initialPolicy e m N) (rawLevel e chi m omega N) Q5)
        h pre positive mass carrier =
      firstExitDepthFrontier 4 (policy e chi m omega N) h pre positive mass carrier := by
  exact fifthCappedUpperPolicy_frontier_four (initialPolicy e m N)
    (rawLevel e chi m omega N) Q5 h pre carrier positive mass

/-- The inherited fourth level is the actual coarse frozenLevel. -/
theorem fourth_inherit_eq_third (e chi : ℝ) (m : ℕ) (omega N : ℝ) :
    fourthCappedUpperPolicy (initialPolicy e m N) (rawLevel e chi m omega N)
        (frozenLevel e chi m omega N) = policy e chi m omega N := by
  exact thirdCappedUpperPolicy_refreeze_four (initialPolicy e m N)
    (rawLevel e chi m omega N)

/-- Refreezing the same actual third level at rank five also changes nothing. -/
theorem fifth_inherit_eq_third (e chi : ℝ) (m : ℕ) (omega N : ℝ) :
    fifthCappedUpperPolicy (initialPolicy e m N) (rawLevel e chi m omega N)
        (frozenLevel e chi m omega N) = policy e chi m omega N := by
  unfold fifthCappedUpperPolicy frozenLevel policy
  rw [frozenParityRosserPolicy_nested false 3 5 (by omega)]
  exact firstExitDepthSplicePolicy_absorb_later 2 4 (by omega) (initialPolicy e m N) _

theorem fourth_inherited_subtree_difference_zero (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (h : ℕ → ℝ) (pre carrier : List ℕ) (positive : Bool) (mass : ℝ)
    (hlen : 3 ≤ pre.length) (hs : ¬ frozenSupported e chi m omega N pre) :
    firstExitRetainedPolynomial
        (fourthCappedUpperPolicy (initialPolicy e m N) (rawLevel e chi m omega N)
          (frozenLevel e chi m omega N)) h pre positive mass carrier -
      firstExitRetainedPolynomial (initialPolicy e m N) h pre positive mass carrier = 0 := by
  rw [fourth_inherit_eq_third,
    retained_subtree_fallback e chi m omega N h pre carrier positive mass hlen hs, sub_self]

theorem fifth_inherited_subtree_difference_zero (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (h : ℕ → ℝ) (pre carrier : List ℕ) (positive : Bool) (mass : ℝ)
    (hlen : 3 ≤ pre.length) (hs : ¬ frozenSupported e chi m omega N pre) :
    firstExitRetainedPolynomial
        (fifthCappedUpperPolicy (initialPolicy e m N) (rawLevel e chi m omega N)
          (frozenLevel e chi m omega N)) h pre positive mass carrier -
      firstExitRetainedPolynomial (initialPolicy e m N) h pre positive mass carrier = 0 := by
  rw [fifth_inherit_eq_third,
    retained_subtree_fallback e chi m omega N h pre carrier positive mass hlen hs, sub_self]

/-- The actual fourth saving definition vanishes for the inherited third level. -/
theorem actual_fourth_inherited_saving_zero (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (z : ℝ) :
    actualHistoricalFourthSaving (initialPolicy e m (N : ℝ))
      (rawLevel e chi m omega (N : ℝ)) (frozenLevel e chi m omega (N : ℝ))
      N cap z = 0 := by
  simp [actualHistoricalFourthSaving, frozenLevel]

/-- Both actual fifth gated densities use the same actual third ancestor. -/
theorem actual_fifth_inherited_saving_zero (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (z : ℝ) :
    actualHistoricalFifthSaving (initialPolicy e m (N : ℝ))
      (rawLevel e chi m omega (N : ℝ))
      (frozenLevel e chi m omega (N : ℝ)) (frozenLevel e chi m omega (N : ℝ))
      N cap z = 0 := by
  simp [actualHistoricalFifthSaving, frozenLevel, rosserAncestor_nested 3 4 (by omega)]

/-- Actual density terms, using the frozen third history and original Theta fallback. -/
def frontierDensityDifference (e chi : ℝ) (m : ℕ) (omega scale : ℝ)
    (N cap : ℕ) (pre : List ℕ) : ℝ :=
  actualFrozenFrontierDensityTerm false N cap (frozenLevel e chi m omega scale) pre -
    actualFrozenFrontierDensityTerm false N cap (fun _ => scale ^ initial e) pre

/-- Both literal strict own-cube indicators are retained in this difference. -/
def ownCubeDensityDifference (e chi : ℝ) (m : ℕ) (omega scale : ℝ)
    (N cap : ℕ) (pre : List ℕ) : ℝ :=
  actualOwnCubeGatedMinusDensity N cap (frozenLevel e chi m omega scale) pre -
    actualOwnCubeGatedMinusDensity N cap (fun _ => scale ^ initial e) pre

theorem frontierDensityDifference_zero (e chi : ℝ) (m : ℕ) (omega scale : ℝ)
    (N cap : ℕ) (pre : List ℕ) (hs : ¬ frozenSupported e chi m omega scale pre) :
    frontierDensityDifference e chi m omega scale N cap pre = 0 := by
  have hlevel := frozenLevel_fallback e chi m omega scale pre hs
  simp only [frontierDensityDifference, actualFrozenFrontierDensityTerm, hlevel, sub_self]

theorem ownCubeDensityDifference_zero (e chi : ℝ) (m : ℕ) (omega scale : ℝ)
    (N cap : ℕ) (pre : List ℕ) (hs : ¬ frozenSupported e chi m omega scale pre) :
    ownCubeDensityDifference e chi m omega scale N cap pre = 0 := by
  have hlevel := frozenLevel_fallback e chi m omega scale pre hs
  simp only [ownCubeDensityDifference, actualOwnCubeGatedMinusDensity, hlevel, sub_self]

/-- Includes next candidates rejected by either own-cube gate. -/
theorem next_candidate_ownCubeDifference_zero (e chi : ℝ) (m : ℕ) (omega scale : ℝ)
    (N cap : ℕ) (h : ℕ → ℝ) (pre remaining : List ℕ) (positive : Bool) (mass : ℝ)
    (hlen : 3 ≤ pre.length) (hs : ¬ frozenSupported e chi m omega scale pre)
    (candidate : FirstExitDepthState ℕ)
    (hcandidate : candidate ∈ firstExitNextSelectionCandidates h pre positive mass remaining) :
    ownCubeDensityDifference e chi m omega scale N cap candidate.selectedPrefix = 0 := by
  obtain ⟨before, q, after, _hrem, rfl⟩ :=
    (mem_firstExitNextSelectionCandidates_iff h pre remaining positive mass candidate).mp hcandidate
  apply ownCubeDensityDifference_zero
  change ¬ frozenSupported e chi m omega scale (q :: pre)
  rw [frozenSupported_cons e chi m omega scale q pre hlen]
  exact hs

theorem sum_next_candidate_ownCubeDifference_zero (e chi : ℝ) (m : ℕ) (omega scale : ℝ)
    (N cap : ℕ) (h : ℕ → ℝ) (pre remaining : List ℕ) (positive : Bool) (mass : ℝ)
    (hlen : 3 ≤ pre.length) (hs : ¬ frozenSupported e chi m omega scale pre)
    (weight : FirstExitDepthState ℕ → ℝ) :
    ((firstExitNextSelectionCandidates h pre positive mass remaining).map
      (fun candidate => weight candidate * ownCubeDensityDifference e chi m omega scale
        N cap candidate.selectedPrefix)).sum = 0 := by
  calc
    _ = ((firstExitNextSelectionCandidates h pre positive mass remaining).map
        (fun _ => (0 : ℝ))).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro candidate hcandidate
      rw [next_candidate_ownCubeDifference_zero e chi m omega scale N cap h pre remaining
        positive mass hlen hs candidate hcandidate, mul_zero]
    _ = 0 := by simp

/-- Filtering a list preserves all multiplicities and signed weights. -/
theorem sum_frontierDensityDifference_filter (e chi : ℝ) (m : ℕ) (omega scale : ℝ)
    (N cap : ℕ) (states : List (FirstExitDepthState ℕ))
    (weight : FirstExitDepthState ℕ → ℝ) :
    (states.map (fun s => weight s *
      frontierDensityDifference e chi m omega scale N cap s.selectedPrefix)).sum =
    ((states.filter (fun s => decide (frozenSupported e chi m omega scale s.selectedPrefix))).map
      (fun s => weight s *
        frontierDensityDifference e chi m omega scale N cap s.selectedPrefix)).sum := by
  induction states with
  | nil => rfl
  | cons state states ih =>
      by_cases hs : frozenSupported e chi m omega scale state.selectedPrefix
      · simp [hs, ih]
      · simp [hs, frontierDensityDifference_zero e chi m omega scale N cap
          state.selectedPrefix hs, ih]

theorem sum_ownCubeDensityDifference_filter (e chi : ℝ) (m : ℕ) (omega scale : ℝ)
    (N cap : ℕ) (states : List (FirstExitDepthState ℕ))
    (weight : FirstExitDepthState ℕ → ℝ) :
    (states.map (fun s => weight s *
      ownCubeDensityDifference e chi m omega scale N cap s.selectedPrefix)).sum =
    ((states.filter (fun s => decide (frozenSupported e chi m omega scale s.selectedPrefix))).map
      (fun s => weight s *
        ownCubeDensityDifference e chi m omega scale N cap s.selectedPrefix)).sum := by
  induction states with
  | nil => rfl
  | cons state states ih =>
      by_cases hs : frozenSupported e chi m omega scale state.selectedPrefix
      · simp [hs, ih]
      · simp [hs, ownCubeDensityDifference_zero e chi m omega scale N cap
          state.selectedPrefix hs, ih]

/-- The finite density support decomposition is on the real target-deleted T3 tree. -/
theorem actual_third_frontier_density_filter (e chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) (z : ℝ) :
    let states := firstExitDepthFrontier 4 (policy e chi m omega (N : ℝ))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z)
    (states.map (fun s => frontierDensityDifference e chi m omega (N : ℝ)
      N cap s.selectedPrefix)).sum =
      ((states.filter (fun s => decide
        (frozenSupported e chi m omega (N : ℝ) s.selectedPrefix))).map
          (fun s => frontierDensityDifference e chi m omega (N : ℝ)
            N cap s.selectedPrefix)).sum := by
  dsimp only
  simpa only [one_mul] using sum_frontierDensityDifference_filter e chi m omega
    (N : ℝ) N cap
    (firstExitDepthFrontier 4 (policy e chi m omega (N : ℝ))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z))
    (fun _ => 1)

end P1CoarseFourthFifthFallback
end
end ImbalancedChen
