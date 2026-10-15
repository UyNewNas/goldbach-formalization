import ImbalancedChen.FirstExitFrontierAdmission
import ImbalancedChen.ActualFrozenOwnCubeDensity
import ImbalancedChen.PrimeHistoryLogCoordinates
import ImbalancedChen.FinitePrimeGeometryCore

/-!
# Exact inherited levels on the same first-exit tree

A splice below rank `m` leaves every frontier through rank `m` unchanged,
including the remaining carrier, sign and mass. A third-level upper policy
is admitted by its actual active rank-three test. Complete validity is then
propagated through later selected primes, including inactive even tests.
The resulting fourth- and fifth-level identities use this same third-level
tree. Level comparisons are finite geometric inputs, not analytic estimates.

The arbitrary finite third-level selector in this file is not identified
with a manuscript certificate or with its rough-cutoff fallback policy.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical

/-- Splicing only deeper tests preserves the full earlier frontier. This
also covers an incoming history already at or beyond the stopping rank. -/
theorem firstExitDepthFrontier_depthSplice_eq {α : Type*}
    (k m : ℕ) (hkm : k ≤ m) (parent replacement : Bool → List α → Bool)
    (h : α → ℝ) (pre carrier : List α) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier k (firstExitDepthSplicePolicy m parent replacement)
        h pre positive mass carrier =
      firstExitDepthFrontier k parent h pre positive mass carrier := by
  induction carrier generalizing pre positive mass with
  | nil => rfl
  | cons p ps ih =>
      by_cases hk : k ≤ pre.length
      · simp only [firstExitDepthFrontier, if_pos hk]
      · have hp : (p :: pre).length ≤ m := by simp only [List.length_cons]; omega
        simp only [firstExitDepthFrontier, if_neg hk, firstExitDepthSplicePolicy,
          if_pos hp]
        rw [ih pre positive mass, ih (p :: pre) (!positive) (mass * h p)]

/-- Replacing the same post-rank policy twice discards the intermediate one. -/
theorem firstExitDepthSplicePolicy_absorb {α : Type*} (k : ℕ)
    (parent old new : Bool → List α → Bool) :
    firstExitDepthSplicePolicy k (firstExitDepthSplicePolicy k parent old) new =
      firstExitDepthSplicePolicy k parent new := by
  funext positive pre
  by_cases hk : pre.length ≤ k <;> simp [firstExitDepthSplicePolicy, hk]

/-- Freezing an already inherited continuation again at a later rank has
no effect on the policy, rather than merely on a chosen polynomial. -/
theorem firstExitDepthSplicePolicy_absorb_later {α : Type*} (k m : ℕ)
    (hkm : k ≤ m) (parent replacement : Bool → List α → Bool) :
    firstExitDepthSplicePolicy m (firstExitDepthSplicePolicy k parent replacement)
        replacement = firstExitDepthSplicePolicy k parent replacement := by
  funext positive pre
  by_cases hm : pre.length ≤ m
  · simp [firstExitDepthSplicePolicy, hm]
  · have hk : ¬pre.length ≤ k := by omega
    simp [firstExitDepthSplicePolicy, hm, hk]

private theorem evenListLength_eq_decide_even (pre : List ℕ) :
    evenListLength pre = decide (Even pre.length) := by
  induction pre with
  | nil => simp [evenListLength]
  | cons p ps ih =>
      simp only [evenListLength, ih, List.length_cons, Nat.even_add_one, decide_not]

/-- The active third admission supplies complete validity. Subsequent
inactive tests use that inherited validity and the true sorted prime carrier. -/
theorem mem_firstExitDepthFrontier_thirdCapped_valid
    (base : Bool → List ℕ → Bool) (Q3 : List ℕ → ℝ) (k : ℕ) (h : ℕ → ℝ)
    (pre carrier : List ℕ) (positive : Bool) (mass : ℝ)
    (hpre : 3 ≤ pre.length → ordinaryRosserPrefixAdmissible false
      (Q3 (rosserAncestor 3 pre)) pre)
    (hsign : positive = evenListLength pre)
    (hprime : ∀ p ∈ carrier, p.Prime)
    (hsort : (carrier.reverse ++ pre).Pairwise (· < ·))
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k (thirdCappedUpperPolicy base Q3)
      h pre positive mass carrier) :
    (3 ≤ state.selectedPrefix.length → ordinaryRosserPrefixAdmissible false
      (Q3 (rosserAncestor 3 state.selectedPrefix)) state.selectedPrefix) ∧
      state.positive = evenListLength state.selectedPrefix := by
  induction carrier generalizing pre positive mass with
  | nil =>
      by_cases hk : k ≤ pre.length
      · simp only [firstExitDepthFrontier, if_pos hk, List.mem_singleton] at hstate
        subst state
        exact ⟨hpre, hsign⟩
      · simp [firstExitDepthFrontier, hk] at hstate
  | cons q qs ih =>
      by_cases hk : k ≤ pre.length
      · rw [firstExitDepthFrontier_of_rank_le_length k _ h pre (q :: qs)
          positive mass hk, List.mem_singleton] at hstate
        subst state
        exact ⟨hpre, hsign⟩
      · have hsort' : (qs.reverse ++ q :: pre).Pairwise (· < ·) := by
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hsort
        have hskipSort : (qs.reverse ++ pre).Pairwise (· < ·) :=
          hsort'.sublist ((List.Sublist.refl qs.reverse).append ((List.Sublist.refl pre).cons q))
        have hprime' : ∀ p ∈ qs, p.Prime :=
          fun p hp => hprime p (List.mem_cons_of_mem q hp)
        by_cases ht : thirdCappedUpperPolicy base Q3 (!positive) (q :: pre) = true
        · rw [firstExitDepthFrontier, if_neg hk, if_pos ht, List.mem_append] at hstate
          rcases hstate with hskip | hselect
          · exact ih pre positive mass hpre hsign hprime' hskipSort hskip
          · have hnext : 3 ≤ (q :: pre).length → ordinaryRosserPrefixAdmissible false
                (Q3 (rosserAncestor 3 (q :: pre))) (q :: pre) := by
              intro hlen
              have hdeep : ¬(q :: pre).length ≤ 2 := by omega
              have ht' : ordinaryParityRosserPolicy false
                  (Q3 (rosserAncestor 3 (q :: pre))) (!positive) (q :: pre) = true := by
                simpa only [thirdCappedUpperPolicy, firstExitDepthSplicePolicy, if_neg hdeep,
                  frozenParityRosserPolicy, ancestorFrozenPolicy] using ht
              by_cases hp : 3 ≤ pre.length
              · rw [rosserAncestor_cons 3 q pre hp] at ht' ⊢
                rw [ordinaryParityRosserPolicy_eq_full_on_valid_prefix false
                  (Q3 (rosserAncestor 3 pre)) pre positive q (hpre hp) hsign
                  (hprime q (by simp)) (by simp) (List.pairwise_append.mp hsort').2.1] at ht'
                exact of_decide_eq_true ht'
              · have hlen2 : pre.length = 2 := by simp only [List.length_cons] at hlen; omega
                have hs : positive = true := by
                  rw [hsign, evenListLength_eq_decide_even, hlen2]
                  decide
                simpa only [hs, Bool.not_true, ordinaryParityRosserPolicy, Bool.false_eq_true,
                  if_false, oddFirstExitPolicy, Bool.false_or, decide_eq_true_eq] using ht'
            have hsign' : (!positive) = evenListLength (q :: pre) := by rw [hsign]; rfl
            exact ih (q :: pre) (!positive) (mass * h q) hnext hsign' hprime' hsort' hselect
        · rw [firstExitDepthFrontier, if_neg hk, if_neg ht, List.append_nil] at hstate
          exact ih pre positive mass hpre hsign hprime' hskipSort hstate

/-- Actual target-deleted prime frontiers inherit validity at their frozen
third level. No caller-supplied rank-four admissibility is needed. -/
theorem actualThirdCapped_frontier_admissible
    (base : Bool → List ℕ → Bool) (Q3 : List ℕ → ℝ) (k : ℕ) (hk : 3 ≤ k)
    (N cap : ℕ) (z : ℝ) (h : ℕ → ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k (thirdCappedUpperPolicy base Q3)
      h [] true 1 (roughPrimeUniverse N cap 0 z)) :
    ordinaryRosserPrefixAdmissible false (Q3 (rosserAncestor 3 state.selectedPrefix))
      state.selectedPrefix := by
  have hv := mem_firstExitDepthFrontier_thirdCapped_valid base Q3 k h []
    (roughPrimeUniverse N cap 0 z) true 1 (by simp) rfl
    (fun _ hp => mem_roughPrimeUniverse_prime hp)
    (by simpa only [List.append_nil, List.pairwise_reverse]
      using roughPrimeUniverse_pairwise_gt N cap 0 z) state hstate
  apply hv.1
  rw [firstExitDepthFrontier_selected_length k _ h [] _ true 1 (by simp) state hstate]
  exact hk

theorem actualThirdCapped_rankFour_admissible
    (base : Bool → List ℕ → Bool) (Q3 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ) (h : ℕ → ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 4 (thirdCappedUpperPolicy base Q3)
      h [] true 1 (roughPrimeUniverse N cap 0 z)) :
    ordinaryRosserPrefixAdmissible false (Q3 (rosserAncestor 3 state.selectedPrefix))
      state.selectedPrefix :=
  actualThirdCapped_frontier_admissible base Q3 4 (by omega) N cap z h state hstate

/-- Freezing the inherited third level again after rank four recovers the
original third-capped policy exactly. -/
theorem thirdCappedUpperPolicy_refreeze_four
    (base : Bool → List ℕ → Bool) (Q3 : List ℕ → ℝ) :
    firstExitDepthSplicePolicy 4 (thirdCappedUpperPolicy base Q3)
        (frozenParityRosserPolicy false 4 (fun pre => Q3 (rosserAncestor 3 pre))) =
      thirdCappedUpperPolicy base Q3 := by
  rw [frozenParityRosserPolicy_nested false 3 4 (by omega)]
  exact firstExitDepthSplicePolicy_absorb_later 2 4 (by omega) base _

/-- A fourth-level replacement preserves the actual third-capped parent
through rank four. -/
def fourthCappedUpperPolicy (base : Bool → List ℕ → Bool)
    (Q3 Q4 : List ℕ → ℝ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 4 (thirdCappedUpperPolicy base Q3)
    (frozenParityRosserPolicy false 4 Q4)

/-- The fifth-level own test is replaced before admission, on the same
third-capped rank-four frontier used by the fourth replacement. -/
def fifthCappedUpperPolicy (base : Bool → List ℕ → Bool)
    (Q3 Q5 : List ℕ → ℝ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 4 (thirdCappedUpperPolicy base Q3)
    (frozenParityRosserPolicy false 5 Q5)

theorem fourthCappedUpperPolicy_frontier_four
    (base : Bool → List ℕ → Bool) (Q3 Q4 : List ℕ → ℝ)
    (h : ℕ → ℝ) (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 4 (fourthCappedUpperPolicy base Q3 Q4)
        h pre positive mass carrier =
      firstExitDepthFrontier 4 (thirdCappedUpperPolicy base Q3)
        h pre positive mass carrier :=
  firstExitDepthFrontier_depthSplice_eq 4 4 le_rfl _ _ h pre carrier positive mass

theorem fifthCappedUpperPolicy_frontier_four
    (base : Bool → List ℕ → Bool) (Q3 Q5 : List ℕ → ℝ)
    (h : ℕ → ℝ) (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 4 (fifthCappedUpperPolicy base Q3 Q5)
        h pre positive mass carrier =
      firstExitDepthFrontier 4 (thirdCappedUpperPolicy base Q3)
        h pre positive mass carrier :=
  firstExitDepthFrontier_depthSplice_eq 4 4 le_rfl _ _ h pre carrier positive mass

/-- The fourth saving is a literal finite sum of actual residual densities
at the inherited and raised levels, with their true signed prime masses. -/
def actualHistoricalFourthSaving (base : Bool → List ℕ → Bool)
    (Q3 Q4 : List ℕ → ℝ) (N cap : ℕ) (z : ℝ) : ℝ :=
  ((firstExitDepthFrontier 4 (thirdCappedUpperPolicy base Q3)
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z)).map
    (fun state =>
      actualFrozenFrontierDensityTerm false N cap
          (fun pre => Q3 (rosserAncestor 3 pre)) state.selectedPrefix -
        actualFrozenFrontierDensityTerm false N cap Q4 state.selectedPrefix)).sum

/-- The fifth saving enumerates every next candidate, including candidates
rejected by the old own test. Each gated density keeps its own indicator. -/
def actualHistoricalFifthSaving (base : Bool → List ℕ → Bool)
    (Q3 Q4 Q5 : List ℕ → ℝ) (N cap : ℕ) (z : ℝ) : ℝ :=
  ((firstExitDepthFrontier 4 (thirdCappedUpperPolicy base Q3)
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z)).map
    (fun frontier =>
      ((firstExitNextSelectionCandidates (fun p : ℕ => 1 / ((p : ℝ) - 1))
        frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining).map
        (fun candidate =>
          (candidate.selectedPrefix.map (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod *
            (actualOwnCubeGatedMinusDensity N cap Q5 candidate.selectedPrefix -
              actualOwnCubeGatedMinusDensity N cap
                (fun pre => Q4 (rosserAncestor 4 pre)) candidate.selectedPrefix))).sum)).sum

/-- The actual third-to-fourth replacement needs only a finite level
comparison; complete prefix admissibility is proved from the true tree. -/
theorem actualHistoricalFourthSaving_eq
    (base : Bool → List ℕ → Bool) (Q3 Q4 : List ℕ → ℝ) (N cap : ℕ) (z : ℝ)
    (hlevel : ∀ state ∈ firstExitDepthFrontier 4 (thirdCappedUpperPolicy base Q3)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      Q3 (rosserAncestor 3 state.selectedPrefix) ≤ Q4 state.selectedPrefix) :
    firstExitRetainedPolynomial (thirdCappedUpperPolicy base Q3)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (fourthCappedUpperPolicy base Q3 Q4)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      actualHistoricalFourthSaving base Q3 Q4 N cap z := by
  have hvalid := fun state hstate => actualThirdCapped_rankFour_admissible
    base Q3 N cap z (fun p : ℕ => 1 / ((p : ℝ) - 1)) state hstate
  have hh := firstExitRetainedPolynomial_frozenParity_splice_sub_eq_density_sum
    false 4 (by omega) (thirdCappedUpperPolicy base Q3) Q4
    (fun pre => Q3 (rosserAncestor 3 pre)) N cap z
    (fun state hstate => ordinaryRosserPrefixAdmissible_mono false state.selectedPrefix
      (hlevel state hstate) (hvalid state hstate)) hvalid
  rw [thirdCappedUpperPolicy_refreeze_four] at hh
  exact hh

/-- The fourth-to-fifth comparison is taken on the original third-capped
frontier, with no old fifth-admission filter and no guessed continuation. -/
theorem actualHistoricalFifthSaving_eq
    (base : Bool → List ℕ → Bool) (Q3 Q4 Q5 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ)
    (h34 : ∀ state ∈ firstExitDepthFrontier 4 (thirdCappedUpperPolicy base Q3)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      Q3 (rosserAncestor 3 state.selectedPrefix) ≤ Q4 state.selectedPrefix)
    (h45 : ∀ frontier ∈ firstExitDepthFrontier 4 (thirdCappedUpperPolicy base Q3)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      ∀ candidate ∈ firstExitNextSelectionCandidates
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier.selectedPrefix
        frontier.positive frontier.mass frontier.remaining,
        Q4 frontier.selectedPrefix ≤ Q5 candidate.selectedPrefix) :
    firstExitRetainedPolynomial (fourthCappedUpperPolicy base Q3 Q4)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (fifthCappedUpperPolicy base Q3 Q5)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      actualHistoricalFifthSaving base Q3 Q4 Q5 N cap z := by
  apply actual_frozen_upper_five_ownCube_saving
  · intro state hstate
    exact ordinaryRosserPrefixAdmissible_mono false state.selectedPrefix (h34 state hstate)
      (actualThirdCapped_rankFour_admissible base Q3 N cap z
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) state hstate)
  · exact h45

/-- Exact telescoping on one historical tree. Neither saving is asserted
nonnegative here, and no asymptotic or integrated estimate is assumed. -/
theorem actualHistoricalThirdToFifthSaving_eq
    (base : Bool → List ℕ → Bool) (Q3 Q4 Q5 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ)
    (h34 : ∀ state ∈ firstExitDepthFrontier 4 (thirdCappedUpperPolicy base Q3)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      Q3 (rosserAncestor 3 state.selectedPrefix) ≤ Q4 state.selectedPrefix)
    (h45 : ∀ frontier ∈ firstExitDepthFrontier 4 (thirdCappedUpperPolicy base Q3)
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      ∀ candidate ∈ firstExitNextSelectionCandidates
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier.selectedPrefix
        frontier.positive frontier.mass frontier.remaining,
        Q4 frontier.selectedPrefix ≤ Q5 candidate.selectedPrefix) :
    firstExitRetainedPolynomial (thirdCappedUpperPolicy base Q3)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial (fifthCappedUpperPolicy base Q3 Q5)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      actualHistoricalFourthSaving base Q3 Q4 N cap z +
        actualHistoricalFifthSaving base Q3 Q4 Q5 N cap z := by
  rw [← actualHistoricalFourthSaving_eq base Q3 Q4 N cap z h34,
    ← actualHistoricalFifthSaving_eq base Q3 Q4 Q5 N cap z h34 h45]
  ring

end

end ImbalancedChen
