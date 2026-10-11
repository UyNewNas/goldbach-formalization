import ImbalancedChen.FirstExitCandidateGeometry
import ImbalancedChen.ActualRosserShortPrefixDensity

/-!
# Actual density changes at frozen upper and lower own-cube tests

Every possible fifth selection is enumerated below the same actual
rank-four parent frontier. Both its old and new own-cube indicators are
retained. Thus newly admitted, previously rejected branches are included.
The old upper tree minus the new upper tree is the positive prefix mass
times new gated lower density minus old gated lower density.

The old level is frozen at the fourth ancestor and the new level at the
fifth. The inherited fourth prefix must be admissible at its old level;
the explicit level monotonicity supplies its tests at the new level.
The lower fourth-selection analogue has positive mass, so the new lower
tree minus the old one has the same density-difference sum.
No continuation equality or analytic density estimate is assumed.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical

/-- Literal lower residual density, restricted by this prefix's own cube.
The strict gate is kept even when the other policy rejects the prefix. -/
def actualOwnCubeGatedMinusDensity
    (N cap : ℕ) (Q : List ℕ → ℝ) (pre : List ℕ) : ℝ :=
  if (pre.prod : ℝ) * (pre.headD 0 : ℝ) ^ 2 < Q pre then
    actualSmallRosserMinusDensity N cap (pre.headD 0 : ℝ) (Q pre / (pre.prod : ℝ))
  else 0

private theorem actual_nextSelection_tail_ancestor
    (k : ℕ) (parent : Bool → List ℕ → Bool) (N cap : ℕ) (z : ℝ)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z))
    (candidate : FirstExitDepthState ℕ)
    (hcandidate : candidate ∈ firstExitNextSelectionCandidates
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier.selectedPrefix
      frontier.positive frontier.mass frontier.remaining) :
    candidate.selectedPrefix.tail = frontier.selectedPrefix ∧
      rosserAncestor k candidate.selectedPrefix = frontier.selectedPrefix := by
  obtain ⟨before, q, after, _hrem, rfl⟩ :=
    (mem_firstExitNextSelectionCandidates_iff _ _ _ _ _ candidate).mp hcandidate
  have hlen := firstExitDepthFrontier_selected_length k parent
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] (roughPrimeUniverse N cap 0 z) true 1
    (by simp) frontier hfrontier
  refine ⟨rfl, ?_⟩
  change rosserAncestor k (q :: frontier.selectedPrefix) = frontier.selectedPrefix
  rw [rosserAncestor_cons k q frontier.selectedPrefix hlen.ge,
    rosserAncestor_self_of_length k frontier.selectedPrefix hlen]

/-- On every actual candidate, including rejected ones, the full gated
continuation is minus the actual prime-prefix mass times the gated lower
density. Admissibility is required only for the inherited four primes. -/
theorem actual_frozen_upper_five_candidate_density
    (parent : Bool → List ℕ → Bool) (Q : List ℕ → ℝ) (N cap : ℕ) (z : ℝ)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier 4 parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z))
    (candidate : FirstExitDepthState ℕ)
    (hcandidate : candidate ∈ firstExitNextSelectionCandidates
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier.selectedPrefix
      frontier.positive frontier.mass frontier.remaining)
    (hpre : ordinaryRosserPrefixAdmissible false (Q candidate.selectedPrefix)
      frontier.selectedPrefix) :
    (if frozenParityRosserPolicy false 5 Q candidate.positive candidate.selectedPrefix = true then
      firstExitRetainedPolynomial (frozenParityRosserPolicy false 5 Q)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) candidate.selectedPrefix candidate.positive
        candidate.mass candidate.remaining else 0) =
      -(candidate.selectedPrefix.map (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod *
        actualOwnCubeGatedMinusDensity N cap Q candidate.selectedPrefix := by
  obtain ⟨p1, p2, p3, p4, p5, hf, hs, h54, h43, h32, h21, _hp5, h5, hsign,
      hmass, hremaining⟩ :=
    actualPrimeNextSelection_rank_four_exists parent N cap z frontier hfrontier candidate hcandidate
  rw [hf, hs] at hpre
  have htests := (ordinaryRosserPrefixAdmissible_upper_four_iff
    (Q [p5, p4, p3, p2, p1]) p1 p2 p3 p4 (by omega) h43 h32 h21).mp hpre
  rw [hs, hsign, hmass, hremaining,
    frozen_upper_five_ownCube_actualDensity Q N cap p1 p2 p3 p4 p5
      (by omega) h54 h43 h32 h21 htests.1 htests.2]
  simp only [actualOwnCubeGatedMinusDensity, List.headD_cons,
    List.prod_cons, List.prod_nil, Nat.cast_mul, mul_one]
  split_ifs <;> ring

/-- The old fourth-frozen upper tree minus the new fifth-frozen upper
tree is the sum of both gated actual lower residual densities on every
candidate of the original parent frontier. No old-admission filter is
used to enumerate the sum. -/
theorem actual_frozen_upper_five_ownCube_saving
    (parent : Bool → List ℕ → Bool) (Q4 Q5 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ)
    (hpre : ∀ frontier ∈ firstExitDepthFrontier 4 parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      ordinaryRosserPrefixAdmissible false (Q4 frontier.selectedPrefix) frontier.selectedPrefix)
    (hlevel : ∀ frontier ∈ firstExitDepthFrontier 4 parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      ∀ candidate ∈ firstExitNextSelectionCandidates
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier.selectedPrefix
        frontier.positive frontier.mass frontier.remaining,
        Q4 frontier.selectedPrefix ≤ Q5 candidate.selectedPrefix) :
    firstExitRetainedPolynomial
        (firstExitDepthSplicePolicy 4 parent (frozenParityRosserPolicy false 4 Q4))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial
        (firstExitDepthSplicePolicy 4 parent (frozenParityRosserPolicy false 5 Q5))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      ((firstExitDepthFrontier 4 parent (fun p : ℕ => 1 / ((p : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z)).map (fun frontier =>
        ((firstExitNextSelectionCandidates (fun p : ℕ => 1 / ((p : ℝ) - 1))
          frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining).map
          (fun candidate =>
            (candidate.selectedPrefix.map (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod *
              (actualOwnCubeGatedMinusDensity N cap Q5 candidate.selectedPrefix -
                actualOwnCubeGatedMinusDensity N cap
                  (fun pre => Q4 (rosserAncestor 4 pre)) candidate.selectedPrefix))).sum)).sum := by
  rw [← frozenParityRosserPolicy_nested false 4 5 (by omega) Q4,
    firstExitRetainedPolynomial_ownCubeSplice_root_sub_eq]
  apply congrArg List.sum
  apply List.map_congr_left
  intro frontier hfrontier
  apply congrArg List.sum
  apply List.map_congr_left
  intro candidate hcandidate
  have hancestor := (actual_nextSelection_tail_ancestor 4 parent N cap z
    frontier hfrontier candidate hcandidate).2
  have hold : ordinaryRosserPrefixAdmissible false
      ((fun pre => Q4 (rosserAncestor 4 pre)) candidate.selectedPrefix)
      frontier.selectedPrefix := by
    simpa only [hancestor] using hpre frontier hfrontier
  have hnew := ordinaryRosserPrefixAdmissible_mono false frontier.selectedPrefix
    (hlevel frontier hfrontier candidate hcandidate) (hpre frontier hfrontier)
  rw [actual_frozen_upper_five_candidate_density parent
      (fun pre => Q4 (rosserAncestor 4 pre)) N cap z frontier hfrontier candidate hcandidate hold,
    actual_frozen_upper_five_candidate_density parent Q5 N cap z
      frontier hfrontier candidate hcandidate hnew]
  ring

/-- Lower parity has the same actual candidate description with positive
prefix mass at the fourth selection. Only the inherited third history is
assumed admissible; the fourth own-cube test remains a literal indicator. -/
theorem actual_frozen_lower_four_candidate_density
    (parent : Bool → List ℕ → Bool) (Q : List ℕ → ℝ) (N cap : ℕ) (z : ℝ)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier 3 parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z))
    (candidate : FirstExitDepthState ℕ)
    (hcandidate : candidate ∈ firstExitNextSelectionCandidates
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier.selectedPrefix
      frontier.positive frontier.mass frontier.remaining)
    (hpre : ordinaryRosserPrefixAdmissible true (Q candidate.selectedPrefix)
      frontier.selectedPrefix) :
    (if frozenParityRosserPolicy true 4 Q candidate.positive candidate.selectedPrefix = true then
      firstExitRetainedPolynomial (frozenParityRosserPolicy true 4 Q)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) candidate.selectedPrefix candidate.positive
        candidate.mass candidate.remaining else 0) =
      (candidate.selectedPrefix.map (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod *
        actualOwnCubeGatedMinusDensity N cap Q candidate.selectedPrefix := by
  obtain ⟨_hlen, hsort, _hP, _hcut, hremaining, hsign, hmass, hprime⟩ :=
    actualPrimeNextSelection_geometry 3 parent N cap z frontier hfrontier candidate hcandidate
  obtain ⟨before, p4, after, _hrem, hc⟩ :=
    (mem_firstExitNextSelectionCandidates_iff _ _ _ _ _ candidate).mp hcandidate
  have hlen := firstExitDepthFrontier_selected_length 3 parent
    (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] (roughPrimeUniverse N cap 0 z) true 1
    (by simp) frontier hfrontier
  obtain ⟨p3, t2, ht3, hl2⟩ := List.length_eq_succ_iff.mp hlen
  obtain ⟨p2, t1, ht2, hl1⟩ := List.length_eq_succ_iff.mp hl2
  obtain ⟨p1, t0, ht1, hl0⟩ := List.length_eq_succ_iff.mp hl1
  have ht0 : t0 = [] := List.length_eq_zero_iff.mp hl0
  have hf : frontier.selectedPrefix = [p3, p2, p1] := by
    rw [← ht3, ← ht2, ← ht1, ht0]
  have hs : candidate.selectedPrefix = [p4, p3, p2, p1] := by simp [hc, hf]
  have hp4 : p4.Prime := hprime p4 (by simp [hs])
  rw [hs] at hsort hremaining hsign hmass
  have hord : p4 < p3 ∧ p3 < p2 ∧ p2 < p1 := by
    simp only [List.pairwise_cons] at hsort
    exact ⟨hsort.1 p3 (by simp), hsort.2.1 p2 (by simp), hsort.2.2.1 p1 (by simp)⟩
  obtain ⟨h43, h32, h21⟩ := hord
  have htrue : candidate.positive = true := by simpa [evenListLength] using hsign
  rw [hf, hs] at hpre
  have hfilter : ([p3, p2, p1].toFinset.filter (fun p => p2 ≤ p)) = {p2, p1} := by
    ext p
    simp only [List.toFinset_cons, List.toFinset_nil, Finset.mem_filter,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty]
    constructor
    · rintro ⟨hp, hge⟩
      rcases hp with rfl | rfl | rfl | hfalse
      · exact False.elim (Nat.not_le_of_lt h32 hge)
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact False.elim hfalse
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), le_rfl⟩
      · exact ⟨Or.inr (Or.inr (Or.inl rfl)), h21.le⟩
  have hsecond : (p1 : ℝ) * p2 ^ 3 < Q [p4, p3, p2, p1] := by
    have hh := hpre.2 p2 (by simp) (by rw [hfilter]; norm_num [h21.ne])
    rw [hfilter] at hh
    simpa [h21.ne, Nat.cast_mul, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hh
  rw [hs, htrue, hmass, hremaining]
  simp only [List.headD_cons]
  rw [frozen_lower_four_ownCube_actualDensity Q N cap p1 p2 p3 p4
    hp4.pos h43 h32 h21 hsecond]
  simp only [actualOwnCubeGatedMinusDensity, List.headD_cons,
    List.prod_cons, List.prod_nil, Nat.cast_mul, mul_one]
  split_ifs <;> ring

/-- At lower rank three to four, restoration has the positive sign: the
new tree minus the old tree sums the new gated lower density minus the old
one, over all candidates at the same parent frontier. -/
theorem actual_frozen_lower_four_ownCube_restoration
    (parent : Bool → List ℕ → Bool) (Q3 Q4 : List ℕ → ℝ)
    (N cap : ℕ) (z : ℝ)
    (hpre : ∀ frontier ∈ firstExitDepthFrontier 3 parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      ordinaryRosserPrefixAdmissible true (Q3 frontier.selectedPrefix) frontier.selectedPrefix)
    (hlevel : ∀ frontier ∈ firstExitDepthFrontier 3 parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z),
      ∀ candidate ∈ firstExitNextSelectionCandidates
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier.selectedPrefix
        frontier.positive frontier.mass frontier.remaining,
        Q3 frontier.selectedPrefix ≤ Q4 candidate.selectedPrefix) :
    firstExitRetainedPolynomial
        (firstExitDepthSplicePolicy 3 parent (frozenParityRosserPolicy true 4 Q4))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial
        (firstExitDepthSplicePolicy 3 parent (frozenParityRosserPolicy true 3 Q3))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      ((firstExitDepthFrontier 3 parent (fun p : ℕ => 1 / ((p : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z)).map (fun frontier =>
        ((firstExitNextSelectionCandidates (fun p : ℕ => 1 / ((p : ℝ) - 1))
          frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining).map
          (fun candidate =>
            (candidate.selectedPrefix.map (fun p : ℕ => 1 / ((p : ℝ) - 1))).prod *
              (actualOwnCubeGatedMinusDensity N cap Q4 candidate.selectedPrefix -
                actualOwnCubeGatedMinusDensity N cap
                  (fun pre => Q3 (rosserAncestor 3 pre)) candidate.selectedPrefix))).sum)).sum := by
  rw [← frozenParityRosserPolicy_nested true 3 4 (by omega) Q3,
    firstExitRetainedPolynomial_ownCubeSplice_root_sub_eq]
  apply congrArg List.sum
  apply List.map_congr_left
  intro frontier hfrontier
  apply congrArg List.sum
  apply List.map_congr_left
  intro candidate hcandidate
  have hancestor := (actual_nextSelection_tail_ancestor 3 parent N cap z
    frontier hfrontier candidate hcandidate).2
  have hold : ordinaryRosserPrefixAdmissible true
      ((fun pre => Q3 (rosserAncestor 3 pre)) candidate.selectedPrefix)
      frontier.selectedPrefix := by
    simpa only [hancestor] using hpre frontier hfrontier
  have hnew := ordinaryRosserPrefixAdmissible_mono true frontier.selectedPrefix
    (hlevel frontier hfrontier candidate hcandidate) (hpre frontier hfrontier)
  rw [actual_frozen_lower_four_candidate_density parent Q4 N cap z
      frontier hfrontier candidate hcandidate hnew,
    actual_frozen_lower_four_candidate_density parent
      (fun pre => Q3 (rosserAncestor 3 pre)) N cap z frontier hfrontier candidate hcandidate hold]
  ring

end

end ImbalancedChen
