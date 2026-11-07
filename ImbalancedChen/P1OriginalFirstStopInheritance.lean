import ImbalancedChen.HistoricalThirdCoarsePolicy
import ImbalancedChen.FirstExitFrontierInvariants
import ImbalancedChen.FirstExitValidSelection
import ImbalancedChen.FirstExitCandidateGeometry
import ImbalancedChen.FrozenRosserPolicy

/-!
# The original rank-one stop survives the actual coarse third tree

The first test is recovered from the valid selected sublist of a real
retained leaf. Frontier membership is reduced to that same real leaf.
The argument keeps the initial cube at `N ^ initial e`, independently
of every later selected third level and of rough activation.
-/

namespace ImbalancedChen.P1OriginalFirstStopInheritance

noncomputable section

open scoped Classical
open HistoricalThirdCoarse
open VariableEnvelope
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

/-- The literal first selection of the actual policy pays both the
complete original singleton test and its original coarse-label stop. -/
theorem singleton_original_tests (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (p : ℕ) (hpass : policy e chi m omega N false [p] = true) :
    ordinaryRosserPrefixAdmissible false (N ^ initial e) [p] ∧
      firstStop e m N [p] ∧ (p : ℝ) ^ 3 < N ^ initial e := by
  rw [policy_through_two e chi m omega N false [p] (by simp)] at hpass
  have htests : ordinaryRosserPrefixAdmissible false (N ^ initial e) [p] ∧
      firstStop e m N [p] := by
    simpa [initialPolicy, oddFirstExitPolicy] using hpass
  have hc : UpperAdmissibleSet (N ^ initial e) [p].toFinset ↔
      (p : ℝ) ^ 3 < N ^ initial e := by
    simp [UpperAdmissibleSet, Finset.filter_singleton, pow_succ, mul_comm]
  have hupper : UpperAdmissibleSet (N ^ initial e) [p].toFinset := by
    simpa only [ordinaryRosserPrefixAdmissible, Bool.false_eq_true, if_false]
      using htests.1.2
  exact ⟨htests.1, htests.2, hc.mp hupper⟩

/-- Every nonempty actual retained leaf has an actual first selected
carrier entry. Its tests are extracted from tree membership, not supplied
as validity or admissibility premises. -/
theorem retained_leaf_original_first_witness
    (e chi : ℝ) (m : ℕ) (omega N : ℝ) (weight : ℕ → ℝ)
    (carrier : List ℕ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (policy e chi m omega N)
      weight [] true 1 carrier)
    (hrank : 0 < leaf.selected.length) :
    ∃ p : ℕ, p ∈ carrier ∧ rosserAncestor 1 leaf.selected = [p] ∧
      primeHistoryTuple 1 leaf.selected 0 = p ∧
      ordinaryRosserPrefixAdmissible false (N ^ initial e) [p] ∧
      firstStop e m N [p] ∧ (p : ℝ) ^ 3 < N ^ initial e := by
  obtain ⟨chosen, hsub, hvalid, hselected⟩ :=
    exists_validSelection_of_mem_firstExitRetainedLeaves
      (policy e chi m omega N) weight [] carrier true 1 leaf hleaf
  cases chosen with
  | nil =>
      simp [hselected] at hrank
  | cons p ps =>
      have hpass : policy e chi m omega N false [p] = true := by
        simpa only [Bool.not_true] using hvalid.1
      have htests := singleton_original_tests e chi m omega N p hpass
      have hp : p ∈ carrier := hsub.subset (by simp)
      have hancestor : rosserAncestor 1 leaf.selected = [p] := by
        rw [hselected, List.append_nil, List.reverse_cons,
          rosserAncestor_append 1 ps.reverse [p] (by simp)]
        simp [rosserAncestor]
      have hcoord : primeHistoryTuple 1 leaf.selected 0 = p := by
        simp [hselected, primeHistoryTuple]
      exact ⟨p, hp, hancestor, hcoord, htests.1, htests.2.1, htests.2.2⟩

/-- Direct leaf API: the original firstStop and the initial first cube
are both inherited by its actual rank-one ancestor. -/
theorem retained_leaf_original_first_tests
    (e chi : ℝ) (m : ℕ) (omega N : ℝ) (weight : ℕ → ℝ)
    (carrier : List ℕ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (policy e chi m omega N)
      weight [] true 1 carrier)
    (hrank : 0 < leaf.selected.length) :
    firstStop e m N (rosserAncestor 1 leaf.selected) ∧
      (primeHistoryTuple 1 leaf.selected 0 : ℝ) ^ 3 < N ^ initial e := by
  obtain ⟨p, _hp, hancestor, hcoord, _hadm, hstop, hcube⟩ :=
    retained_leaf_original_first_witness e chi m omega N weight carrier leaf hleaf hrank
  rw [hancestor, hcoord]
  exact ⟨hstop, hcube⟩

/-- Every actual positive-rank frontier inherits the original first
tests even though the policy changes at the third selection. -/
theorem frontier_original_first_tests
    (e chi : ℝ) (m : ℕ) (omega N : ℝ) (weight : ℕ → ℝ)
    (carrier : List ℕ) (k : ℕ) (hk : 0 < k)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k (policy e chi m omega N)
      weight [] true 1 carrier) :
    firstStop e m N (rosserAncestor 1 state.selectedPrefix) ∧
      (primeHistoryTuple 1 state.selectedPrefix 0 : ℝ) ^ 3 < N ^ initial e := by
  have hlen := firstExitDepthFrontier_selected_length k
    (policy e chi m omega N) weight [] carrier true 1 (by simp) state hstate
  have hleaf := firstExitDepthFrontier_toLeaf_mem k
    (policy e chi m omega N) weight [] carrier true 1 state hstate
  exact retained_leaf_original_first_tests e chi m omega N weight carrier
    {selected := state.selectedPrefix, positive := state.positive, mass := state.mass}
    hleaf (by simpa only [hlen] using hk)

/-- The original first-stop endpoint is transported to the actual first
processing coordinate of the full frontier tuple. The closed endpoint
stop and the strict cell face are both retained. -/
theorem frontier_original_first_cell
    (e chi : ℝ) (m : ℕ) (omega N : ℝ) (weight : ℕ → ℝ)
    (carrier : List ℕ) (k : ℕ) (hk : 0 < k)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k (policy e chi m omega N)
      weight [] true 1 carrier) :
    ∃ i : Fin (m + 1),
      logPrimeMeshPoint 0 (19 / 96) m i.val ≤
        primeHistoryLogCoordinates N k state.selectedPrefix ⟨0, hk⟩ ∧
      primeHistoryLogCoordinates N k state.selectedPrefix ⟨0, hk⟩ <
        logPrimeMeshPoint 0 (19 / 96) m (i.val + 1) ∧
      logPrimeMeshPoint 0 (19 / 96) m (i.val + 1) ≤ extendedFirstStop - 4 * e := by
  have hlen := firstExitDepthFrontier_selected_length k
    (policy e chi m omega N) weight [] carrier true 1 (by simp) state hstate
  have hstop := (frontier_original_first_tests
    e chi m omega N weight carrier k hk state hstate).1
  obtain ⟨i, hlo, hhi, hstop⟩ := hstop
  have hcoord := primeHistoryLogCoordinates_ancestor N hlen (by omega : 1 ≤ k) (0 : Fin 1)
  have hlo' : logPrimeMeshPoint 0 (19 / 96) m i.val ≤
      primeHistoryLogCoordinates N k state.selectedPrefix ⟨0, hk⟩ := by
    simpa only [hcoord] using hlo
  have hhi' : primeHistoryLogCoordinates N k state.selectedPrefix ⟨0, hk⟩ <
      logPrimeMeshPoint 0 (19 / 96) m (i.val + 1) := by
    simpa only [hcoord] using hhi
  exact ⟨i, hlo', hhi', hstop⟩

/-- A next candidate need not pass its own old or new gate. Its already
retained first ancestor nevertheless keeps the original stop and cube. -/
theorem next_candidate_original_first_tests
    (e chi : ℝ) (m : ℕ) (omega N : ℝ) (weight : ℕ → ℝ)
    (carrier : List ℕ) (k : ℕ) (hk : 0 < k)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k (policy e chi m omega N)
      weight [] true 1 carrier)
    (candidate : FirstExitDepthState ℕ)
    (hcandidate : candidate ∈ firstExitNextSelectionCandidates weight
      frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining) :
    firstStop e m N (rosserAncestor 1 candidate.selectedPrefix) ∧
      (primeHistoryTuple 1 (rosserAncestor 1 candidate.selectedPrefix) 0 : ℝ) ^ 3 <
        N ^ initial e := by
  have hlen := firstExitDepthFrontier_selected_length k
    (policy e chi m omega N) weight [] carrier true 1 (by simp) frontier hfrontier
  have htests := frontier_original_first_tests
    e chi m omega N weight carrier k hk frontier hfrontier
  obtain ⟨_before, q, _after, _hremaining, hcandidate_eq⟩ :=
    (mem_firstExitNextSelectionCandidates_iff weight frontier.selectedPrefix
      frontier.remaining frontier.positive frontier.mass candidate).1 hcandidate
  have hancestor : rosserAncestor 1 candidate.selectedPrefix =
      rosserAncestor 1 frontier.selectedPrefix := by
    rw [hcandidate_eq]
    exact rosserAncestor_cons 1 q frontier.selectedPrefix (by omega)
  have hcoord := primeHistoryTuple_ancestor hlen (by omega : 1 ≤ k) (0 : Fin 1)
  have hcube :
      (primeHistoryTuple 1 (rosserAncestor 1 frontier.selectedPrefix) 0 : ℝ) ^ 3 <
        N ^ initial e := by
    rw [hcoord]
    exact htests.2
  rw [hancestor]
  exact ⟨htests.1, hcube⟩

/-- The rank-four T3 frontier and every enumerated fifth candidate share
the same original first test without a separate rank-one hypothesis. -/
theorem rankFour_and_fifth_original_first_tests
    (e chi : ℝ) (m : ℕ) (omega N : ℝ) (weight : ℕ → ℝ)
    (carrier : List ℕ) (frontier candidate : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier 4 (policy e chi m omega N)
      weight [] true 1 carrier)
    (hcandidate : candidate ∈ firstExitNextSelectionCandidates weight
      frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining) :
    (firstStop e m N (rosserAncestor 1 frontier.selectedPrefix) ∧
      (primeHistoryTuple 1 frontier.selectedPrefix 0 : ℝ) ^ 3 < N ^ initial e) ∧
    (firstStop e m N (rosserAncestor 1 candidate.selectedPrefix) ∧
      (primeHistoryTuple 1 (rosserAncestor 1 candidate.selectedPrefix) 0 : ℝ) ^ 3 <
        N ^ initial e) := by
  exact ⟨frontier_original_first_tests e chi m omega N weight carrier 4 (by omega)
      frontier hfrontier,
    next_candidate_original_first_tests e chi m omega N weight carrier 4 (by omega)
      frontier hfrontier candidate hcandidate⟩

end

end ImbalancedChen.P1OriginalFirstStopInheritance
