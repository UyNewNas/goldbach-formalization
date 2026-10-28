import ImbalancedChen.P4AOriginalAscendingCell2ActualChronology
import ImbalancedChen.P5OriginalCommonRefinedAncestry
import ImbalancedChen.P4AActualEighthInheritedHistoryGuard

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Consume the independently frozen common-refined constructor, not an assumed
identity with the old actual58Candidate. Both corrected fallback caps are
actual source-subset tents on cell2, hence bounded by R. The newly reseeded
fourth/fifth cap and literal eleven-family lambda6 are bounded directly.
This transports the actual ancestor guard to the shared physical frontier.
It does not identify all87 replacement/ownership with the slot16 source.
-/
namespace ImbalancedChen.P4AOriginalCell2CommonRefinedParent
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P2OriginalAscendingEighthCapDictionary
open P4AOriginalAscending14Literal42 P4AOriginalAscendingCell2Affine
open P4AOriginalAscendingCell2ActualChronology
open P4AOriginalCell0HalfOpenPrimeCarrier
open P1OriginalVariableFourthContinuation P1OriginalVariableFifthContinuation

/-- On a genuine cell2 history every corrected fallbackSeed branch is a
real subset tent already bounded by the source's old plane system. -/
theorem common_lambda3_le_R (d : P5OriginalCommonRefinedConstructor.OriginalData)
    (N : ℝ) (he : 0 ≤ d.e) (pre : List ℕ) (hlen : pre.length = 8)
    (ht : literalRows (point8 N pre))
    (hs : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
      (rosserAncestor 3 pre)) :
    P5OriginalCommonRefinedConstructor.lambda3 d N (rosserAncestor 4 pre) ≤ R (point8 N pre) := by
  have hold : P5OriginalCommonRefinedConstructor.originalSeed d N (rosserAncestor 4 pre) ≤
      R (point8 N pre) := by
    simpa only [P5OriginalCommonRefinedConstructor.originalSeed, seedExponent,
      rosserAncestor_nested 3 4 (by decide)] using
      supported_third_seed_le_R d.e d.chi d.m d.omega N he pre hlen ht hs
  unfold P5OriginalCommonRefinedConstructor.lambda3
  apply max_le hold
  unfold P5OriginalCommonRefinedConstructor.fallbackSeed
  split_ifs
  · have h := ancestor_subset_tent_le_R N pre hlen ht 3 (by decide) ({1,2} : Finset (Fin 3))
    simpa [rosserAncestor_nested 3 4 (by decide)] using h
  · have h := ancestor_subset_tent_le_R N pre hlen ht 2 (by decide) ({1} : Finset (Fin 2))
    simpa [rosserAncestor_nested 2 4 (by decide)] using h
  · exact hold

/-- These are the shared constructor's NEW actual fourth/fifth values.
They are not rewritten to the old predecessor values. -/
theorem common_actual_fifth_le_R (d : P5OriginalCommonRefinedConstructor.OriginalData)
    (N : ℝ) (he : 0 ≤ d.e) (pre : List ℕ) (hlen : pre.length = 8)
    (ht : literalRows (point8 N pre))
    (hs : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
      (rosserAncestor 3 pre)) :
    P5OriginalCommonRefinedConstructor.actualParent5 d N (rosserAncestor 6 pre) ≤ R (point8 N pre) := by
  have heR : (0 : ℝ) ≤ d.e := by exact_mod_cast he
  have hseed := common_lambda3_le_R d N he pre hlen ht hs
  have h4len : (rosserAncestor 4 pre).length = 4 := by simp [hlen]
  have h5len : (rosserAncestor 5 pre).length = 5 := by simp [hlen]
  have h4 : P5OriginalCommonRefinedConstructor.exponent4 d N (rosserAncestor 4 pre) ≤
      R (point8 N pre) := by
    rw [P5OriginalCommonRefinedConstructor.exponent4, if_pos h4len]
    apply finiteMax_le
    · exact hseed
    · intro r _ _
      rw [r.bufferedCandidate_eq]
      have hr := ancestor_subset_tent_le_R N pre hlen ht 4 (by decide) r.selected
      linarith
  change P5OriginalCommonRefinedConstructor.exponent5 d N
    (rosserAncestor 5 (rosserAncestor 6 pre)) ≤ _
  rw [rosserAncestor_nested 5 6 (by decide),
    P5OriginalCommonRefinedConstructor.exponent5, if_pos h5len,
    rosserAncestor_nested 4 5 (by decide)]
  apply finiteMax_le
  · exact h4
  · intro r _ _
    have hr := ancestor_subset_tent_le_R N pre hlen ht 5 (by decide) r.selected
    rw [candidate, envelope_eq_v]
    linarith

/-- The eleven source regions remain incompatible with cell2 even when
their eligibility is re-tested against the NEW actual fifth parent. -/
theorem common_lambda6_eq_new_actual_parent
    (d : P5OriginalCommonRefinedConstructor.OriginalData) (N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 8) (ht : literalRows (point8 N pre)) :
    P5OriginalCommonRefinedConstructor.lambda6 d N (rosserAncestor 6 pre) =
      P5OriginalCommonRefinedConstructor.actualParent5 d N (rosserAncestor 6 pre) := by
  apply P5OriginalCommonRefinedConstructor.lambda6_eq_parent_of_no_eligible
  intro c _ hc
  have hphys := hc.2.1
  have hid : primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre) = first6 (point8 N pre) := by
    funext i
    exact primeHistoryLogCoordinates_ancestor N hlen (by decide : 6 ≤ 8) i
  rw [hid] at hphys
  exact cell2_no_sixth_PhysicalCell _ ht c hphys

/-- A real retained state of the common physical policy supplies its own
new sixth ancestor guard. No equality with the old actual58 tree is used. -/
theorem shared_frontier_CurrentParentGuard
    (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selected2 d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))) :
    HistoricalThirdCoarse.firstStop (d.e : ℝ) d.m (N : ℝ) (rosserAncestor 1 s.selectedPrefix) ∧
    CurrentParentGuard (point8 (N : ℝ) s.selectedPrefix)
      (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix)) := by
  have hm : s ∈ firstExitDepthFrontier 8
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))
      (fun p => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap w z) ∧
      ∃ j ∈ bank2 d.e d.chi d.m d.omega,
        primeHistoryTuple 8 s.selectedPrefix ∈ primeBox d.m N j := by
    simpa only [selected2, List.mem_filter, decide_eq_true_eq] using hs
  obtain ⟨hf, j, hj, hp⟩ := hm
  have hf6 := hf
  rw [P5OriginalCommonRefinedAncestry.policy8_frontier_eight_eq_six] at hf6
  have hlen := firstExitDepthFrontier_selected_length 8 _ _ []
    (roughPrimeUniverse N cap w z) true 1 (by simp) s hf
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 8 _ _ _ s hf
  have hpos : ∀ p ∈ s.selectedPrefix, 0 < p := by
    intro p hp
    exact (mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp))).pos
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hrows, hstop, hsupport⟩ := bank2_rows_stop_support d.e d.chi d.m d.omega (N : ℝ)
    hNr s.selectedPrefix hlen hpos j hj (primeBox_log hN j _ hp)
  have hup : P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)
      (rosserAncestor 6 s.selectedPrefix) ≤ R (point8 (N : ℝ) s.selectedPrefix) := by
    rw [common_lambda6_eq_new_actual_parent d (N : ℝ) s.selectedPrefix hlen hrows]
    exact common_actual_fifth_le_R d (N : ℝ) he s.selectedPrefix hlen hrows hsupport
  have hlo := P4AActualEighthInheritedHistoryGuard.actual_log_history7_lt_current
    (P5OriginalCommonRefinedConstructor.policy5 d (N : ℝ))
    (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ))
    N cap hNr w z (fun p => 1 / ((p : ℝ) - 1)) s hf6
  have heq : P2OriginalDescendingEighthLogSemantics.history7
      (point8 (N : ℝ) s.selectedPrefix) = oddCube (point8 (N : ℝ) s.selectedPrefix) 6 := by
    norm_num [P2OriginalDescendingEighthLogSemantics.history7, oddCube, prefixSum,
      Finset.sum_filter, Fin.sum_univ_succ]
    ring
  rw [heq] at hlo
  exact ⟨hstop, hlo, hup⟩

/-- The original slot16 chronology is evaluated using the NEW common
lambda6 on the same actual prefix. This is a slot cap identity; the
complete policy8 all87 replacement identity remains a separate obligation. -/
theorem shared_frontier_slot16
    (d : P5OriginalCommonRefinedConstructor.OriginalData) (he : 0 ≤ d.e)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selected2 d.e d.chi d.m d.omega N cap w z
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))) :
    P4AOriginalPrior58Chronology.slot16 (N : ℝ)
      (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix =
        M (point8 (N : ℝ) s.selectedPrefix) := by
  have hg := (shared_frontier_CurrentParentGuard d he N cap hN w z s hs).2
  have hr := selected2_source_rows d.e d.chi d.m d.omega N cap hN w z
    (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ)) s hs
  have hf : s ∈ firstExitDepthFrontier 8
      (P5OriginalCommonRefinedConstructor.policy8 d (N : ℝ))
      (fun p => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap w z) :=
    (List.mem_filter.mp hs).1
  have hlen := firstExitDepthFrontier_selected_length 8 _ _ []
    (roughPrimeUniverse N cap w z) true 1 (by simp) s hf
  let t := point8 (N : ℝ) s.selectedPrefix
  have ha : ascending14Owns t :=
    ⟨2, (mem_selectedCellIndices 2).2 (by decide), literalRows_cellGuard t hr⟩
  have hnot : ¬ P4AOriginalSeed7Unequal15Literal.ActualSeed7 (N : ℝ)
      (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix := by
    intro hh
    exact P4AOriginalAscendingCell0AfterSeed7.cell0_seed7_affine_disjoint t
      (literalRows_core t hr) hh.2.1
  have h15 : P4AOriginalPrior58Chronology.slot15 (N : ℝ)
      (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix =
        P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) := by
    simp [P4AOriginalPrior58Chronology.slot15, P4AOriginalSeed7Unequal15Literal.seed7Raised,
      hnot, P4AOriginalSeed7Unequal15Literal.currentSixth]
  have h16 : literal16Exponent (N : ℝ)
      (P5OriginalCommonRefinedConstructor.lambda6 d (N : ℝ)) s.selectedPrefix = M t := by
    simp [literal16Exponent, familyNextExponent, ha, hg, t, point8, inheritedExponent]
  have hle := hg.2.trans (literalRows_cellGuard t hr).improvement.le
  simp only [P4AOriginalPrior58Chronology.slot16, h15, h16, max_eq_right hle]

end
end ImbalancedChen.P4AOriginalCell2CommonRefinedParent
