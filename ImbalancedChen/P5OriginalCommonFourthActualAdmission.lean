import ImbalancedChen.P5OriginalCommonRefinedPreservation
import ImbalancedChen.Part3ActualRetainedAncestorTests
import ImbalancedChen.ActualFrozenOwnCubeDensity

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual common rank-four frontier supplies its own full admissibility
at the actual fourth cap. This is derived from real ancestor tests and
the disjoint original second/third regions, rather than assumed as an
admissibility field in the eventual physical fifth-density caller.
No range, desired saving, common approximation, PP or K is a premise.
-/
namespace ImbalancedChen.P5OriginalCommonFourthActualAdmission
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P5OriginalAboveMuThirdLowerPhysicalCoefficient

private theorem third_guard_false_of_second (N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 3) (hs : secondGuard N pre) : ¬thirdGuard N pre := by
  have h0 : primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 0 =
      primeHistoryLogCoordinates N 3 pre 0 :=
    primeHistoryLogCoordinates_ancestor N hlen (by decide : 2 ≤ 3) (0 : Fin 2)
  have h1 : primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 1 =
      primeHistoryLogCoordinates N 3 pre 1 :=
    primeHistoryLogCoordinates_ancestor N hlen (by decide : 2 ≤ 3) (1 : Fin 2)
  change SecondRegion (primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 0)
    (primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 1) at hs
  rw [h0, h1] at hs
  intro ht
  change ThirdRegion (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 0)
    (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 1)
    (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 2) at ht
  rw [rosserAncestor_self_of_length 3 pre hlen] at ht
  exact above_mu_regions_disjoint hs ht

/-- The actual common third selection passes the ordinary test at the
literal common lambda3, even when it was admitted by the second action. -/
theorem actual_common_third_admissible (d : OriginalData) (N : ℝ) (hN : 1 ≤ N)
    (pre : List ℕ) (hlen : pre.length = 3) (hp : common3 d N false pre = true) :
    ordinaryRosserPrefixAdmissible false (N ^ lambda3 d N pre) pre := by
  have hold (ho : old3 d N false pre = true) :
      ordinaryRosserPrefixAdmissible false (N ^ lambda3 d N pre) pre := by
    rw [old3_after_two d N false pre (by omega)] at ho
    have ha : ordinaryRosserPrefixAdmissible false (N ^ originalSeed d N pre) pre := by
      simpa only [ordinaryParityRosserPolicy, Bool.false_eq_true, if_false,
        oddFirstExitPolicy, Bool.false_or, decide_eq_true_eq] using ho
    exact ordinaryRosserPrefixAdmissible_mono false pre
      (Real.rpow_le_rpow_of_exponent_le hN (le_max_left _ _)) ha
  rcases Bool.or_eq_true.mp hp with ho | hf
  · exact hold ho
  · by_cases hs : secondGuard N pre
    · have ht := third_guard_false_of_second N pre hlen hs
      have ha : ordinaryRosserPrefixAdmissible false
          (N ^ VariableEnvelope.v (primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 1)) pre := by
        simpa [fallback23, finalPolicy, secondPolicy, firstExitDepthSplicePolicy, hlen,
          secondReplacement, hs, ordinaryParityRosserPolicy, oddFirstExitPolicy] using hf
      have hl : VariableEnvelope.v (primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 1) ≤
          lambda3 d N pre := by
        have hh := le_max_right (originalSeed d N pre) (fallbackSeed d N pre)
        simpa only [fallbackSeed, if_neg ht, if_pos hs] using hh
      exact ordinaryRosserPrefixAdmissible_mono false pre
        (Real.rpow_le_rpow_of_exponent_le hN hl) ha
    · apply hold
      simpa [fallback23, finalPolicy, secondPolicy, firstExitDepthSplicePolicy, hlen,
        secondReplacement, hs, oldPolicy, old3] using hf

/-- Full ordinary validity at the real fourth ancestor is recovered from
the actual recursive common frontier. Its even fourth test alone would
not suffice. The third and first inherited tests are retained. -/
theorem actual_common_fourth_frontier_admissible (d : OriginalData)
    (N cap : ℕ) (hN : 1 ≤ (N : ℝ)) (z : ℝ) (state : FirstExitDepthState ℕ)
    (hs : state ∈ firstExitDepthFrontier 4 (common3 d (N : ℝ))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z)) :
    ordinaryRosserPrefixAdmissible false (level4 d (N : ℝ) state.selectedPrefix)
      state.selectedPrefix := by
  let H := state.selectedPrefix
  have hlen : H.length = 4 := firstExitDepthFrontier_selected_length 4 _ _ [] _ true 1
    (by simp) state hs
  have hleaf := firstExitDepthFrontier_toLeaf_mem 4 _ _ [] _ true 1 state hs
  have hat := Part3.ActualRetainedAncestorTests.retained_leaf_ancestor_tests
    (common3 d (N : ℝ)) (fun p : ℕ => 1 / ((p : ℝ) - 1))
    (roughPrimeUniverse N cap 0 z) _ hleaf
  have h3len : (rosserAncestor 3 H).length = 3 := by
    rw [rosserAncestor_length, hlen]
    decide
  have h3sign : evenListLength (rosserAncestor 3 H) = false := by
    rw [evenListLength_eq_decide_even, h3len]
    decide
  have hpass : common3 d (N : ℝ) false (rosserAncestor 3 H) = true := by
    simpa only [h3sign] using hat 3 (by decide) (by omega : 3 ≤ H.length)
  have h3 := actual_common_third_admissible d (N : ℝ) hN _ h3len hpass
  have hlev : (N : ℝ) ^ lambda3 d (N : ℝ) (rosserAncestor 3 H) ≤
      level4 d (N : ℝ) H := by
    rw [lambda3_ancestor d (N : ℝ) 3 (by decide) H]
    exact Real.rpow_le_rpow_of_exponent_le hN (lambda3_le_exponent4 d (N : ℝ) H)
  have h3raised := ordinaryRosserPrefixAdmissible_mono false _ hlev h3
  obtain ⟨q, pre, hH, hprelen⟩ := List.length_eq_succ_iff.mp hlen
  have ha : rosserAncestor 3 H = pre := by
    rw [← hH, rosserAncestor_cons 3 q pre (by omega), rosserAncestor_self_of_length 3 pre hprelen]
  rw [ha] at h3raised
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 4 _ _ _ state hs
  have hqmem : q ∈ roughPrimeUniverse N cap 0 z := by
    apply hsub.subset
    apply List.mem_reverse.mpr
    rw [← hH]
    simp
  have hsort : (q :: pre).Pairwise (· < ·) := by
    have hh := (roughPrimeUniverse_pairwise_gt N cap 0 z).sublist hsub
    simpa only [H, ← hH, List.pairwise_reverse] using hh
  have heq := ordinaryParityRosserPolicy_eq_full_on_valid_prefix false
    (level4 d (N : ℝ) H) pre false q h3raised
    (by rw [evenListLength_eq_decide_even, hprelen]; decide)
    (mem_roughPrimeUniverse_prime hqmem) (by intro h; cases h) hsort
  have ht := ordinaryParityRosserPolicy_upper_even (level4 d (N : ℝ) H) (q :: pre)
  change ordinaryParityRosserPolicy false (level4 d (N : ℝ) H) (!false) (q :: pre) = true at ht
  rw [heq] at ht
  have hadm : ordinaryRosserPrefixAdmissible false (level4 d (N : ℝ) H) (q :: pre) :=
    of_decide_eq_true ht
  simpa only [hH] using hadm

end
end ImbalancedChen.P5OriginalCommonFourthActualAdmission
