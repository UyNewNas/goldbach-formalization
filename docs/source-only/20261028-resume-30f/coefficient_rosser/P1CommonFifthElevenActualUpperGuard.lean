import ImbalancedChen.P1ActualOriginalAndCommonFifthGuard
import ImbalancedChen.P2InheritedFourthRaw31Embedding
import ImbalancedChen.P5OriginalCommonRefinedPreservation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The independent COMMON constructor is bounded directly, with its actual
re-seeded maxima. Every fourth/fifth selected subset and both corrected
fallback tents belong to the ORIGINAL eleven-cell raw31 envelope. The
only extra seed is the original unsupported-third Theta fallback.

On a real PhysicalCell the upper guard is exactly: supported original
third ancestor OR literal initial(e)<=oldCap. This is a missing-condition
classification, not a claim that every raw physical point is supported.
The original licence, rows, current caps and eligibility are unchanged.
-/

namespace ImbalancedChen.P1CommonFifthElevenActualUpperGuard

noncomputable section
open scoped Classical BigOperators
open VariableEnvelope HistoricalThirdCoarse
open P2OriginalFourthCapProducerInterface P1OriginalVariableFourthContinuation
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open Certificates.P2OriginalSixthElevenLogSemantics

private theorem v_eq_tent (s : ℝ) : v s = tent s := by
  rw [v_eq_min]
  simp only [A, C, tent]
  congr 1
  ring

/-- The existing raw31 interface uses numeric masks. This finite exact
dictionary additionally covers an arbitrary actual selected subset. The
closed decision term is source text only and has not been evaluated. -/
private theorem fin5_nonempty_mask (I : Finset (Fin 5)) (hI : I.Nonempty) :
    ∃ mask ∈ Finset.Icc 1 31, ∀ i : Fin 5, bit mask i.val = decide (i ∈ I) := by
  have hcode : ∀ I : Finset (Fin 5), I.Nonempty →
      ∃ b : Fin 32, 0 < b.val ∧ ∀ i : Fin 5, bit b.val i.val = decide (i ∈ I) := by decide
  obtain ⟨b, hb, hbits⟩ := hcode I hI
  exact ⟨b.val, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hbits⟩

/-- ALL actual first-five subsets, including the empty subset, are paid
by the original old branch planes. No row geometry or new cap bound is
a premise. Empty v(0)=1/2 is below R0<=oldCap by actual positivity. -/
theorem subset_tent_le_oldCap (c : Cell) (t : Physical) (hc : PhysicalCell c t)
    (I : Finset (Fin 5)) : v (∑ i ∈ I, t i.castSucc) ≤ oldCap c t := by
  by_cases hi : I.Nonempty
  · obtain ⟨mask, hm, hbits⟩ := fin5_nonempty_mask I hi
    have hsum : (∑ i ∈ I, t i.castSucc) = subsetSum mask t := by
      unfold subsetSum
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hbits i]
        simp
      · intro i _
        rfl
    rw [hsum, v_eq_tent]
    exact hc.raw_envelope.2.1 mask hm
  · have hI : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hi
    have hx := hc.coordinates_pos 0
    have hr : (1 / 2 : ℝ) ≤ R0 t := by dsimp [R0]; linarith
    have hzero : v (0 : ℝ) = 1 / 2 := by rw [v_eq_tent]; norm_num [tent]
    simpa only [hI, Finset.sum_empty, hzero] using hr.trans hc.comparison

theorem ancestor_subset_tent_le_oldCap (c : Cell) (N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 6) (hc : PhysicalCell c (primeHistoryLogCoordinates N 6 pre))
    (k : ℕ) (hk : k ≤ 5) (I : Finset (Fin k)) :
    v (∑ i ∈ I, primeHistoryLogCoordinates N k (rosserAncestor k pre) i) ≤
      oldCap c (primeHistoryLogCoordinates N 6 pre) := by
  let emb : Fin k ↪ Fin 5 := ⟨fun i => i.castLE hk, by
    intro i j h
    exact Fin.ext (congrArg Fin.val h)⟩
  let J := I.map emb
  have hsum : (∑ i ∈ I, primeHistoryLogCoordinates N k (rosserAncestor k pre) i) =
      ∑ i ∈ J, primeHistoryLogCoordinates N 6 pre i.castSucc := by
    simp only [J, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    exact primeHistoryLogCoordinates_ancestor N hlen (by omega : k ≤ 6) i
  rw [hsum]
  exact subset_tent_le_oldCap c _ hc J

/-- Every fallback case reads an actual first-three/first-two subset tent,
or the unchanged originalSeed. No old/common exponent is identified. -/
theorem common_lambda3_le_oldCap_of_original_seed
    (d : OriginalData) (N : ℝ) (c : Cell) (pre : List ℕ) (hlen : pre.length = 6)
    (hc : PhysicalCell c (primeHistoryLogCoordinates N 6 pre))
    (hseed : originalSeed d N (rosserAncestor 4 pre) ≤
      oldCap c (primeHistoryLogCoordinates N 6 pre)) :
    lambda3 d N (rosserAncestor 4 pre) ≤ oldCap c (primeHistoryLogCoordinates N 6 pre) := by
  unfold lambda3
  apply max_le hseed
  unfold fallbackSeed
  split_ifs
  · have h := ancestor_subset_tent_le_oldCap c N pre hlen hc 3 (by decide)
      ({1, 2} : Finset (Fin 3))
    simpa [rosserAncestor_nested 3 4 (by decide)] using h
  · have h := ancestor_subset_tent_le_oldCap c N pre hlen hc 2 (by decide)
      ({1} : Finset (Fin 2))
    simpa [rosserAncestor_nested 2 4 (by decide)] using h
  · exact hseed

/-- Both re-seeded finite maxima are controlled by their own actual seed
and the source's ORIGINAL subset planes. Row eligibility is unchanged and
arbitrary licensed rows are allowed; no replacement licence is introduced. -/
theorem actualParent5_le_oldCap_of_original_seed
    (d : OriginalData) (N : ℝ) (he : 0 ≤ d.e) (c : Cell) (pre : List ℕ)
    (hlen : pre.length = 6) (hc : PhysicalCell c (primeHistoryLogCoordinates N 6 pre))
    (hseed : originalSeed d N (rosserAncestor 4 pre) ≤
      oldCap c (primeHistoryLogCoordinates N 6 pre)) :
    actualParent5 d N pre ≤ oldCap c (primeHistoryLogCoordinates N 6 pre) := by
  have heR : (0 : ℝ) ≤ d.e := by exact_mod_cast he
  have h3 := common_lambda3_le_oldCap_of_original_seed d N c pre hlen hc hseed
  have h4len : (rosserAncestor 4 pre).length = 4 := by simp [hlen]
  have h5len : (rosserAncestor 5 pre).length = 5 := by simp [hlen]
  have h4 : P5OriginalCommonRefinedConstructor.exponent4 d N (rosserAncestor 4 pre) ≤
      oldCap c (primeHistoryLogCoordinates N 6 pre) := by
    rw [P5OriginalCommonRefinedConstructor.exponent4, if_pos h4len]
    apply finiteMax_le
    · exact h3
    · intro r _ _
      rw [r.bufferedCandidate_eq]
      have h := ancestor_subset_tent_le_oldCap c N pre hlen hc 4 (by decide) r.selected
      linarith
  unfold actualParent5
  rw [P5OriginalCommonRefinedConstructor.exponent5, if_pos h5len,
    rosserAncestor_nested 4 5 (by decide)]
  apply finiteMax_le
  · exact h4
  · intro r _ _
    rw [P1OriginalVariableFifthContinuation.candidate,
      P1OriginalVariableFifthContinuation.envelope_eq_v]
    have h := ancestor_subset_tent_le_oldCap c N pre hlen hc 5 (by decide) r.selected
    linarith

/-- The genuine old-third support discharges the only non-tent seed. This
applies uniformly to all eleven original cells and the NEW common parent. -/
theorem actualParent5_le_oldCap_on_supported_source
    (d : OriginalData) (N : ℝ) (he : 0 ≤ d.e) (c : Cell) (pre : List ℕ)
    (hlen : pre.length = 6) (hc : PhysicalCell c (primeHistoryLogCoordinates N 6 pre))
    (hs : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
      (rosserAncestor 3 pre)) :
    actualParent5 d N pre ≤ oldCap c (primeHistoryLogCoordinates N 6 pre) := by
  apply actualParent5_le_oldCap_of_original_seed d N he c pre hlen hc
  simpa only [originalSeed, rosserAncestor_nested 4 5 (by decide)] using
    P2InheritedFourthRaw31Embedding.selected_third_seed_le_oldCap (d.e : ℝ) d.chi d.m
      d.omega N c pre hlen hc (by exact_mod_cast he) hs

/-- The original inherited seed really participates in the actual common
parent. Thus its unsupported Theta floor cannot be ignored in an upper
guard merely because H5 is below that parent. -/
theorem original_seed_le_actualParent5 (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    originalSeed d N (rosserAncestor 4 pre) ≤ actualParent5 d N pre := by
  have h0 : originalSeed d N (rosserAncestor 4 pre) ≤ lambda3 d N (rosserAncestor 4 pre) :=
    le_max_left _ _
  have h1 := lambda3_le_exponent4 d N (rosserAncestor 4 pre)
  have h2 := inherited4_le_exponent5 d N (rosserAncestor 5 pre)
  rw [rosserAncestor_nested 4 5 (by decide)] at h2
  exact h0.trans (h1.trans h2)

/-- Exact missing-condition classification. It does not assert that an
unsupported arithmetic source point exists, nor that the manuscript is
false. It identifies the precise extra floor condition such a point needs. -/
theorem actual_upper_guard_iff_supported_or_initial
    (d : OriginalData) (N : ℝ) (he : 0 ≤ d.e) (c : Cell) (pre : List ℕ)
    (hlen : pre.length = 6) (hc : PhysicalCell c (primeHistoryLogCoordinates N 6 pre)) :
    actualParent5 d N pre ≤ oldCap c (primeHistoryLogCoordinates N 6 pre) ↔
      P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
        (rosserAncestor 3 pre) ∨
      HistoricalThirdCoarse.initial (d.e : ℝ) ≤ oldCap c (primeHistoryLogCoordinates N 6 pre) := by
  by_cases hs : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
      (rosserAncestor 3 pre)
  · exact ⟨fun _ => Or.inl hs,
      fun _ => actualParent5_le_oldCap_on_supported_source d N he c pre hlen hc hs⟩
  · have hseed : originalSeed d N (rosserAncestor 4 pre) =
        HistoricalThirdCoarse.initial (d.e : ℝ) := by
      simp only [originalSeed, seedExponent, rosserAncestor_nested 3 4 (by decide),
        P1CoarseFirstCubeFallbackMargin.effectiveExponent, if_neg hs]
    constructor
    · intro hupper
      exact Or.inr (by rw [← hseed]; exact (original_seed_le_actualParent5 d N pre).trans hupper)
    · intro h
      apply actualParent5_le_oldCap_of_original_seed d N he c pre hlen hc
      rw [hseed]
      exact h.resolve_left hs

theorem unsupported_initial_above_old_rejects_sixth
    (d : OriginalData) (N : ℝ) (c : Cell) (pre : List ℕ)
    (hs : ¬P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
      (rosserAncestor 3 pre))
    (hfloor : oldCap c (primeHistoryLogCoordinates N 6 pre) <
      HistoricalThirdCoarse.initial (d.e : ℝ)) : ¬eligibleSixth d N c pre := by
  have hseed : originalSeed d N (rosserAncestor 4 pre) =
      HistoricalThirdCoarse.initial (d.e : ℝ) := by
    simp only [originalSeed, seedExponent, rosserAncestor_nested 3 4 (by decide),
      P1CoarseFirstCubeFallbackMargin.effectiveExponent, if_neg hs]
  intro hc
  have h := (original_seed_le_actualParent5 d N pre).trans hc.2.2.2
  rw [hseed] at h
  exact (not_le_of_gt hfloor) h

/-- Both lower and upper tests of the unchanged actual sixth eligibility
are now derived on the actual common FINAL source. PhysicalCell and the
original third support are primitive source conditions, not an H5 or
actualParent<=oldCap conclusion supplied by a caller. -/
theorem final_supported_source_eligibleSixth
    (d : OriginalData) (N cap : ℕ) (hN : 1 < (N : ℝ)) (he : 0 ≤ d.e)
    (w z : ℝ) (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (policy8 d (N : ℝ)) weight [] true 1
      (roughPrimeUniverse N cap w z)) (hlen : 6 ≤ leaf.selected.length)
    (c : Cell)
    (hc : PhysicalCell c
      (primeHistoryLogCoordinates (N : ℝ) 6 (rosserAncestor 6 leaf.selected)))
    (hs : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega (N : ℝ)
      (rosserAncestor 3 leaf.selected)) :
    eligibleSixth d (N : ℝ) c (rosserAncestor 6 leaf.selected) := by
  have h6 : (rosserAncestor 6 leaf.selected).length = 6 := by
    rw [rosserAncestor_length, Nat.min_eq_left hlen]
  have hs6 : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega (N : ℝ)
      (rosserAncestor 3 (rosserAncestor 6 leaf.selected)) := by
    rwa [rosserAncestor_nested 3 6 (by decide)]
  have hlower := P1ActualOriginalAndCommonFifthGuard.common_final_actual_retained_H5_lower_guard
    d N cap hN w z weight leaf hleaf hlen
  have hupper := actualParent5_le_oldCap_on_supported_source d (N : ℝ) he c
    (rosserAncestor 6 leaf.selected) h6 hc hs6
  exact ⟨h6, hc, hlower, hupper⟩

/-- Exhaustive actual-source retest, including unsupported third histories.
The lower test is proved from the real final leaf. The remaining upper
test is precisely the original support-or-literal-initial-floor condition;
there is no blanket licence obtained by dropping this alternative. -/
theorem final_source_sixth_eligibility_iff_original_floor
    (d : OriginalData) (N cap : ℕ) (hN : 1 < (N : ℝ)) (he : 0 ≤ d.e)
    (w z : ℝ) (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves (policy8 d (N : ℝ)) weight [] true 1
      (roughPrimeUniverse N cap w z)) (hlen : 6 ≤ leaf.selected.length)
    (c : Cell)
    (hc : PhysicalCell c
      (primeHistoryLogCoordinates (N : ℝ) 6 (rosserAncestor 6 leaf.selected))) :
    eligibleSixth d (N : ℝ) c (rosserAncestor 6 leaf.selected) ↔
      P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega (N : ℝ)
        (rosserAncestor 3 leaf.selected) ∨
      HistoricalThirdCoarse.initial (d.e : ℝ) ≤
        oldCap c (primeHistoryLogCoordinates (N : ℝ) 6 (rosserAncestor 6 leaf.selected)) := by
  have h6 : (rosserAncestor 6 leaf.selected).length = 6 := by
    rw [rosserAncestor_length, Nat.min_eq_left hlen]
  have hlower := P1ActualOriginalAndCommonFifthGuard.common_final_actual_retained_H5_lower_guard
    d N cap hN w z weight leaf hleaf hlen
  have hiff := actual_upper_guard_iff_supported_or_initial d (N : ℝ) he c
    (rosserAncestor 6 leaf.selected) h6 hc
  rw [rosserAncestor_nested 3 6 (by decide)] at hiff
  exact ⟨fun h => hiff.mp h.2.2.2, fun h => ⟨h6, hc, hlower, hiff.mpr h⟩⟩

end
end ImbalancedChen.P1CommonFifthElevenActualUpperGuard
