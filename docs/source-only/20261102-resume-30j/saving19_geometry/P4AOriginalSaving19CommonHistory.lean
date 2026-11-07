import ImbalancedChen.P2OriginalSaving19HistoricalMinorant
import ImbalancedChen.P4AOriginalLive171819PrimeBank
import ImbalancedChen.P5OriginalCommonRefinedPreservation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Use the independently defined common historical third/fourth/fifth/sixth
constructor. The new lower bound is for its actual lambda3, while G's
whole-source chosen-plane proof supplies the upper lambda6<=A14 bound.
Thus H7<lambda3 is now derived on a uniformly trimmed compact source,
instead of inferred incorrectly from H7<lambda6 or supplied as a guard.
The original selected prime-bank consumer derives its own third support.
No equality B3=lambda3 or R=lambda6 is used. No T10/11026 source occurs.
-/

namespace ImbalancedChen.P4AOriginalSaving19CommonHistory

noncomputable section
open scoped Classical
open Set VariableEnvelope HistoricalThirdCoarse
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P2OriginalSaving19HistoricalMinorant
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P4AOriginalLive171819CommonParent P4AOriginalLive171819PrimeBank

/-- The original lookup, not a newly rounded or child-indexed replacement,
supplies the old third cap. Its selected box is fixed by first-three data. -/
theorem supported_originalSeed_histories
    (d : OriginalData) (N : ℝ) (pre : List ℕ) (hlen : pre.length = 8)
    {δ : ℝ} (hδ : 0 < δ) (hm : δ ≤ historyMargin (point8 N pre))
    (he : 0 ≤ (d.e : ℝ)) (heδ : (d.e : ℝ) ≤ δ / 16)
    (hegate : (d.e : ℝ) ≤ 3 / 256) (hχ : d.chi ≤ δ / 16)
    (hsup : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
      (rosserAncestor 3 pre)) :
    3 * point8 N pre 0 < originalSeed d N (rosserAncestor 4 pre) ∧
      history3 (point8 N pre) < originalSeed d N (rosserAncestor 4 pre) ∧
      history5 (point8 N pre) < originalSeed d N (rosserAncestor 4 pre) ∧
      history7 (point8 N pre) < originalSeed d N (rosserAncestor 4 pre) := by
  obtain ⟨j, hj, hjt⟩ := hsup.2
  have hc (k : Fin 3) := primeHistoryLogCoordinates_ancestor N hlen (by omega : 3 ≤ 8) k
  have hbox : (box d.m j).InBox (point8 N pre 0) (point8 N pre 1) (point8 N pre 2) := by
    simpa only [hc] using inBox_of_cell hjt
  have hwidth : ((box d.m j).width : ℝ) ≤ d.chi :=
    ((mem_cells (d.e : ℝ) d.chi d.m j).mp hj).2.2.2.2.2
  have hg := original_coarse_histories (box d.m j) hδ hm he heδ hegate hχ hbox hwidth
  have hseed : originalSeed d N (rosserAncestor 4 pre) = levelExponent (d.e : ℝ) (box d.m j) := by
    unfold originalSeed P1OriginalVariableFourthContinuation.seedExponent
    rw [rosserAncestor_nested 3 4 (by omega)]
    rw [P1CoarseFirstCubeFallbackMargin.effectiveExponent, if_pos hsup,
      exponent_on_cell (d.e : ℝ) d.chi d.m _ j hj hjt]
  simpa only [hseed] using hg

/-- Causal refinement keeps the original lower bound when the corrected
fallback seed is added. Both actual seeds and their maximum remain intact. -/
theorem supported_common_third_histories
    (d : OriginalData) (N : ℝ) (pre : List ℕ) (hlen : pre.length = 8)
    {δ : ℝ} (hδ : 0 < δ) (hm : δ ≤ historyMargin (point8 N pre))
    (he : 0 ≤ (d.e : ℝ)) (heδ : (d.e : ℝ) ≤ δ / 16)
    (hegate : (d.e : ℝ) ≤ 3 / 256) (hχ : d.chi ≤ δ / 16)
    (hsup : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
      (rosserAncestor 3 pre)) :
    3 * point8 N pre 0 < lambda3 d N (rosserAncestor 4 pre) ∧
      history3 (point8 N pre) < lambda3 d N (rosserAncestor 4 pre) ∧
      history5 (point8 N pre) < lambda3 d N (rosserAncestor 4 pre) ∧
      history7 (point8 N pre) < lambda3 d N (rosserAncestor 4 pre) := by
  have hh := supported_originalSeed_histories d N pre hlen hδ hm he heδ hegate hχ hsup
  have hle : originalSeed d N (rosserAncestor 4 pre) ≤ lambda3 d N (rosserAncestor 4 pre) :=
    le_max_left _ _
  exact ⟨hh.1.trans_le hle, hh.2.1.trans_le hle,
    hh.2.2.1.trans_le hle, hh.2.2.2.trans_le hle⟩

/-- The existing fourth/fifth/sixth finite maxima retain the same third
ancestor. This structural transfer is independent of all geometry. -/
theorem common_third_le_current_sixth (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    lambda3 d N (rosserAncestor 4 pre) ≤ lambda6 d N (rosserAncestor 6 pre) := by
  have h5 := lambda3_le_exponent5 d N (rosserAncestor 5 pre)
  rw [lambda3_ancestor d N 5 (by omega)] at h5
  have hp : lambda3 d N pre ≤ actualParent5 d N (rosserAncestor 6 pre) := by
    simpa only [actualParent5, rosserAncestor_nested 5 6 (by omega)] using h5
  rw [lambda3_ancestor d N 4 (by omega)]
  exact hp.trans (actualParent5_le_lambda6 d N (rosserAncestor 6 pre))

/-- Actual arithmetic bank membership produces source and old support;
only the source-margin/mesh precision are added. In particular, neither
H7<lambda3 nor a third-support predicate is a premise of this consumer. -/
theorem selected_common_third_histories
    (i : Fin 13) (d : OriginalData) (N cap : ℕ) (hN : 1 < N)
    (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selected (.ascending19 i) d.e d.chi d.m d.omega N cap w z (policy8 d (N : ℝ)))
    {δ : ℝ} (hδ : 0 < δ) (hm : δ ≤ historyMargin (point8 (N : ℝ) s.selectedPrefix))
    (he : 0 ≤ (d.e : ℝ)) (heδ : (d.e : ℝ) ≤ δ / 16)
    (hegate : (d.e : ℝ) ≤ 3 / 256) (hχ : d.chi ≤ δ / 16) :
    3 * point8 (N : ℝ) s.selectedPrefix 0 < lambda3 d (N : ℝ) (rosserAncestor 4 s.selectedPrefix) ∧
      history3 (point8 (N : ℝ) s.selectedPrefix) < lambda3 d (N : ℝ) (rosserAncestor 4 s.selectedPrefix) ∧
      history5 (point8 (N : ℝ) s.selectedPrefix) < lambda3 d (N : ℝ) (rosserAncestor 4 s.selectedPrefix) ∧
      history7 (point8 (N : ℝ) s.selectedPrefix) < lambda3 d (N : ℝ) (rosserAncestor 4 s.selectedPrefix) := by
  have hmem : s ∈ firstExitDepthFrontier 8 (policy8 d (N : ℝ))
      (fun p => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap w z) ∧
      ∃ j ∈ bank (.ascending19 i) d.e d.chi d.m d.omega,
        primeHistoryTuple 8 s.selectedPrefix ∈ P4AOriginalCell0HalfOpenPrimeCarrier.primeBox d.m N j := by
    simpa only [selected, List.mem_filter, decide_eq_true_eq] using hs
  obtain ⟨hf, j, hj, hp⟩ := hmem
  have hlen := firstExitDepthFrontier_selected_length 8 _ _ []
    (roughPrimeUniverse N cap w z) true 1 (by simp) s hf
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 8 _ _ _ s hf
  have hpos : ∀ p ∈ s.selectedPrefix, 0 < p := by
    intro p hp
    exact (mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp))).pos
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨_hrows, _hstop, hsup⟩ := bank_rows_stop_support (.ascending19 i)
    d.e d.chi d.m d.omega (N : ℝ) hNr s.selectedPrefix hlen hpos j hj
      (P4AOriginalCell0HalfOpenPrimeCarrier.primeBox_log hN j _ hp)
  exact supported_common_third_histories d (N : ℝ) s.selectedPrefix hlen hδ hm he heδ hegate hχ hsup

/-- All thirteen banks share one precision on their common compact source.
Quantifiers fix epsilon before the original data, all targets and states.
This closes the missing third-history condition, without claiming the
unproved global bank-exhaustion or old-gain preservation statements. -/
theorem compact_selected_common_third_histories (K : Set Point) (hK : IsCompact K)
    (hsource : ∀ t ∈ K, ∃ i : Fin 13, OriginalAscendingThirteenCellOwnership.StrictRows i t) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (d : OriginalData), 0 ≤ (d.e : ℝ) → (d.e : ℝ) ≤ ε → d.chi ≤ ε →
      ∀ (i : Fin 13) (N cap : ℕ), 1 < N → ∀ (w z : ℝ) (s : FirstExitDepthState ℕ),
        s ∈ selected (.ascending19 i) d.e d.chi d.m d.omega N cap w z (policy8 d (N : ℝ)) →
        point8 (N : ℝ) s.selectedPrefix ∈ K →
        3 * point8 (N : ℝ) s.selectedPrefix 0 < lambda3 d (N : ℝ) (rosserAncestor 4 s.selectedPrefix) ∧
          history3 (point8 (N : ℝ) s.selectedPrefix) < lambda3 d (N : ℝ) (rosserAncestor 4 s.selectedPrefix) ∧
          history5 (point8 (N : ℝ) s.selectedPrefix) < lambda3 d (N : ℝ) (rosserAncestor 4 s.selectedPrefix) ∧
          history7 (point8 (N : ℝ) s.selectedPrefix) < lambda3 d (N : ℝ) (rosserAncestor 4 s.selectedPrefix) := by
  obtain ⟨δ, hδ, hm⟩ := hK.exists_forall_le' continuous_historyMargin.continuousOn
    (by intro t ht; obtain ⟨i, hi⟩ := hsource t ht; exact historyMargin_pos hi)
  refine ⟨min (δ / 16) (3 / 256), lt_min (by positivity) (by norm_num), ?_⟩
  intro d he heε hχε i N cap hN w z s hs hKmem
  exact selected_common_third_histories i d N cap hN w z s hs hδ (hm _ hKmem) he
    (heε.trans (min_le_left _ _)) (heε.trans (min_le_right _ _))
    (hχε.trans (min_le_left _ _))

/-- The new actual third history is consumed by the original residual and
gain dictionary. All desired parent/history bounds come from source or
constructor proofs. The history result is stronger than the old retained
frontier H7<lambda6 result, and is useful to the held physical-mask guard. -/
theorem selected_saving19_actual_parent_dictionary
    (i : Fin 13) (d : OriginalData) (he : 0 ≤ d.e)
    (N cap : ℕ) (hN : 1 < N) (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ selected (.ascending19 i) d.e d.chi d.m d.omega N cap w z (policy8 d (N : ℝ)))
    {δ : ℝ} (hδ : 0 < δ) (hm : δ ≤ historyMargin (point8 (N : ℝ) s.selectedPrefix))
    (heδ : (d.e : ℝ) ≤ δ / 16) (hegate : (d.e : ℝ) ≤ 3 / 256) (hχ : d.chi ≤ δ / 16) :
    history7 (point8 (N : ℝ) s.selectedPrefix) < lambda3 d (N : ℝ) (rosserAncestor 4 s.selectedPrefix) ∧
      lambda3 d (N : ℝ) (rosserAncestor 4 s.selectedPrefix) ≤
        lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) ∧
      lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) ≤
        comparisonCap (point8 (N : ℝ) s.selectedPrefix) ∧
      conservativeDensity (point8 (N : ℝ) s.selectedPrefix) ≤
        parentDensity (lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix))
          (point8 (N : ℝ) s.selectedPrefix) := by
  have heR : 0 ≤ (d.e : ℝ) := by exact_mod_cast he
  have hh := (selected_common_third_histories i d N cap hN w z s hs hδ hm heR heδ hegate hχ).2.2.2
  have h36 := common_third_le_current_sixth d (N : ℝ) s.selectedPrefix
  obtain ⟨hr, _hstop, _h6, hup⟩ := shared_frontier_live_guard (.ascending19 i) d he N cap hN w z s hs
  have hrows := OriginalAscendingThirteenCellOwnership.rows_physical
    (P4AOriginalLive171819Atlas.source19_guard i _ hr)
  have hcap : lambda6 d (N : ℝ) (rosserAncestor 6 s.selectedPrefix) ≤
      comparisonCap (point8 (N : ℝ) s.selectedPrefix) := hup
  exact ⟨hh, h36, hcap, conservativeDensity_le_parentDensity hrows (hh.trans_le h36) hcap⟩

end
end ImbalancedChen.P4AOriginalSaving19CommonHistory
