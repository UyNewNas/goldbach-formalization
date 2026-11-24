import ImbalancedChen.P4AOriginalCompleteSixthChronology

/-! SOURCE ONLY / UNCOMPILED. The R03 complete87 literal source dictionary
now controls every endpoint in the concrete complete-sixth constructor.
The terminal theorem has no lambda6/current/fifth/R6-bound hypothesis.
Its one real schedule requirement is actual supported third membership.
Supplying that membership uniformly is the original compact common-mesh
construction, not a claim about an arbitrary untrimmed finite partition. -/
namespace ImbalancedChen.P4AOriginalFull87CompleteSixthBound
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P1OriginalVariableFourthContinuation
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P4AOriginalCompleteSixthChronology

def firstSix (t : P4AOriginalFull87SourceDictionary.Point) : Certificates.P2OriginalSixthElevenLogSemantics.Physical := fun i => t i.castSucc.castSucc
def slots (m : ℕ) : Finset (Fin 6) := Finset.univ.filter fun i => Certificates.P2OriginalSixthElevenLogSemantics.bit m i.val

/-- Closed 64-subset encoding only; UNEVALUATED and no real tuple sampled. -/
theorem slots_complete : ∀ I : Finset (Fin 6),
    ∃ m ∈ Finset.Icc 0 63, slots m = I := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem source_subset_conventions (c : P4AOriginalFull87SourceDictionary.Cell) (m : ℕ)
    (hm : m ∈ Finset.Icc 1 63) (t : P4AOriginalFull87SourceDictionary.Point) :
    Certificates.P2OriginalSixthElevenLogSemantics.selectedSum m (firstSix t) = P4AOriginalFull87SourceDictionary.oldSubsetSum c m t := by
  have hml := (Finset.mem_Icc.mp hm).1
  have hmu := (Finset.mem_Icc.mp hm).2
  cases c with
  | remaining c => rfl
  | descending i =>
      interval_cases m <;>
        norm_num [Certificates.P2OriginalSixthElevenLogSemantics.selectedSum, Certificates.P2OriginalSixthElevenLogSemantics.bit, firstSix, P4AOriginalFull87SourceDictionary.oldSubsetSum,
          OriginalDescendingFifteenCellOwnership.subsetSum,
          OriginalDescendingFifteenCellOwnership.maskSlots,
          Finset.sum_filter, Fin.sum_univ_succ]
  | ascendingPair i =>
      interval_cases m <;>
        norm_num [Certificates.P2OriginalSixthElevenLogSemantics.selectedSum, Certificates.P2OriginalSixthElevenLogSemantics.bit, firstSix, P4AOriginalFull87SourceDictionary.oldSubsetSum,
          OriginalAscendingThirteenCellOwnership.subsetSum,
          OriginalAscendingThirteenCellOwnership.maskSlots,
          Finset.sum_filter, Fin.sum_univ_succ]
  | h3 i =>
      interval_cases m <;>
        norm_num [Certificates.P2OriginalSixthElevenLogSemantics.selectedSum, Certificates.P2OriginalSixthElevenLogSemantics.bit, firstSix, P4AOriginalFull87SourceDictionary.oldSubsetSum,
          P4AOriginalFirstFailureH3Literal.oldSubsetSum, Fin.sum_univ_succ]

theorem source_sixth_tents (c : P4AOriginalFull87SourceDictionary.Cell) (t : P4AOriginalFull87SourceDictionary.Point) (h : P4AOriginalFull87SourceDictionary.Source c t)
    (m : ℕ) (hm : m ∈ Finset.Icc 1 63) :
    v (Certificates.P2OriginalSixthElevenLogSemantics.selectedSum m (firstSix t)) ≤ P4AOriginalFull87SourceDictionary.comparison c t := by
  rw [source_subset_conventions c m hm t]
  exact P4AOriginalFull87SourceDictionary.source_all_old_tents h m hm

theorem source_empty_tent (c : P4AOriginalFull87SourceDictionary.Cell) (t : P4AOriginalFull87SourceDictionary.Point) (h : P4AOriginalFull87SourceDictionary.Source c t) :
    v 0 ≤ P4AOriginalFull87SourceDictionary.comparison c t := by
  have ho := P4AOriginalFull87SourceDictionary.source_ordered h
  have hp : 0 ≤ t 0 := ho.1.trans (ho.2.1.trans ho.2.2.1)
  have hb := source_sixth_tents c t h 1 (by decide)
  have hb' : v (t 0) ≤ P4AOriginalFull87SourceDictionary.comparison c t := by
    simpa [Certificates.P2OriginalSixthElevenLogSemantics.selectedSum, Certificates.P2OriginalSixthElevenLogSemantics.bit, firstSix, Fin.sum_univ_succ] using hb
  rw [v_eq_A ho.2.2.2] at hb'
  rw [v_eq_A (by norm_num [mu] : (0 : ℝ) ≤ mu)]
  dsimp [A] at hb' ⊢
  linarith

theorem source_all_subsets (c : P4AOriginalFull87SourceDictionary.Cell) (t : P4AOriginalFull87SourceDictionary.Point) (h : P4AOriginalFull87SourceDictionary.Source c t)
    (I : Finset (Fin 6)) : v (∑ i ∈ I, firstSix t i) ≤ P4AOriginalFull87SourceDictionary.comparison c t := by
  obtain ⟨m, hm, rfl⟩ := slots_complete I
  have heq : (∑ i ∈ slots m, firstSix t i) = Certificates.P2OriginalSixthElevenLogSemantics.selectedSum m (firstSix t) := by
    simp only [slots, Finset.sum_filter, Certificates.P2OriginalSixthElevenLogSemantics.selectedSum]
  rw [heq]
  by_cases hz : m = 0
  · subst m
    simpa [Certificates.P2OriginalSixthElevenLogSemantics.selectedSum, Certificates.P2OriginalSixthElevenLogSemantics.bit] using source_empty_tent c t h
  · apply source_sixth_tents c t h m
    have hu := (Finset.mem_Icc.mp hm).2
    simp only [Finset.mem_Icc]
    omega

theorem source_ancestor_tent_le_comparison (N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 8) (c : P4AOriginalFull87SourceDictionary.Cell)
    (h : P4AOriginalFull87SourceDictionary.Source c (primeHistoryLogCoordinates N 8 pre))
    (k : ℕ) (hk : k ≤ 6) (I : Finset (Fin k)) :
    v (∑ i ∈ I, primeHistoryLogCoordinates N k (rosserAncestor k pre) i) ≤
      P4AOriginalFull87SourceDictionary.comparison c (primeHistoryLogCoordinates N 8 pre) := by
  let emb : Fin k ↪ Fin 6 :=
    ⟨fun i => i.castLE hk, by intro i j hij; exact Fin.ext (congrArg Fin.val hij)⟩
  have heq : (∑ i ∈ I, primeHistoryLogCoordinates N k (rosserAncestor k pre) i) =
      ∑ j ∈ I.map emb, firstSix (primeHistoryLogCoordinates N 8 pre) j := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    exact primeHistoryLogCoordinates_ancestor N hlen (by omega : k ≤ 8) i
  rw [heq]
  exact source_all_subsets c _ h _

theorem source_original_endpoint_le_comparison (c : P4AOriginalFull87SourceDictionary.Cell) (t : P4AOriginalFull87SourceDictionary.Point)
    (h : P4AOriginalFull87SourceDictionary.Source c t) : original (t 0) (t 1) (t 2) ≤ P4AOriginalFull87SourceDictionary.comparison c t := by
  obtain ⟨he1,he3,he7,he5,he6⟩ := P4AOriginalFull87SourceDictionary.oldSubsetSum_third_masks c t
  have h1 := P4AOriginalFull87SourceDictionary.source_all_old_tents h 1 (by decide)
  have h3 := P4AOriginalFull87SourceDictionary.source_all_old_tents h 3 (by decide)
  have h7 := P4AOriginalFull87SourceDictionary.source_all_old_tents h 7 (by decide)
  have h5 := P4AOriginalFull87SourceDictionary.source_all_old_tents h 5 (by decide)
  have h6 := P4AOriginalFull87SourceDictionary.source_all_old_tents h 6 (by decide)
  rw [he1] at h1
  rw [he3] at h3
  rw [he7] at h7
  rw [he5] at h5
  rw [he6] at h6
  rw [original_eq_six (P4AOriginalFull87SourceDictionary.source_ordered h)]
  exact max_le h1 (max_le h3 (max_le h7 (max_le (P4AOriginalFull87SourceDictionary.source_old_w h).le (max_le h5 h6))))

/-- Both above-mu fallbacks are absent on the original87 source. -/
theorem actual_third_eq_original (d : OriginalData) (N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 8) (c : P4AOriginalFull87SourceDictionary.Cell)
    (h : P4AOriginalFull87SourceDictionary.Source c (primeHistoryLogCoordinates N 8 pre)) :
    lambda3 d N (rosserAncestor 4 pre) =
      P1CoarseFirstCubeFallbackMargin.effectiveExponent (d.e : ℝ) d.chi d.m
        d.omega N (rosserAncestor 3 pre) := by
  have hx := (P4AOriginalFull87SourceDictionary.source_basic h).1.le
  have h2 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 2 ≤ 8) (0 : Fin 2)
  have h3 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 8) (0 : Fin 3)
  have hn2 : ¬P5OriginalAboveMuThirdLowerPhysicalCoefficient.secondGuard N (rosserAncestor 4 pre) := by
    intro hh
    have hh' := hh.1
    rw [rosserAncestor_nested 2 4 (by decide)] at hh'
    exact (not_lt_of_ge hx) (h2 ▸ hh')
  have hn3 : ¬P5OriginalAboveMuThirdLowerPhysicalCoefficient.thirdGuard N (rosserAncestor 4 pre) := by
    intro hh
    have hh' := hh.1
    rw [rosserAncestor_nested 3 4 (by decide)] at hh'
    exact (not_lt_of_ge hx) (h3 ▸ hh')
  simp only [lambda3, fallbackSeed, if_neg hn3, if_neg hn2, max_self,
    originalSeed, P1OriginalVariableFourthContinuation.seedExponent,
    rosserAncestor_nested 3 4 (by decide)]

theorem supported_third_le_comparison (d : OriginalData) (N : ℝ)
    (he : 0 ≤ d.e) (pre : List ℕ) (hlen : pre.length = 8) (c : P4AOriginalFull87SourceDictionary.Cell)
    (h : P4AOriginalFull87SourceDictionary.Source c (primeHistoryLogCoordinates N 8 pre))
    (hs : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
      (rosserAncestor 3 pre)) :
    lambda3 d N (rosserAncestor 4 pre) ≤ P4AOriginalFull87SourceDictionary.comparison c (primeHistoryLogCoordinates N 8 pre) := by
  have heR : (0 : ℝ) ≤ d.e := by exact_mod_cast he
  rw [actual_third_eq_original d N pre hlen c h,
    P1CoarseFirstCubeFallbackMargin.effectiveExponent, if_pos hs]
  obtain ⟨j, hj, ht⟩ := hs.2
  rw [HistoricalThirdCoarse.exponent_on_cell _ _ _ _ j hj ht]
  let t := primeHistoryLogCoordinates N 8 pre
  have h0 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 8) (0 : Fin 3)
  have h1 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 8) (1 : Fin 3)
  have h2 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 8) (2 : Fin 3)
  have hb := HistoricalThirdCoarse.inBox_of_cell ht
  rw [h0,h1,h2] at hb
  have ho := P4AOriginalFull87SourceDictionary.source_ordered h
  have hg := HistoricalThirdCoarse.gamma_le_endpoint (d.e : ℝ)
    (HistoricalThirdCoarse.box d.m j) heR hb ho.1 ho.2.1 ho.2.2.1
  rw [HistoricalThirdCoarse.endpoint, if_pos ho.2.2.2] at hg
  have hh := source_original_endpoint_le_comparison c t h
  dsimp only [HistoricalThirdCoarse.levelExponent]
  linarith

theorem supported_fifth_le_comparison (d : OriginalData) (N : ℝ)
    (he : 0 ≤ d.e) (pre : List ℕ) (hlen : pre.length = 8) (c : P4AOriginalFull87SourceDictionary.Cell)
    (h : P4AOriginalFull87SourceDictionary.Source c (primeHistoryLogCoordinates N 8 pre))
    (hs : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
      (rosserAncestor 3 pre)) :
    actualParent5 d N (rosserAncestor 6 pre) ≤ P4AOriginalFull87SourceDictionary.comparison c (primeHistoryLogCoordinates N 8 pre) := by
  have heR : (0 : ℝ) ≤ d.e := by exact_mod_cast he
  have h4len : (rosserAncestor 4 pre).length = 4 := by simp [hlen]
  have h5len : (rosserAncestor 5 pre).length = 5 := by simp [hlen]
  have h4 : exponent4 d N (rosserAncestor 4 pre) ≤ P4AOriginalFull87SourceDictionary.comparison c (primeHistoryLogCoordinates N 8 pre) := by
    rw [exponent4, if_pos h4len]
    apply finiteMax_le
    · exact supported_third_le_comparison d N he pre hlen c h hs
    · intro r _ _
      rw [r.bufferedCandidate_eq]
      have hh := source_ancestor_tent_le_comparison N pre hlen c h 4 (by decide) r.selected
      linarith
  change exponent5 d N (rosserAncestor 5 (rosserAncestor 6 pre)) ≤ _
  rw [rosserAncestor_nested 5 6 (by decide), exponent5, if_pos h5len,
    rosserAncestor_nested 4 5 (by decide)]
  apply finiteMax_le _ _ _ _ _ h4
  intro r _ _
  rw [P1OriginalVariableFifthContinuation.candidate,
    P1OriginalVariableFifthContinuation.envelope_eq_v]
  have hh := source_ancestor_tent_le_comparison N pre hlen c h 5 (by decide) r.selected
  linarith

/-- Concrete complete current-parent upper bound on every original87
source, with the original supported coarse ancestor. No physical witness,
caller lambda6, complete-sixth upper bound or signed-density conclusion is
assumed. All mesh parameters remain in their original pre-N order. -/
theorem source_current_le_comparison (e : ℚ) (q : ℕ) (omega N : ℝ)
    (he : 0 ≤ e) (pre : List ℕ) (hlen : pre.length = 8) (c : P4AOriginalFull87SourceDictionary.Cell)
    (h : P4AOriginalFull87SourceDictionary.Source c (primeHistoryLogCoordinates N 8 pre))
    (hs : P1ThirdFallbackSupport.supported ((data e q omega).e : ℝ)
      (data e q omega).chi (data e q omega).m (data e q omega).omega N
      (rosserAncestor 3 pre)) :
    currentSixthExponent e q omega N (rosserAncestor 6 pre) ≤
      P4AOriginalFull87SourceDictionary.comparison c (primeHistoryLogCoordinates N 8 pre) := by
  apply current_le_of_subset_tents
  · exact supported_fifth_le_comparison (data e q omega) N he pre hlen c h hs
  · intro m hm
    have hcoords : primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre) =
        firstSix (primeHistoryLogCoordinates N 8 pre) := by
      funext i
      exact primeHistoryLogCoordinates_ancestor N hlen (by decide : 6 ≤ 8) i
    rw [hcoords]
    exact source_sixth_tents c _ h m hm

end
end ImbalancedChen.P4AOriginalFull87CompleteSixthBound
