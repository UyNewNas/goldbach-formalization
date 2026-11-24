import ImbalancedChen.P4AOriginalFull87ActualCommonHistory
import ImbalancedChen.P4AOriginalSixthWinningAction

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

On the original87 shared-history slice, a saved SIXTH geometric source is
actually admitted by its original guard. The actual fifth upper comparison
is proved from its unchanged row maxima and the saved row's 31 old planes.
The H3/H5 tests come from the actual shared third history. No archived row
is declared geometrically valid merely because its index is in the file.

The conclusion is a source/actual-guard equivalence on this slice, NOT
acceptance of every entire saved rectangle in other sixth source domains,
a saved numerical-gain identity or a changed policy.
-/
namespace ImbalancedChen.P4AOriginalSavedSixthActualAdmission
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P1OriginalVariableFourthContinuation
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P4AOriginalCompleteSixthChronology P4AOriginalFull87SourceDictionary
open P4AOriginalFull87ActualCommonHistory

abbrev SavedRow := P4AOriginalSavedSixthArchive.Row
abbrev SixPoint := Certificates.P2OriginalSixthElevenLogSemantics.Physical

def slots5 (m : ℕ) : Finset (Fin 5) :=
  Finset.univ.filter fun j => Certificates.P2OriginalSixthElevenLogSemantics.bit m j.val

/-- Small finite bit dictionary only; this does not evaluate archive bytes. -/
theorem slots5_complete : ∀ I : Finset (Fin 5),
    ∃ m ∈ Finset.Icc 0 31, slots5 m = I := by decide

theorem saved_W_le (i : SavedRow) (t : SixPoint) :
    Certificates.P2OriginalSixthElevenLogSemantics.W t ≤
      P4AOriginalSavedSixthArchive.oldUpper i t :=
  finiteMax_seed_le _ _ _ _

theorem saved_tent_le (i : SavedRow) (m : ℕ) (hm : m ∈ Finset.Icc 1 31)
    (t : SixPoint) :
    v (Certificates.P2OriginalSixthElevenLogSemantics.subsetSum m t) ≤
      P4AOriginalSavedSixthArchive.oldUpper i t :=
  (P4AOriginalSavedSixthArchive.old_tent_le_oldPlane i m t).trans
    (finiteMax_row_le _ _ _ _ m hm trivial)

/-- Every old subproduct of the first FIVE coordinates is paid by the
saved row's real oldUpper. The empty subset is paid by its original W. -/
theorem saved_all_subsets_le (i : SavedRow) (t : SixPoint) (ht : t 2 ≤ mu)
    (I : Finset (Fin 5)) :
    v (∑ j ∈ I, t j.castSucc) ≤ P4AOriginalSavedSixthArchive.oldUpper i t := by
  obtain ⟨m,hm,rfl⟩ := slots5_complete I
  have hid : (∑ j ∈ slots5 m, t j.castSucc) =
      Certificates.P2OriginalSixthElevenLogSemantics.subsetSum m t := by
    simp only [slots5, Finset.sum_filter,
      Certificates.P2OriginalSixthElevenLogSemantics.subsetSum]
  rw [hid]
  by_cases hz : m = 0
  · subst m
    have hW := saved_W_le i t
    have hzero : v 0 ≤ Certificates.P2OriginalSixthElevenLogSemantics.W t := by
      norm_num [v_eq_min,A,C] at ⊢
      dsimp [Certificates.P2OriginalSixthElevenLogSemantics.W,mu] at *
      linarith
    simpa [Certificates.P2OriginalSixthElevenLogSemantics.subsetSum,
      Certificates.P2OriginalSixthElevenLogSemantics.bit] using hzero.trans hW
  · apply saved_tent_le i m _ t
    have hlo := (Finset.mem_Icc.mp hm).1
    have hhi := (Finset.mem_Icc.mp hm).2
    simp only [Finset.mem_Icc]
    omega

theorem six_le_saved (i : SavedRow) (t : SixPoint) (ht : t 2 ≤ mu) :
    six (t 0) (t 1) (t 2) ≤ P4AOriginalSavedSixthArchive.oldUpper i t := by
  have h1 := saved_all_subsets_le i t ht {0}
  have h3 := saved_all_subsets_le i t ht {0,1}
  have h7 := saved_all_subsets_le i t ht {0,1,2}
  have h5 := saved_all_subsets_le i t ht {0,2}
  have h6 := saved_all_subsets_le i t ht {1,2}
  norm_num at h1 h3 h7 h5 h6
  have hW : B (t 2) ≤ P4AOriginalSavedSixthArchive.oldUpper i t := by
    have hid : B (t 2) = Certificates.P2OriginalSixthElevenLogSemantics.W t := by
      dsimp [B,cap,Certificates.P2OriginalSixthElevenLogSemantics.W]
      ring
    rw [hid]
    exact saved_W_le i t
  simpa only [six,add_assoc] using
    max_le h1 (max_le h3 (max_le h7 (max_le hW (max_le h5 h6))))

/-- Subset bounds read the relevant actual ancestor, not a free tuple
whose relation to the old parent has been left as a hypothesis. -/
theorem ancestor_tent_le_saved (i : SavedRow) (N : ℝ) (pre : List ℕ)
    (hlen : pre.length = 8) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates N 8 pre))
    (k : ℕ) (hk : k ≤ 5) (I : Finset (Fin k)) :
    v (∑ j ∈ I, primeHistoryLogCoordinates N k (rosserAncestor k pre) j) ≤
      P4AOriginalSavedSixthArchive.oldUpper i
        (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)) := by
  let emb : Fin k ↪ Fin 5 :=
    ⟨fun j => j.castLE hk, by intro a b h; exact Fin.ext (congrArg Fin.val h)⟩
  have hid : (∑ j ∈ I, primeHistoryLogCoordinates N k (rosserAncestor k pre) j) =
      ∑ j ∈ I.map emb,
        primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre) j.castSucc := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro j _
    rw [primeHistoryLogCoordinates_ancestor N hlen (by omega : k ≤ 8),
      primeHistoryLogCoordinates_ancestor N hlen (by decide : 6 ≤ 8)]
    rfl
  rw [hid]
  exact saved_all_subsets_le i _
    (P4AOriginalSixthWinningAction.source_third_bound N pre hlen c hs) _

/-- The actual finite Gamma seed is no larger than its original six
continuous branches; every branch is bounded by this saved oldUpper. -/
theorem supported_third_le_saved (i : SavedRow) (d : OriginalData) (N : ℝ)
    (he : 0 ≤ d.e) (pre : List ℕ) (hlen : pre.length = 8) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates N 8 pre))
    (hsupport : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
      (rosserAncestor 3 pre)) :
    lambda3 d N (rosserAncestor 4 pre) ≤
      P4AOriginalSavedSixthArchive.oldUpper i
        (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)) := by
  have heR : (0 : ℝ) ≤ d.e := by exact_mod_cast he
  rw [P4AOriginalFull87CompleteSixthBound.actual_third_eq_original d N pre hlen c hs,
    P1CoarseFirstCubeFallbackMargin.effectiveExponent, if_pos hsupport]
  obtain ⟨j,hj,ht⟩ := hsupport.2
  rw [HistoricalThirdCoarse.exponent_on_cell _ _ _ _ j hj ht]
  have hbox := HistoricalThirdCoarse.inBox_of_cell ht
  have h0 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 8) (0 : Fin 3)
  have h1 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 8) (1 : Fin 3)
  have h2 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 8) (2 : Fin 3)
  rw [h0,h1,h2] at hbox
  have ho := source_ordered hs
  have hg := HistoricalThirdCoarse.gamma_le_endpoint (d.e : ℝ)
    (HistoricalThirdCoarse.box d.m j) heR hbox ho.1 ho.2.1 ho.2.2.1
  rw [HistoricalThirdCoarse.endpoint, if_pos ho.2.2.2, original_eq_six ho] at hg
  have h6 := six_le_saved i (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre))
    (P4AOriginalSixthWinningAction.source_third_bound N pre hlen c hs)
  rw [primeHistoryLogCoordinates_ancestor N hlen (by decide : 6 ≤ 8) (0 : Fin 6),
    primeHistoryLogCoordinates_ancestor N hlen (by decide : 6 ≤ 8) (1 : Fin 6),
    primeHistoryLogCoordinates_ancestor N hlen (by decide : 6 ≤ 8) (2 : Fin 6)] at h6
  dsimp only [HistoricalThirdCoarse.levelExponent]
  linarith

theorem actual_fifth_le_saved (i : SavedRow) (d : OriginalData) (N : ℝ)
    (he : 0 ≤ d.e) (pre : List ℕ) (hlen : pre.length = 8) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates N 8 pre))
    (hsupport : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
      (rosserAncestor 3 pre)) :
    actualParent5 d N (rosserAncestor 6 pre) ≤
      P4AOriginalSavedSixthArchive.oldUpper i
        (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)) := by
  have heR : (0 : ℝ) ≤ d.e := by exact_mod_cast he
  have h4len : (rosserAncestor 4 pre).length = 4 := by simp [hlen]
  have h5len : (rosserAncestor 5 pre).length = 5 := by simp [hlen]
  have h4 : exponent4 d N (rosserAncestor 4 pre) ≤
      P4AOriginalSavedSixthArchive.oldUpper i
        (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)) := by
    rw [exponent4,if_pos h4len]
    apply finiteMax_le
    · exact supported_third_le_saved i d N he pre hlen c hs hsupport
    · intro r _ _
      rw [r.bufferedCandidate_eq]
      have h := ancestor_tent_le_saved i N pre hlen c hs 4 (by decide) r.selected
      linarith
  change exponent5 d N (rosserAncestor 5 (rosserAncestor 6 pre)) ≤ _
  rw [rosserAncestor_nested 5 6 (by decide),exponent5,if_pos h5len,
    rosserAncestor_nested 4 5 (by decide)]
  apply finiteMax_le _ _ _ _ _ h4
  intro r _ _
  rw [P1OriginalVariableFifthContinuation.candidate,
    P1OriginalVariableFifthContinuation.envelope_eq_v]
  have h := ancestor_tent_le_saved i N pre hlen c hs 5 (by decide) r.selected
  linarith

/-- Exact converse on the original87 shared-history slice. A row's original
Source is the only remaining pointwise saved geometric premise. No actual
fifth bound or H3/H5 guard is passed to this conversion. -/
theorem savedEligible_iff_source (i : SavedRow) (e : ℚ) (q : ℕ) (om N : ℝ)
    (he : 0 ≤ e) (pre : List ℕ) (hlen : pre.length = 8) (c : Cell)
    (hs : Source c (primeHistoryLogCoordinates N 8 pre))
    (hr : RealizedHistory e q om N pre c) :
    savedEligible e q om N i (rosserAncestor 6 pre) ↔
      P4AOriginalSavedSixthArchive.Source i
        (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)) := by
  constructor
  · exact fun h => h.2.1
  · intro hsrc
    have hc (j : Fin 6) := primeHistoryLogCoordinates_ancestor N hlen
      (by decide : 6 ≤ 8) j
    have hhist3 := hr.2.2.1 (1 : Fin 4)
    have hhist5 := hr.2.2.1 (2 : Fin 4)
    rw [lambda3_ancestor _ _ 4 (by decide)] at hhist3 hhist5
    have hl3 : Certificates.P2OriginalSixthElevenLogSemantics.H3
        (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)) <
        lambda3 (data e q om) N (rosserAncestor 6 pre) := by
      rw [lambda3_ancestor _ _ 6 (by decide)]
      simpa [P4AOriginalFull87HistoryCore.oldHistory,
        P4AOriginalRemainingEighthSources.history,
        Certificates.P2OriginalSixthElevenLogSemantics.H3,hc] using hhist3
    have hl5 : Certificates.P2OriginalSixthElevenLogSemantics.H5
        (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)) <
        lambda3 (data e q om) N (rosserAncestor 6 pre) := by
      rw [lambda3_ancestor _ _ 6 (by decide)]
      simpa [P4AOriginalFull87HistoryCore.oldHistory,
        P4AOriginalRemainingEighthSources.history,
        Certificates.P2OriginalSixthElevenLogSemantics.H5,hc] using hhist5
    exact ⟨by simp [hlen],hsrc,hl3,hl5,
      actual_fifth_le_saved i (data e q om) N he pre hlen c hs hr.2.1⟩

end
end ImbalancedChen.P4AOriginalSavedSixthActualAdmission
