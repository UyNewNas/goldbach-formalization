import ImbalancedChen.P4AOriginalRemainingAscendingAtlas
import ImbalancedChen.P5OriginalCommonRefinedAncestry
import ImbalancedChen.P4AActualEighthInheritedHistoryGuard

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Bounds for the independently frozen common constructor on the eleven
actual remaining source IDs. The source-specific old planes and strict
singleton row are derived from their literal atlas; actual new fourth,
fifth and sixth values are never identified with old values or with R.
-/
namespace ImbalancedChen.P4AOriginalRemainingAscendingCommonParent
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope HistoricalThirdCoarse
open P4AOriginalRemainingAscendingAtlas P2OriginalAscendingEighthCapDictionary
open P4AOriginalAscending14Literal42
open P1OriginalVariableFourthContinuation P1OriginalVariableFifthContinuation
abbrev point8 (N : ℝ) (pre : List ℕ) := primeHistoryLogCoordinates N 8 pre
abbrev first6 (t : Fin 8 → ℝ) : Fin 6 → ℝ := fun i => t ⟨i.val, by omega⟩
variable (c : RemainingCell)

/-- Literal row34 is strict: the old singleton-A cap is strictly below R. -/
theorem source_singleton_strict (t : Fin 8 → ℝ) (ht : sourceRows c t) :
    A (t 0) < R t := by
  have h := ht (34 : Fin 96)
  have heq : rows c 34 = baseRows 34 := by fin_cases c <;> decide
  rw [heq] at h
  norm_num [baseRows, P4AOriginalAscendingCell0Literal96.rows,
    evalRow, P4AOriginalSeed7Unequal15Literal.evalAffine,
    Fin.sum_univ_succ] at h
  dsimp [A, R, d, C]
  linarith

/-- Every one of the eleven source cells licenses the old third mask6 at
A(t0). The actual atlas cell instead has this mask equal to R>A(t0), so none applies. -/
theorem source_no_sixth_PhysicalCell (t : Fin 8 → ℝ) (ht : sourceRows c t)
    (sc : Certificates.P2OriginalSixthElevenLogSemantics.Cell) :
    ¬ Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell sc (first6 t) := by
  intro hp
  have h6 := Certificates.P2OriginalSixthElevenLogSemantics.branchLicense_sound
    (hp.first3Branches 6 (by decide))
  have hd := (sourceRows_cellGuard c t ht).old_descending
  have heq : Certificates.P2OriginalSixthElevenLogSemantics.tent
      (Certificates.P2OriginalSixthElevenLogSemantics.subsetSum 6 (first6 t)) = R t := by
    have hdesc : 57 / 64 - 3 * (t 1 + t 2) / 2 ≤ (1 + (t 1 + t 2)) / 2 := by
      dsimp [A, C, d] at hd
      linarith
    norm_num [Certificates.P2OriginalSixthElevenLogSemantics.subsetSum,
      Certificates.P2OriginalSixthElevenLogSemantics.bit, first6,
      Fin.sum_univ_succ, Certificates.P2OriginalSixthElevenLogSemantics.tent]
    rw [min_eq_right hdesc]
    dsimp [R, d, C]
    ring
  rw [heq] at h6
  have hstrict := source_singleton_strict c t ht
  change R t ≤ (1 + t 0) / 2 at h6
  dsimp [A] at hstrict
  linarith


variable (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)

private theorem empty_tent_le_R (t : Fin 8 → ℝ) (ht : sourceRows c t) : v 0 ≤ R t := by
  have hc := sourceRows_cellGuard c t ht
  have hpos : 0 < t 0 := hc.last_pos.trans (hc.order (by decide : (0 : Fin 8) < 7))
  have h0 := source_singleton_strict c t ht
  rw [v_eq_min]
  dsimp [A, C] at *
  norm_num
  linarith

/-- Every subset cap through rank six is bounded on this very source cell,
including an empty selected mask. No row-wise cap bound is a premise. -/
theorem ancestor_subset_tent_le_R (pre : List ℕ) (hlen : pre.length = 8)
    (ht : sourceRows c (point8 N pre)) (k : ℕ) (hk : k ≤ 6)
    (I : Finset (Fin k)) :
    v (∑ i ∈ I, primeHistoryLogCoordinates N k (rosserAncestor k pre) i) ≤
      R (point8 N pre) := by
  let emb : Fin k ↪ Fin 6 := ⟨fun i => i.castLE hk, by intro i j h; exact Fin.ext (congrArg Fin.val h)⟩
  let J : Finset (Fin 6) := I.map emb
  have hsum : (∑ i ∈ I, primeHistoryLogCoordinates N k (rosserAncestor k pre) i) =
      P2OriginalAscendingEighthCapDictionary.subsetSum (point8 N pre) J := by
    simp only [J, P2OriginalAscendingEighthCapDictionary.subsetSum, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    exact primeHistoryLogCoordinates_ancestor N hlen (by omega : k ≤ 8) i
  rw [hsum]
  by_cases hj : J = ∅
  · simpa [hj, P2OriginalAscendingEighthCapDictionary.subsetSum] using empty_tent_le_R c _ ht
  · exact old_tents_below_R (literalPattern (sourceId c)) _
      (sourceRows_cellGuard c _ ht).old_planes J (by simp [oldMasks, hj])

/-- On the actual supported third ancestor Gamma is a lower enclosure of
the original third envelope R. The unsupported Theta fallback is excluded
by a genuine support witness, never silently substituted. -/
theorem supported_third_seed_le_R (he : 0 ≤ e) (pre : List ℕ) (hlen : pre.length = 8)
    (ht : sourceRows c (point8 N pre))
    (hs : P1ThirdFallbackSupport.supported (e : ℝ) chi m omega N (rosserAncestor 3 pre)) :
    P1CoarseFirstCubeFallbackMargin.effectiveExponent (e : ℝ) chi m omega N
      (rosserAncestor 3 pre) ≤ R (point8 N pre) := by
  obtain ⟨j, hj, hjt⟩ := hs.2
  have hc := sourceRows_cellGuard c _ ht
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hcoords (i : Fin 3) := primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 8) i
  have hb := inBox_of_cell hjt
  have horder : Ordered
      (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 0)
      (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 1)
      (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 2) := by
    simp only [hcoords]
    exact ⟨(hc.last_pos.trans (hc.order (by decide : (2 : Fin 8) < 7))).le,
      (hc.order (by decide : (1 : Fin 8) < 2)).le,
      (hc.order (by decide : (0 : Fin 8) < 1)).le, hc.largest.le⟩
  have hg := gamma_le_endpoint (e : ℝ) (box m j) heR hb
    horder.1 horder.2.1 horder.2.2.1
  have hend : endpoint
      (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 0)
      (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 1)
      (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 2) = R (point8 N pre) := by
    simp only [hcoords, endpoint, if_pos hc.largest.le]
    exact hc.originalThird_eq
  rw [hend] at hg
  rw [P1CoarseFirstCubeFallbackMargin.effectiveExponent, if_pos hs,
    exponent_on_cell (e : ℝ) chi m _ j hj hjt]
  dsimp [levelExponent]
  linarith

/-- On any of these eleven original atlas histories every corrected fallbackSeed branch is a
real subset tent already bounded by the source's old plane system. -/
theorem common_lambda3_le_R (d : P5OriginalCommonRefinedConstructor.OriginalData)
    (N : ℝ) (he : 0 ≤ d.e) (pre : List ℕ) (hlen : pre.length = 8)
    (ht : sourceRows c (point8 N pre))
    (hs : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
      (rosserAncestor 3 pre)) :
    P5OriginalCommonRefinedConstructor.lambda3 d N (rosserAncestor 4 pre) ≤ R (point8 N pre) := by
  have hold : P5OriginalCommonRefinedConstructor.originalSeed d N (rosserAncestor 4 pre) ≤
      R (point8 N pre) := by
    simpa only [P5OriginalCommonRefinedConstructor.originalSeed, seedExponent,
      rosserAncestor_nested 3 4 (by decide)] using
      supported_third_seed_le_R c d.e d.chi d.m d.omega N he pre hlen ht hs
  unfold P5OriginalCommonRefinedConstructor.lambda3
  apply max_le hold
  unfold P5OriginalCommonRefinedConstructor.fallbackSeed
  split_ifs
  · have h := ancestor_subset_tent_le_R c N pre hlen ht 3 (by decide) ({1,2} : Finset (Fin 3))
    simpa [rosserAncestor_nested 3 4 (by decide)] using h
  · have h := ancestor_subset_tent_le_R c N pre hlen ht 2 (by decide) ({1} : Finset (Fin 2))
    simpa [rosserAncestor_nested 2 4 (by decide)] using h
  · exact hold

/-- These are the shared constructor's NEW actual fourth/fifth values.
They are not rewritten to the old predecessor values. -/
theorem common_actual_fifth_le_R (d : P5OriginalCommonRefinedConstructor.OriginalData)
    (N : ℝ) (he : 0 ≤ d.e) (pre : List ℕ) (hlen : pre.length = 8)
    (ht : sourceRows c (point8 N pre))
    (hs : P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N
      (rosserAncestor 3 pre)) :
    P5OriginalCommonRefinedConstructor.actualParent5 d N (rosserAncestor 6 pre) ≤ R (point8 N pre) := by
  have heR : (0 : ℝ) ≤ d.e := by exact_mod_cast he
  have hseed := common_lambda3_le_R c d N he pre hlen ht hs
  have h4len : (rosserAncestor 4 pre).length = 4 := by simp [hlen]
  have h5len : (rosserAncestor 5 pre).length = 5 := by simp [hlen]
  have h4 : P5OriginalCommonRefinedConstructor.exponent4 d N (rosserAncestor 4 pre) ≤
      R (point8 N pre) := by
    rw [P5OriginalCommonRefinedConstructor.exponent4, if_pos h4len]
    apply finiteMax_le
    · exact hseed
    · intro r _ _
      rw [r.bufferedCandidate_eq]
      have hr := ancestor_subset_tent_le_R c N pre hlen ht 4 (by decide) r.selected
      linarith
  change P5OriginalCommonRefinedConstructor.exponent5 d N
    (rosserAncestor 5 (rosserAncestor 6 pre)) ≤ _
  rw [rosserAncestor_nested 5 6 (by decide),
    P5OriginalCommonRefinedConstructor.exponent5, if_pos h5len,
    rosserAncestor_nested 4 5 (by decide)]
  apply finiteMax_le
  · exact h4
  · intro r _ _
    have hr := ancestor_subset_tent_le_R c N pre hlen ht 5 (by decide) r.selected
    rw [candidate, envelope_eq_v]
    linarith

/-- The eleven source regions remain incompatible with each actual remaining source even when
their eligibility is re-tested against the NEW actual fifth parent. -/
theorem common_lambda6_eq_new_actual_parent
    (d : P5OriginalCommonRefinedConstructor.OriginalData) (N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 8) (ht : sourceRows c (point8 N pre)) :
    P5OriginalCommonRefinedConstructor.lambda6 d N (rosserAncestor 6 pre) =
      P5OriginalCommonRefinedConstructor.actualParent5 d N (rosserAncestor 6 pre) := by
  apply P5OriginalCommonRefinedConstructor.lambda6_eq_parent_of_no_eligible
  intro sc _ hc
  have hphys := hc.2.1
  have hid : primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre) = first6 (point8 N pre) := by
    funext i
    exact primeHistoryLogCoordinates_ancestor N hlen (by decide : 6 ≤ 8) i
  rw [hid] at hphys
  exact source_no_sixth_PhysicalCell c _ ht sc hphys


end
end ImbalancedChen.P4AOriginalRemainingAscendingCommonParent
