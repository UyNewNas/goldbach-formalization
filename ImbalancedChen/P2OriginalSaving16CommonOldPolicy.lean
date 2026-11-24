import ImbalancedChen.P2OriginalSaving16HistoricalMesh
import ImbalancedChen.P4AOriginalRemainingAscendingCommonParent
import ImbalancedChen.P5OriginalFifthArchiveFallbackSeparation
import ImbalancedChen.P2OriginalFourteenUniformResidual

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual common constructor is not redefined. This module proves that
its original historical third lookup realizes all fourteen retained
sources at one fixed schedule. The old fourth/fifth rows, licence and
eligibility remain literal. Every sixth action keeps PhysicalCell and
H5<current<=oldCap; the actual14 source is disjoint from those eleven
PhysicalCells, so its sixth cap inherits its true fifth parent.

This supplies the supported-third and current<=R ports on the complete
retained14 source. It does not prove full22/full87 ownership, preservation
under changes of the numerical archive schedule, or the integral reserve.
-/
namespace ImbalancedChen.P2OriginalSaving16CommonOldPolicy
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope
open P2OriginalAscendingEighthCapDictionary
open P2OriginalSaving16FourteenPhysicalAtlas
open P2OriginalSaving16TrimmedHistory
open P2OriginalSaving16HistoricalMesh
open P5OriginalCommonRefinedConstructor
open P5OriginalCommonRefinedPreservation
open P5OriginalCommonRefinedSeedHull
open P5OriginalFifthArchiveFallbackSeparation

abbrev firstSix (t : Point) : Fin 6 → ℝ := fun i => t ⟨i.val, by omega⟩

/-- All fourteen actual branch assignments are dispatched to their own
existing source proof. This is not a CellGuard-only exclusion claim. -/
theorem source_no_sixth_PhysicalCell (c : Cell) (t : Point) (ht : sourceRows c t)
    (s : SixthCell) :
    ¬Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell s (firstSix t) := by
  cases c with
  | inl i =>
      fin_cases i
      · exact P4AOriginalCell0ActualSixthParentGuard.cell0_no_sixth_PhysicalCell t
          (by simpa [sourceRows, rows] using ht) s
      · exact P4AOriginalAscendingCell1ActualChronology.cell1_no_sixth_PhysicalCell t
          (by simpa [sourceRows, rows] using ht) s
      · exact P4AOriginalAscendingCell2ActualChronology.cell2_no_sixth_PhysicalCell t
          (by simpa [sourceRows, rows] using ht) s
  | inr i =>
      exact P4AOriginalRemainingAscendingCommonParent.source_no_sixth_PhysicalCell i t ht s

/-- Neither the upper current<=oldCap test nor the H5 test is deleted.
Actual source geometry makes their PhysicalCell conjunct false here. -/
theorem actual_sixth_eq_actual_fifth (data : OriginalData) (N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 8) (c : Cell)
    (ht : sourceRows c (primeHistoryLogCoordinates N 8 pre)) :
    lambda6 data N (rosserAncestor 6 pre) =
      actualParent5 data N (rosserAncestor 6 pre) := by
  apply lambda6_eq_parent_of_no_eligible
  intro s _ hs
  have hcoords : primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre) =
      firstSix (primeHistoryLogCoordinates N 8 pre) := by
    funext i
    exact primeHistoryLogCoordinates_ancestor N hlen (by decide : 6 ≤ 8) i
  have hp := hs.2.1
  rw [hcoords] at hp
  exact source_no_sixth_PhysicalCell c _ ht s hp

theorem source_ancestor_tent_le_R (N : ℝ) (pre : List ℕ) (hlen : pre.length = 8)
    (c : Cell) (ht : sourceRows c (primeHistoryLogCoordinates N 8 pre))
    (k : ℕ) (hk : k ≤ 6) (I : Finset (Fin k)) :
    v (∑ i ∈ I, primeHistoryLogCoordinates N k (rosserAncestor k pre) i) ≤
      R (primeHistoryLogCoordinates N 8 pre) := by
  let t := primeHistoryLogCoordinates N 8 pre
  have hc := sourceRows_cellGuard c t ht
  let emb : Fin k ↪ Fin 6 :=
    ⟨fun i => i.castLE hk, by intro i j hij; exact Fin.ext (congrArg Fin.val hij)⟩
  let J := I.map emb
  have heq : (∑ i ∈ I, primeHistoryLogCoordinates N k (rosserAncestor k pre) i) =
      subsetSum t J := by
    simp only [J, subsetSum, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    exact primeHistoryLogCoordinates_ancestor N hlen (by omega : k ≤ 8) i
  rw [heq]
  by_cases hj : J = ∅
  · have hb : v (t 0) ≤ R t := by
      simpa [subsetSum] using old_tents_below_R _ t hc.old_planes {0}
        (by simp [oldMasks])
    have h0 := hc.coordinate_pos 0
    rw [v_eq_A hc.largest.le] at hb
    simp only [hj, subsetSum, Finset.sum_empty]
    rw [v_eq_A (by norm_num [mu] : (0 : ℝ) ≤ mu)]
    dsimp [A] at hb ⊢
    linarith
  · exact old_tents_below_R _ t hc.old_planes J (by simp [oldMasks, hj])

/-- The above-mu corrections cannot alter this source's actual third
ancestor. The effective exponent still retains all old support/fallback
branches; support is proved later for the chosen common schedule. -/
theorem actual_third_eq_original (data : OriginalData) (N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 8) (c : Cell)
    (ht : sourceRows c (primeHistoryLogCoordinates N 8 pre)) :
    lambda3 data N (rosserAncestor 4 pre) =
      P1CoarseFirstCubeFallbackMargin.effectiveExponent (data.e : ℝ) data.chi data.m
        data.omega N (rosserAncestor 3 pre) := by
  have hx := (sourceRows_cellGuard c _ ht).largest.le
  have h2 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 2 ≤ 8) (0 : Fin 2)
  have h3 := primeHistoryLogCoordinates_ancestor N hlen (by decide : 3 ≤ 8) (0 : Fin 3)
  have hn2 : ¬P5OriginalAboveMuThirdLowerPhysicalCoefficient.secondGuard N (rosserAncestor 4 pre) := by
    intro h
    have hh := h.1
    rw [rosserAncestor_nested 2 4 (by decide)] at hh
    exact (not_lt_of_ge hx) (h2 ▸ hh)
  have hn3 : ¬P5OriginalAboveMuThirdLowerPhysicalCoefficient.thirdGuard N (rosserAncestor 4 pre) := by
    intro h
    have hh := h.1
    rw [rosserAncestor_nested 3 4 (by decide)] at hh
    exact (not_lt_of_ge hx) (h3 ▸ hh)
  simp only [lambda3, fallbackSeed, if_neg hn3, if_neg hn2, max_self,
    originalSeed, P1OriginalVariableFourthContinuation.seedExponent,
    rosserAncestor_nested 3 4 (by decide)]

/-- Exact old/common fourth and fifth values, at the SAME schedule and
the SAME actual fifth ancestor. No comparison of signed coefficients is
used to infer preservation of the original two-own-cube gain. -/
theorem old_fifth_actions_and_gain_preserved (data : OriginalData) (N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 8) (c : Cell)
    (ht : sourceRows c (primeHistoryLogCoordinates N 8 pre)) :
    commonInherited data N (rosserAncestor 5 pre) = oldInherited data N (rosserAncestor 5 pre) ∧
    exponent5 data N (rosserAncestor 5 pre) = oldFifth data N (rosserAncestor 5 pre) ∧
    P5OriginalCommonRefinedFifthGainDefect.commonGain data N (rosserAncestor 5 pre) =
      P5OriginalCommonRefinedFifthGainDefect.oldGain data N (rosserAncestor 5 pre) := by
  have h5 : (rosserAncestor 5 pre).length = 5 := by simp [hlen]
  have hx := primeHistoryLogCoordinates_ancestor N hlen (by decide : 5 ≤ 8) (0 : Fin 5)
  have hbelow : primeHistoryLogCoordinates N 5 (rosserAncestor 5 pre) 0 ≤ mu := by
    rw [hx]
    exact (sourceRows_cellGuard c _ ht).largest.le
  have h4 := inherited_eq_old_below_mu data N _ h5 hbelow
  have hnew := fifth_eq_old_below_mu data N _ h5 hbelow
  refine ⟨h4, hnew, ?_⟩
  simp only [P5OriginalCommonRefinedFifthGainDefect.commonGain,
    P5OriginalCommonRefinedFifthGainDefect.oldGain, h4, hnew]

private theorem actual_fifth_le_R_from_third (data : OriginalData) (N : ℝ)
    (he : 0 ≤ data.e) (pre : List ℕ) (hlen : pre.length = 8) (c : Cell)
    (ht : sourceRows c (primeHistoryLogCoordinates N 8 pre))
    (hthird : lambda3 data N (rosserAncestor 4 pre) ≤ R (primeHistoryLogCoordinates N 8 pre)) :
    actualParent5 data N (rosserAncestor 6 pre) ≤ R (primeHistoryLogCoordinates N 8 pre) := by
  have heR : (0 : ℝ) ≤ data.e := by exact_mod_cast he
  have h4len : (rosserAncestor 4 pre).length = 4 := by simp [hlen]
  have h5len : (rosserAncestor 5 pre).length = 5 := by simp [hlen]
  have h4 : exponent4 data N (rosserAncestor 4 pre) ≤ R (primeHistoryLogCoordinates N 8 pre) := by
    rw [exponent4, if_pos h4len]
    apply P1OriginalVariableFourthContinuation.finiteMax_le
    · exact hthird
    · intro r _ _
      rw [r.bufferedCandidate_eq]
      have h := source_ancestor_tent_le_R N pre hlen c ht 4 (by decide) r.selected
      linarith
  change exponent5 data N (rosserAncestor 5 (rosserAncestor 6 pre)) ≤ _
  rw [rosserAncestor_nested 5 6 (by decide), exponent5, if_pos h5len,
    rosserAncestor_nested 4 5 (by decide)]
  apply P1OriginalVariableFourthContinuation.finiteMax_le
  · exact h4
  · intro r _ _
    rw [P1OriginalVariableFifthContinuation.candidate,
      P1OriginalVariableFifthContinuation.envelope_eq_v]
    have h := source_ancestor_tent_le_R N pre hlen c ht 5 (by decide) r.selected
    linarith

/-- Source-specific realized old policy. The conclusion has the true
firstStop, actual third support, all four histories, actual sixth cap,
and unchanged old fifth gain. Neither current<=R nor support is assumed.
The finite fourth/fifth source data stay universally quantified so the
actual original banks may be used without changing this schedule proof. -/
theorem exists_common_actual_parent_on_trim (delta : ℝ) (hdelta : 0 < delta) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∀ chi : ℝ, 0 < chi → chi ≤ (e : ℝ) / 10 →
      ∃ m0 : ℕ, ∀ data : OriginalData, data.e = e → data.chi = chi → m0 ≤ data.m →
      data.omega ≤ 1 / 100 → ∀ N : ℝ, 1 < N →
      ∀ pre : List ℕ, pre.length = 8 → (∀ p ∈ pre, 0 < p) →
      primeHistoryLogCoordinates N 8 pre ∈ trimmedRegion delta →
        HistoricalThirdCoarse.firstStop (data.e : ℝ) data.m N (rosserAncestor 1 pre) ∧
        P1ThirdFallbackSupport.supported (data.e : ℝ) data.chi data.m data.omega N (rosserAncestor 3 pre) ∧
        3 * primeHistoryLogCoordinates N 8 pre 0 < lambda3 data N (rosserAncestor 4 pre) ∧
        oddCube (primeHistoryLogCoordinates N 8 pre) 2 < lambda3 data N (rosserAncestor 4 pre) ∧
        oddCube (primeHistoryLogCoordinates N 8 pre) 4 < lambda3 data N (rosserAncestor 4 pre) ∧
        oddCube (primeHistoryLogCoordinates N 8 pre) 6 < lambda3 data N (rosserAncestor 4 pre) ∧
        lambda3 data N (rosserAncestor 4 pre) ≤ lambda6 data N (rosserAncestor 6 pre) ∧
        CurrentParentGuard (primeHistoryLogCoordinates N 8 pre) (lambda6 data N (rosserAncestor 6 pre)) ∧
        P5OriginalCommonRefinedFifthGainDefect.commonGain data N (rosserAncestor 5 pre) =
          P5OriginalCommonRefinedFifthGainDefect.oldGain data N (rosserAncestor 5 pre) := by
  obtain ⟨e0, he0, hmesh⟩ := exists_actual_historical_mesh delta hdelta
  refine ⟨e0, he0, ?_⟩
  intro e he hee chi hchi hchie
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  obtain ⟨m0, hm0⟩ := hmesh (e : ℝ) heR hee chi hchi hchie
  refine ⟨m0, ?_⟩
  intro data hde hdc hdm homega N hN pre hlen hpos ht
  let t := primeHistoryLogCoordinates N 8 pre
  obtain ⟨c, hct⟩ := mem_iUnion.mp (trimmedRegion_subset_region delta hdelta ht)
  have hc := sourceRows_cellGuard c t hct
  obtain ⟨j, hj, hjt, h1, h3, h5, h7, hlo, hhi⟩ := hm0 data.m hdm t ht
  have hj' : j ∈ HistoricalThirdCoarse.cells (data.e : ℝ) data.chi data.m := by
    simpa only [hde, hdc] using hj
  have hsupport : P1ThirdFallbackSupport.supported (data.e : ℝ) data.chi data.m
      data.omega N (rosserAncestor 3 pre) := by
    refine ⟨actual_third_active data.omega N hN homega pre hlen hpos hc, j, hj', ?_⟩
    rw [firstThree_ancestor N pre hlen]
    exact hjt
  have hcap : lambda3 data N (rosserAncestor 4 pre) =
      HistoricalThirdCoarse.exponent (e : ℝ) chi data.m (firstThree t) := by
    rw [actual_third_eq_original data N pre hlen c hct,
      P1CoarseFirstCubeFallbackMargin.effectiveExponent, if_pos hsupport,
      firstThree_ancestor N pre hlen, hde, hdc]
  have hparent : lambda3 data N (rosserAncestor 4 pre) ≤ lambda6 data N (rosserAncestor 6 pre) := by
    have hh := lambda3_le_exponent5 data N (rosserAncestor 5 pre)
    rw [lambda3_ancestor data N 5 (by decide),
      ← lambda3_ancestor data N 4 (by decide) pre] at hh
    have hp := actualParent5_le_lambda6 data N (rosserAncestor 6 pre)
    change exponent5 data N (rosserAncestor 5 (rosserAncestor 6 pre)) ≤ _ at hp
    rw [rosserAncestor_nested 5 6 (by decide)] at hp
    exact hh.trans hp
  have hupper : lambda6 data N (rosserAncestor 6 pre) ≤ R t := by
    rw [actual_sixth_eq_actual_fifth data N pre hlen c hct]
    exact actual_fifth_le_R_from_third data N (by simpa only [hde] using he.le)
      pre hlen c hct (by rw [hcap]; exact hhi)
  have hstop := actual_firstStop_of_joint_cell (data.e : ℝ) data.chi N data.m
    pre hlen j hj' hjt
  have h7cap : oddCube t 6 < lambda3 data N (rosserAncestor 4 pre) := by
    rwa [hcap]
  refine ⟨hstop, hsupport, ?_, ?_, ?_, ?_, hparent, ?_,
    (old_fifth_actions_and_gain_preserved data N pre hlen c hct).2.2⟩
  · rwa [hcap]
  · rwa [hcap]
  · rwa [hcap]
  · rwa [hcap]
  · exact ⟨h7cap.trans_le hparent, hupper⟩

/-- J's uniform arithmetic comparison now consumes the actual old common
constructor on every retained cell WITHOUT its former current<=R port.
No prime-integral limit or historical Q96 bound is asserted by this local
pointwise residual result. -/
theorem exists_uniform_realized_frontier_gain
    (delta : ℝ) (hdelta : 0 < delta) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
      ∀ chi : ℝ, 0 < chi → chi ≤ (e : ℝ) / 10 →
      ∃ m0 N0 : ℕ, 2 ≤ N0 ∧
      ∀ data : OriginalData, data.e = e → data.chi = chi → m0 ≤ data.m →
      data.omega ≤ 1 / 100 → ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (cap : ℕ) (z : ℝ) (state : FirstExitDepthState ℕ),
      state ∈ firstExitDepthFrontier 8 (policy6 data (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) →
      let pre := state.selectedPrefix
      let t := primeHistoryLogCoordinates (N : ℝ) 8 pre
      t ∈ trimmedRegion delta →
        sourceGain (R t) (M t) t - epsilon <
          (actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
              (currentLevel (N : ℝ) (lambda6 data (N : ℝ)) pre / (pre.prod : ℝ)) -
            actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
              (familyNextLevel (N : ℝ) (lambda6 data (N : ℝ))
                P4AOriginalAscending14Literal42.literalPattern pre / (pre.prod : ℝ))) *
            Real.log (N : ℝ) / singularSeries N := by
  obtain ⟨e0, he0, hparent⟩ := exists_common_actual_parent_on_trim delta hdelta
  obtain ⟨N0, hN0, hgain⟩ :=
    P2OriginalFourteenUniformResidual.exists_uniform_actual_fourteen_frontier_gain epsilon hepsilon
  refine ⟨e0, he0, ?_⟩
  intro e he hee chi hchi hchie
  obtain ⟨m0, hm0⟩ := hparent e he hee chi hchi hchie
  refine ⟨m0, N0, hN0, ?_⟩
  intro data hde hdc hdm homega N hN hEven cap z state hs
  dsimp only
  intro ht
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlen := firstExitDepthFrontier_selected_length 8 _ _ []
    (roughPrimeUniverse N cap 0 z) true 1 (by simp) state hs
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 8
    (policy6 data (N : ℝ)) (fun p : ℕ => 1 / ((p : ℝ) - 1))
    (roughPrimeUniverse N cap 0 z) state hs
  have hpos : ∀ p ∈ state.selectedPrefix, 0 < p := by
    intro p hp
    exact (mem_roughPrimeUniverse_prime (hsub.subset (List.mem_reverse.mpr hp))).pos
  obtain ⟨hstop, hsupp, h1, h3, h5, h7, h36, hguard, holdGain⟩ :=
    hm0 data hde hdc hdm homega (N : ℝ) hNr state.selectedPrefix hlen hpos ht
  have hs' : state ∈ firstExitDepthFrontier 8
      (P4AOriginalEighthParentPhysicalLedger.parentPolicy (N : ℝ)
        (lambda6 data (N : ℝ)) (policy5 data (N : ℝ)))
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) := by
    simpa only [P4AOriginalEighthParentPhysicalLedger.parentPolicy,
      P4AActualSixthFrozenEighthAdmission.sixthPolicy, policy6, level6] using hs
  exact hgain N hN hEven (lambda6 data (N : ℝ)) (policy5 data (N : ℝ))
    P4AOriginalAscending14Literal42.literalPattern cap z state hs'
    (region_selectedFamilyGuard (trimmedRegion_subset_region delta hdelta ht)) hguard.2

end
end ImbalancedChen.P2OriginalSaving16CommonOldPolicy
