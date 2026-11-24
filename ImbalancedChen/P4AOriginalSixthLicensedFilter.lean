import ImbalancedChen.P4AOriginalSixthWinningAction
import ImbalancedChen.P4AOriginalFull87FiniteParentPolicy

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

The original raw-current guard is retained. A new sixth action is used
only when its OWN rounded endpoint passes all lower square gates and the
selected-tent debit. The inherited finite fifth cap is never removed.
This changes the sixth cap outside the earlier common margin stratum;
it is not a rewrite of the old policy and gives no signed-gain inequality.
-/
namespace ImbalancedChen.P4AOriginalSixthLicensedFilter
noncomputable section
open scoped Classical BigOperators
open P1OriginalVariableFourthContinuation P1GuardFrozenFiniteCapAlgebra
open P5OriginalCommonRefinedConstructor P4AOriginalCompleteSixthChronology
open P4AOriginalFull87FiniteParentCaps P4AOriginalSixthActionBank
open P4AOriginalSixthCommonMargin P1QuantizedActionLicense
open P4AOriginalFull87HistoryCore (width)

/-- The additional check does not recompute ActualEligible with a rounded
or filtered current. It can only remove an original eligible action. -/
def Accepted (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (a : Action) : Prop :=
  let t := primeHistoryLogCoordinates N 6 pre
  ActualEligible e q om N pre a ∧
    LowerLicense (selected a) t (rounded n (endpoint a t) : ℝ) ∧
    (rounded n (endpoint a t) : ℝ) + width n ≤
      VariableEnvelope.v (∑ j ∈ selected a, t j)

/-- This is a new producer, with a real inherited fifth branch. -/
def licensedCap (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) : ℝ :=
  finiteMax allActions (Accepted n e q om N pre)
    (fun a => (rounded n (endpoint a (primeHistoryLogCoordinates N 6 pre)) : ℝ))
    (cap5 n e q om N (rosserAncestor 5 pre))

theorem fifth_le_licensedCap (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) :
    cap5 n e q om N (rosserAncestor 5 pre) ≤ licensedCap n e q om N pre :=
  finiteMax_seed_le _ _ _ _

theorem accepted_cap_le (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ)
    (a : Action) (ha : Accepted n e q om N pre a) :
    (rounded n (endpoint a (primeHistoryLogCoordinates N 6 pre)) : ℝ) ≤
      licensedCap n e q om N pre :=
  finiteMax_row_le _ _ _ _ a (mem_allActions a) ha

/-- Every original eligible action is below the COMPLETE raw maximum.
Later actions keep their original chronological predecessor and stage. -/
theorem actual_endpoint_le_current (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (a : Action) (ha : ActualEligible e q om N pre a) :
    endpoint a (primeHistoryLogCoordinates N 6 pre) ≤
      currentSixthExponent e q om N pre := by
  cases a with
  | saved i =>
      have hi : P4AOriginalSavedSixthArchive.endpoint i
          (primeHistoryLogCoordinates N 6 pre) ≤ savedExponent e q om N pre :=
        finiteMax_row_le _ _ _ _ i (Finset.mem_univ _) ha
      exact hi.trans ((saved_le_eleven e q om N pre).trans
        (afterLater_mono e q om N pre (show 0 ≤ 8 by omega)))
  | eleven c =>
      have hc : Certificates.P2OriginalSixthElevenLogSemantics.newCap c
          (primeHistoryLogCoordinates N 6 pre) ≤ elevenExponent e q om N pre :=
        finiteMax_row_le _ _ _ _ c
          (List.mem_toFinset.mpr
            (Certificates.P2OriginalSixthElevenLogSemantics.allCells_complete c)) ha
      exact hc.trans (afterLater_mono e q om N pre (show 0 ≤ 8 by omega))
  | later c =>
      have hc : P4AOriginalSixthLaterSemantics.endpoint c
          (primeHistoryLogCoordinates N 6 pre) ≤
          afterLater e q om N pre (P4AOriginalSixthLaterLiteral.stage c + 1) :=
        finiteMax_row_le _ _ _ _ c (Finset.mem_univ _) ha
      exact hc.trans (afterLater_mono e q om N pre
        (Nat.succ_le_of_lt (P4AOriginalSixthLaterSemantics.original_stage_range c)))

theorem licensedCap_le_old (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) :
    licensedCap n e q om N pre ≤ cap6 n e q om N pre := by
  apply finiteMax_le
  · exact cap5_le_cap6 n e q om N pre
  · intro a _ ha
    have hr := rounded_mono n (actual_endpoint_le_current e q om N pre a ha.1)
    exact hr.trans (le_max_right _ _)

/-- If no rounded action is legal, the result is exactly the real fifth
predecessor. No source state or whole branch is deleted. -/
theorem inherit_of_no_accepted (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (h : ∀ a, ¬Accepted n e q om N pre a) :
    licensedCap n e q om N pre = cap5 n e q om N (rosserAncestor 5 pre) :=
  finiteMax_eq_seed_of_outside _ _ _ _ (fun a _ => h a)

/-- Any strict increase has an actual old action, its own mask, and a
licensed rounded endpoint. The equality branch receives no invented mask. -/
theorem strict_update_licensed (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ)
    (h : cap5 n e q om N (rosserAncestor 5 pre) < licensedCap n e q om N pre) :
    ∃ a ∈ allActions, ActualEligible e q om N pre a ∧
      licensedCap n e q om N pre =
        (rounded n (endpoint a (primeHistoryLogCoordinates N 6 pre)) : ℝ) ∧
      LowerLicense (selected a) (primeHistoryLogCoordinates N 6 pre)
        (licensedCap n e q om N pre) ∧
      licensedCap n e q om N pre + width n ≤
        VariableEnvelope.v (∑ j ∈ selected a, primeHistoryLogCoordinates N 6 pre j) := by
  rcases finiteMax_attained allActions (Accepted n e q om N pre)
      (fun a => (rounded n (endpoint a (primeHistoryLogCoordinates N 6 pre)) : ℝ))
      (cap5 n e q om N (rosserAncestor 5 pre)) with heq | ⟨a,ha,hacc,heq⟩
  · exact (not_lt_of_ge heq.le h).elim
  · exact ⟨a,ha,hacc.1,heq,heq.symm ▸ hacc.2.1,heq.symm ▸ hacc.2.2⟩

theorem licensedCap_mem_alphabet (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) : licensedCap n e q om N pre ∈
      (alphabet n e q).image (fun x : ℚ => (x : ℝ)) := by
  rcases finiteMax_attained allActions (Accepted n e q om N pre)
      (fun a => (rounded n (endpoint a (primeHistoryLogCoordinates N 6 pre)) : ℝ))
      (cap5 n e q om N (rosserAncestor 5 pre)) with heq | ⟨a,_,_,heq⟩
  · rw [heq]
    exact (caps_mem_alphabet n e q om N (rosserAncestor 5 pre)).2.1
  · rw [heq]
    apply Finset.mem_image.mpr
    refine ⟨rounded n (endpoint a (primeHistoryLogCoordinates N 6 pre)), ?_, rfl⟩
    exact Finset.mem_union_right _ (rounded_mem n _)

/-- Exact finite-max equality once all original eligible actions pass the
additional check. This premise is discharged on the public safe stratum. -/
theorem eq_old_of_all_accepted (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ)
    (h : ∀ a, ActualEligible e q om N pre a → Accepted n e q om N pre a) :
    licensedCap n e q om N pre = cap6 n e q om N pre := by
  apply le_antisymm (licensedCap_le_old n e q om N pre)
  by_cases hstrict : cap5 n e q om N (rosserAncestor 5 pre) < cap6 n e q om N pre
  · obtain ⟨a,_,ha,_,hvalue⟩ :=
      P4AOriginalSixthWinningAction.strict_update_winner n e q om N pre hstrict
    rw [hvalue]
    exact accepted_cap_le n e q om N pre a (h a ha)
  · exact (le_of_not_gt hstrict).trans (fifth_le_licensedCap n e q om N pre)

/-- Equality to the old cap is a conclusion on the common safe stratum,
not a global identity and not a numerical saving estimate. -/
theorem licensedCap_eq_old_on_safe (delta : ℝ) (hd : 0 < delta)
    (n : ℕ) (hn : 4 * width n < delta) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 8)
    (c : P4AOriginalFull87SourceDictionary.Cell)
    (hs : P4AOriginalFull87SourceDictionary.Source c (primeHistoryLogCoordinates N 8 pre))
    (ht : primeHistoryLogCoordinates N 8 pre ∈ safe8 delta) :
    licensedCap n e q om N (rosserAncestor 6 pre) =
      cap6 n e q om N (rosserAncestor 6 pre) := by
  apply le_antisymm (licensedCap_le_old n e q om N _)
  by_cases hstrict : cap5 n e q om N (rosserAncestor 5 (rosserAncestor 6 pre)) <
      cap6 n e q om N (rosserAncestor 6 pre)
  · obtain ⟨a,_,ha,_,hvalue⟩ := P4AOriginalSixthWinningAction.strict_update_winner
      n e q om N (rosserAncestor 6 pre) hstrict
    have hl := P4AOriginalSixthWinningAction.all_actual_actions_licensed
      delta hd n hn e q om N pre hlen c hs ht a ha
    rw [hvalue]
    exact accepted_cap_le n e q om N _ a ⟨ha,hl.1,hl.2.2⟩
  · exact (le_of_not_gt hstrict).trans (fifth_le_licensedCap n e q om N _)

/-- The cap change has a concrete original action and small positive
lower-gate defect as a witness. This is not yet an arithmetic mass bound. -/
theorem changed_has_margin_witness (delta : ℝ) (hd : 0 < delta)
    (n : ℕ) (hn : 4 * width n < delta) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 8)
    (c : P4AOriginalFull87SourceDictionary.Cell)
    (hs : P4AOriginalFull87SourceDictionary.Source c (primeHistoryLogCoordinates N 8 pre))
    (hchange : licensedCap n e q om N (rosserAncestor 6 pre) ≠
      cap6 n e q om N (rosserAncestor 6 pre)) :
    ∃ a ∈ allActions, GeometricSource a
        (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)) ∧
      ∃ g : P1QuantizedActionLicense.Gate 6,
        0 < endpoint a (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)) -
          gate (selected a) (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)) g ∧
        endpoint a (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)) -
          gate (selected a) (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)) g < delta := by
  have hnot : primeHistoryLogCoordinates N 8 pre ∉ safe8 delta := by
    intro ht
    exact hchange (licensedCap_eq_old_on_safe delta hd n hn e q om N pre hlen c hs ht)
  change ¬project6 (primeHistoryLogCoordinates N 8 pre) ∈ safe delta at hnot
  rw [P4AOriginalSixthWinningAction.project6_history N pre hlen] at hnot
  exact not_safe_witness delta _ hnot

end
end ImbalancedChen.P4AOriginalSixthLicensedFilter
