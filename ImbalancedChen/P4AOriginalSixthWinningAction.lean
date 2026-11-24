import ImbalancedChen.P4AOriginalSixthCommonMargin
import ImbalancedChen.P4AOriginalFull87ActionLicenseIntegration

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

The COMPLETE sixth producer is traced back to a real saved, eleven, or
later action, using the SAME actual guards and chronological currents.
Only a STRICT increase above the finite fifth parent is assigned a mask.
On equality/inheritance no fictitious sixth action is introduced.

The common square-margin stratum licenses every actual eligible action,
not only an arbitrarily chosen winner. This establishes pointwise actual
provenance and uniform licensing, NOT a constant winning mask on a whole
previously certified parent box or preservation of signed numerical gains.
-/
namespace ImbalancedChen.P4AOriginalSixthWinningAction
noncomputable section
open scoped Classical BigOperators
open P1OriginalVariableFourthContinuation P1GuardFrozenFiniteCapAlgebra
open P5OriginalCommonRefinedConstructor P4AOriginalCompleteSixthChronology
open P4AOriginalFull87FiniteParentCaps P4AOriginalSixthActionBank
open P4AOriginalSixthCommonMargin P1QuantizedActionLicense
open P4AOriginalFull87HistoryCore (width)

/-- At each stage the actual maximum is either the ORIGINAL fifth parent
or the endpoint of one actual previously applied action. Equal endpoints
are allowed; no uniqueness or global monotonicity of signed weights is used. -/
theorem afterLater_attained (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) (k : ℕ) :
    afterLater e q om N pre k = fifth e q om N pre ∨
      ∃ a : Action, ActualEligible e q om N pre a ∧
        afterLater e q om N pre k = endpoint a (primeHistoryLogCoordinates N 6 pre) := by
  have hs : savedExponent e q om N pre = fifth e q om N pre ∨
      ∃ a : Action, ActualEligible e q om N pre a ∧
        savedExponent e q om N pre = endpoint a (primeHistoryLogCoordinates N 6 pre) := by
    rcases finiteMax_attained Finset.univ (fun i => savedEligible e q om N i pre)
      (fun i => P4AOriginalSavedSixthArchive.endpoint i (primeHistoryLogCoordinates N 6 pre))
      (fifth e q om N pre) with h | ⟨i,_,hi,h⟩
    · exact Or.inl h
    · exact Or.inr ⟨.saved i,hi,h⟩
  have he : elevenExponent e q om N pre = fifth e q om N pre ∨
      ∃ a : Action, ActualEligible e q om N pre a ∧
        elevenExponent e q om N pre = endpoint a (primeHistoryLogCoordinates N 6 pre) := by
    rcases finiteMax_attained
      Certificates.P2OriginalSixthElevenLogSemantics.allCells.toFinset
      (fun c => eligibleSixth (data e q om) N c pre)
      (fun c => Certificates.P2OriginalSixthElevenLogSemantics.newCap c
        (primeHistoryLogCoordinates N 6 pre))
      (savedExponent e q om N pre) with h | ⟨c,_,hc,h⟩
    · change elevenExponent e q om N pre = savedExponent e q om N pre at h
      rcases hs with hs | ⟨a,ha,hs⟩
      · exact Or.inl (h.trans hs)
      · exact Or.inr ⟨a,ha,h.trans hs⟩
    · exact Or.inr ⟨.eleven c,hc,h⟩
  induction k with
  | zero => exact he
  | succ k ih =>
      rcases finiteMax_attained Finset.univ
        (fun c => laterEligible k (afterLater e q om N pre k) N c pre)
        (fun c => P4AOriginalSixthLaterSemantics.endpoint c
          (primeHistoryLogCoordinates N 6 pre))
        (afterLater e q om N pre k) with h | ⟨c,_,hc,h⟩
      · change afterLater e q om N pre (k+1) = afterLater e q om N pre k at h
        rcases ih with hi | ⟨a,ha,hi⟩
        · exact Or.inl (h.trans hi)
        · exact Or.inr ⟨a,ha,h.trans hi⟩
      · have hstage : P4AOriginalSixthLaterLiteral.stage c = k := hc.2.1
        have hactual : ActualEligible e q om N pre (.later c) := by
          simpa only [ActualEligible, hstage] using hc
        exact Or.inr ⟨.later c,hactual,h⟩

theorem current_attained (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) :
    currentSixthExponent e q om N pre = fifth e q om N pre ∨
      ∃ a : Action, ActualEligible e q om N pre a ∧
        currentSixthExponent e q om N pre = endpoint a (primeHistoryLogCoordinates N 6 pre) :=
  afterLater_attained e q om N pre 8

/-- A strict finite update really equals the biased-floor value of an
actual raw-current-eligible action. Quantization does not re-run guards. -/
theorem strict_update_winner (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ)
    (hwin : cap5 n e q om N (rosserAncestor 5 pre) < cap6 n e q om N pre) :
    ∃ a ∈ allActions, ActualEligible e q om N pre a ∧
      currentSixthExponent e q om N pre = endpoint a (primeHistoryLogCoordinates N 6 pre) ∧
      cap6 n e q om N pre = (rounded n (endpoint a
        (primeHistoryLogCoordinates N 6 pre)) : ℝ) := by
  rcases current_attained e q om N pre with hinherit | ⟨a,ha,hraw⟩
  · have heq : cap6 n e q om N pre = cap5 n e q om N (rosserAncestor 5 pre) := by
      rw [cap6_eq_protect, hinherit, cap5_eq_protect,
        originalSeed_ancestor _ _ 5 (by decide)]
      rfl
    exact (not_lt_of_ge heq.le hwin).elim
  · have hb : originalSeed (data e q om) N pre ≤
        cap5 n e q om N (rosserAncestor 5 pre) := by
      rw [cap5_eq_protect, originalSeed_ancestor _ _ 5 (by decide)]
      exact seed_le_protect _ _ _
    have heq : cap6 n e q om N pre =
        protect n (originalSeed (data e q om) N pre)
          (endpoint a (primeHistoryLogCoordinates N 6 pre)) := by
      rw [cap6_eq_protect,hraw]
    have hgt := hb.trans_lt hwin
    rw [heq] at hgt
    have hrounded : originalSeed (data e q om) N pre <
        (rounded n (endpoint a (primeHistoryLogCoordinates N 6 pre)) : ℝ) := by
      simpa only [protect,lt_max_iff,lt_self_iff_false,false_or] using hgt
    refine ⟨a,mem_allActions a,ha,hraw,?_⟩
    rw [heq,protect,max_eq_right hrounded.le]

/-- The coordinate range needed by saved-square licensing is derived from
original87 geometry at the OWN sixth ancestor. -/
theorem source_third_bound (N : ℝ) (pre : List ℕ) (hlen : pre.length = 8)
    (c : P4AOriginalFull87SourceDictionary.Cell)
    (hs : P4AOriginalFull87SourceDictionary.Source c
      (primeHistoryLogCoordinates N 8 pre)) :
    primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre) 2 ≤ VariableEnvelope.mu := by
  rw [primeHistoryLogCoordinates_ancestor N hlen (by decide : 6 ≤ 8) (2 : Fin 6)]
  have ho : StrictAnti (primeHistoryLogCoordinates N 8 pre) :=
    Fin.strictAnti_iff_succ_lt.mpr (P4AOriginalFull87SourceDictionary.source_basic hs).2.2.2
  exact (ho.antitone (show (0 : Fin 8) ≤ 2 by decide)).trans
    (P4AOriginalFull87SourceDictionary.source_basic hs).1.le

theorem project6_history (N : ℝ) (pre : List ℕ) (hlen : pre.length = 8) :
    project6 (primeHistoryLogCoordinates N 8 pre) =
      primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre) := by
  funext i
  exact (primeHistoryLogCoordinates_ancestor N hlen (by decide : 6 ≤ 8) i).symm

/-- ALL actual sixth actions are licensed on one common stratum, even
before choosing a winner. The actual dynamic parent guards are unchanged. -/
theorem all_actual_actions_licensed (delta : ℝ) (hd : 0 < delta)
    (n : ℕ) (hn : 4 * width n < delta) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 8)
    (c : P4AOriginalFull87SourceDictionary.Cell)
    (hs : P4AOriginalFull87SourceDictionary.Source c (primeHistoryLogCoordinates N 8 pre))
    (ht : primeHistoryLogCoordinates N 8 pre ∈ safe8 delta)
    (a : Action) (ha : ActualEligible e q om N (rosserAncestor 6 pre) a) :
    let t := primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)
    LowerLicense (selected a) t (rounded n (endpoint a t) : ℝ) ∧
    (∀ g : P1QuantizedActionLicense.Gate 6,
      gate (selected a) t g + delta / 2 < (rounded n (endpoint a t) : ℝ)) ∧
    (rounded n (endpoint a t) : ℝ) + width n ≤
      VariableEnvelope.v (∑ j ∈ selected a, t j) := by
  have hgeo := actualEligible_geometric e q om N (rosserAncestor 6 pre)
    (source_third_bound N pre hlen c hs) a ha
  change project6 (primeHistoryLogCoordinates N 8 pre) ∈ safe delta at ht
  rw [project6_history N pre hlen] at ht
  exact safe_rounded delta hd n hn _ ht a hgeo

/-- Actual winner, exact mask, all buffered square licences and selected
upper debit at the SAME cap6. No uniform licence record is a premise. -/
theorem strict_update_licensed (delta : ℝ) (hd : 0 < delta)
    (n : ℕ) (hn : 4 * width n < delta) (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 8)
    (c : P4AOriginalFull87SourceDictionary.Cell)
    (hs : P4AOriginalFull87SourceDictionary.Source c (primeHistoryLogCoordinates N 8 pre))
    (ht : primeHistoryLogCoordinates N 8 pre ∈ safe8 delta)
    (hwin : cap5 n e q om N (rosserAncestor 5 pre) <
      cap6 n e q om N (rosserAncestor 6 pre)) :
    ∃ a ∈ allActions, ActualEligible e q om N (rosserAncestor 6 pre) a ∧
      cap6 n e q om N (rosserAncestor 6 pre) =
        (rounded n (endpoint a (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre))) : ℝ) ∧
      (∀ g : P1QuantizedActionLicense.Gate 6,
        gate (selected a) (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)) g + delta / 2 <
          cap6 n e q om N (rosserAncestor 6 pre)) ∧
      cap6 n e q om N (rosserAncestor 6 pre) + width n ≤
        VariableEnvelope.v (∑ j ∈ selected a,
          primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre) j) := by
  have hwin' : cap5 n e q om N (rosserAncestor 5 (rosserAncestor 6 pre)) <
      cap6 n e q om N (rosserAncestor 6 pre) := by
    simpa only [rosserAncestor_nested 5 6 (by decide)] using hwin
  obtain ⟨a,ha,hg,_hraw,hvalue⟩ := strict_update_winner n e q om N
    (rosserAncestor 6 pre) hwin'
  have hl := all_actual_actions_licensed delta hd n hn e q om N pre hlen c hs ht a hg
  refine ⟨a,ha,hg,hvalue,?_,?_⟩
  · rw [hvalue]
    exact hl.2.1
  · rw [hvalue]
    exact hl.2.2

end
end ImbalancedChen.P4AOriginalSixthWinningAction
