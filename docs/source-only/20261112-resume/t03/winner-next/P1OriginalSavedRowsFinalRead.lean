import ImbalancedChen.P1OriginalSavedRowsActualAdmission
import ImbalancedChen.P1OriginalSixthWinnerBankRead
import ImbalancedChen.P4AOriginalFiniteFallbackPolicy
import ImbalancedChen.P4AOriginalOrderedSavedGain

/-! Sixth-level reads of the actual finite dispatch. Later tuple entries
leave its sixth ancestor fixed. A selected eighth continuation still
overwrites it at the original exit depth. -/
namespace ImbalancedChen.P1OriginalSavedRowsFinalRead
noncomputable section
open scoped Classical BigOperators
open P4AOriginalSavedSixthHistoricalOwner
open P4AOriginalSavedSixthSigned (pre)
open P4AOriginalSavedSixthArchive (Row)
open P4AOriginalSavedSixthPlanes (box)
open P4AOriginalNewFifthCoverage (Schedule)
open P4AOriginalSavedSixthSourceGates (source_iff)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap)
open P4AOriginalFull87DataPolicy (licensedCap)
open P1OriginalSavedRowsActualAdmission (row_owner)

private theorem valid_from_owner (n : ℕ) (hn : 4*width n < 1/1600)
    (i : Row) {d : P5OriginalCommonRefinedConstructor.OriginalData} (he : 0 ≤ d.e)
    {N : ℕ} (hN : 1 < N) (p : Fin 6 → ℕ) (hp : ∀ j,(p j).Prime)
    (hs : P4AOriginalSavedSixthArchive.Source i (actualPrimeTupleLog N p)) (ho : Owner d N p) :
    FirstExitValidSelection (P4AOriginalFull87DataPolicy.fifthPolicy n d (N:ℝ)) [] true (List.ofFn p) := by
  obtain ⟨ht,hg⟩ := (source_iff i _).mp hs
  have hpos (j) := (hp j).pos
  have hNr : (1:ℝ) < N := by exact_mod_cast hN
  have hanti : StrictAnti p := by
    intro j k hjk
    have H := Real.rpow_lt_rpow_of_exponent_lt hNr (P4AOriginalSavedSixthPrimeMean.ordered6 i ht hjk)
    rw [actualPrimeTupleLog_rpow hN p hpos,actualPrimeTupleLog_rpow hN p hpos] at H
    exact_mod_cast H
  have hcap := P4AOriginalSavedSixthOwnCaps.on_positive i he p ht hg ho n hn
  refine P4AOriginalSixthTupleReverse.from_own_root n d hN p hp hanti (root d N p) ho.stop ?_ ho.initial.le
    ho.first (by linarith only [ho.third]) (by linarith only [ho.fifth]) ?_
  · rw [ho.seed]
    simp [P5OriginalCommonRefinedConstructor.originalSeed,P1OriginalVariableFourthContinuation.seedExponent,
      pre_list,rosserAncestor]
  · simpa [P4AOriginalSavedSixthSigned.old,pre_list,rosserAncestor] using hcap.1

theorem original_and_union_selection (n : ℕ) (hn : 4*width n < 1/1600)
    {e : ℚ} {q : ℕ} (hs : Schedule e q 0) {a : ℝ} (ha : a ≤ 1/100)
    {N : ℕ} (hN : 1 < N) (p : Fin 6 → ℕ) (hp : ∀ j,(p j).Prime) (i : Row)
    (h : P4AOriginalSavedSixthArchive.Source i (actualPrimeTupleLog N p)) :
    FirstExitValidSelection (P4AOriginalFull87DataPolicy.fifthPolicy n
      (P4AOriginalCompleteSixthChronology.data e q a) (N:ℝ)) [] true (List.ofFn p) ∧
    FirstExitValidSelection (P4AOriginalFull87DataPolicy.fifthPolicy n (bank e q a) (N:ℝ))
      [] true (List.ofFn p) := by
  have own := row_owner i hs ha hN p (fun j => (hp j).pos) ((source_iff i _).mp h).1
  exact ⟨valid_from_owner n hn i hs.1 hN p hp h own.1,
    valid_from_owner n hn i hs.1 hN p hp h own.2⟩

/-- The unrounded raw fifth tree also reaches the actual rank-six node.
Only the fifth odd gate needs to be lifted from the protected selection. -/
theorem original_raw_selection (n : ℕ) (hn : 4*width n < 1/1600)
    {e : ℚ} {q : ℕ} (hs : Schedule e q 0) {a : ℝ} (ha : a ≤ 1/100)
    {N : ℕ} (hN : 1 < N) (p : Fin 6 → ℕ) (hp : ∀ j,(p j).Prime)
    (i : Row) (h : P4AOriginalSavedSixthArchive.Source i (actualPrimeTupleLog N p)) :
    FirstExitValidSelection (P5OriginalCommonRefinedConstructor.policy5
      (P4AOriginalCompleteSixthChronology.data e q a) (N:ℝ)) [] true (List.ofFn p) := by
  let d := P4AOriginalCompleteSixthChronology.data e q a
  let h5 := rosserAncestor 5 (pre p)
  obtain ⟨ht,hg⟩ := (source_iff i _).mp h
  have ho := (row_owner i hs ha hN p (fun j => (hp j).pos) ht).1
  have ha5 := (P4AOriginalFull87DataPolicy.active_ancestor d (N:ℝ) 5 (by decide) (pre p)).mpr ho.active
  have hseed : P5OriginalCommonRefinedConstructor.originalSeed d (N:ℝ) h5 = root d N p :=
    (P4AOriginalFull87FiniteParentCaps.originalSeed_ancestor _ _ 5 (by decide) _).trans ho.seed.symm
  have hl : P5OriginalCommonRefinedConstructor.lambda3 d (N:ℝ) h5 = root d N p := by
    rw [P5OriginalCommonRefinedPreservation.lambda3_ancestor _ _ 5 (by decide)]
    exact (P5OriginalCommonRefinedPreservation.lambda3_ancestor d (N:ℝ) 4 (by decide) (pre p)).symm
  have hb := P5OriginalCommonRefinedPreservation.lambda3_le_exponent5 d (N:ℝ) h5
  rw [hl] at hb
  have hf := ho.first
  have hr : 0 ≤ root d N p := by linarith only [hf,(P4AOriginalSavedSixthPrimeMean.bounds i ht 0).1]
  have hceil := (P4AOriginalSavedSixthOwnCaps.raw_parent_upper i hs.1 p ht ho).trans
    (hg.le.trans (VariableEnvelope.v_le_cap _))
  have hle : P4AOriginalFull87DataPolicy.level5Exponent n d (N:ℝ) h5 ≤
      P5OriginalCommonRefinedConstructor.exponent5 d (N:ℝ) h5 := by
    rw [P4AOriginalFull87DataPolicy.level5Exponent,if_pos ha5,P4AOriginalFull87DataPolicy.cap5_eq_protect,hseed]
    exact (P1GuardFrozenFiniteCapAlgebra.protect_error n _ _ hr hb hceil).2.2
  have h5word : h5 = [p 4,p 3,p 2,p 1,p 0] := by simp [h5,pre_list,rosserAncestor]
  rw [h5word] at hle
  have HP := (original_and_union_selection n hn hs ha hN p hp i h).1
  rw [show List.ofFn p = [p 0,p 1,p 2,p 3,p 4,p 5] by simp [List.ofFn_succ]] at HP ⊢
  simp only [FirstExitValidSelection,Bool.not_true,Bool.not_false] at HP ⊢
  obtain ⟨h1,h2,h3,h4,h5gate,_,_⟩ := HP
  refine ⟨h1,h2,h3,h4,?_,P5OriginalCommonRefinedConstructor.policy5_even d (N:ℝ) _,trivial⟩
  simp [P4AOriginalFull87DataPolicy.fifthPolicy,firstExitDepthSplicePolicy,
    frozenParityRosserPolicy,ancestorFrozenPolicy,rosserAncestor,ordinaryParityRosserPolicy,oddFirstExitPolicy] at h5gate
  have hm := ordinaryRosserPrefixAdmissible_mono false _
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN.le : (1:ℝ)≤N) hle) h5gate
  simpa [P5OriginalCommonRefinedConstructor.policy5,P5OriginalCommonRefinedConstructor.level5,
    firstExitDepthSplicePolicy,frozenParityRosserPolicy,ancestorFrozenPolicy,rosserAncestor,
    ordinaryParityRosserPolicy,oddFirstExitPolicy] using hm

theorem selected_words (n : ℕ) (hn : 4*width n < 1/1600)
    {e : ℚ} {q : ℕ} {a ω : ℝ} (hs : Schedule e q a) (hw : ω ≤ a)
    {N : ℕ} (hN : 1 < N) (p : Fin 6 → ℕ) (i : Row)
    (h : P4AOriginalSavedSixthArchive.Source i (actualPrimeTupleLog N p)) :
    p ∈ P4AOriginalOrderedSixthSigned.admitted n (bank e q a) ω N N
      (P4AOriginalFull87RawChronology.cutoff N) ↔ p ∈ P4AOriginalSavedSixthPrimeMean.primes N := by
  have ho := P4AOriginalOrderedSavedGain.source_owner hs hN p i h
  rw [P4AOriginalOrderedFifthOwner.admitted_iff_on_owner n (bank e q a)
    (by exact_mod_cast hs.1 : 0 ≤ ((bank e q a).e:ℝ)) (by exact_mod_cast hN.le) hw p ho]
  exact P4AOriginalSavedSixthOccurrence.admitted_on_source n hn hs hN p h

theorem physical_descendant (i : Row) {e : ℚ} {q : ℕ} (hs : Schedule e q 0)
    {a ω : ℝ} (ha : a ≤ 1/100) (hw : ω ≤ a) {N : ℕ} (hN : 1 < N)
    (p : Fin 6 → ℕ) (hp : ∀ j, 0 < p j) (ht : actualPrimeTupleLog N p ∈ box i)
    (B : Bank) (δ : ℝ) (n : ℕ) (later : List ℕ) (pos : Bool)
    (hmore : 6 < (later ++ pre p).length) :
    let d := bank e q a
    let h := later ++ pre p
    let keep := ordinaryParityRosserPolicy false ((N:ℝ)^licensedCap n d (N:ℝ) (pre p)) pos h
    P4AOriginalFiniteFallbackPolicy.policy B δ n d ω (N:ℝ) pos h =
      (if h.length ≤ 8 then keep else
        match selectedCap δ n (N:ℝ) h with
        | none => keep
        | some v => ordinaryParityRosserPolicy false ((N:ℝ)^(v:ℝ)) pos h) := by
  let d := bank e q a
  let h := later ++ pre p
  have ho := (row_owner i hs ha hN p hp ht).2
  have hl : (pre p).length = 6 := pre_len p
  have h6 : rosserAncestor 6 h = pre p := by
    rw [show h = later ++ pre p from rfl,rosserAncestor_append 6 later (pre p) hl.ge]
    simp [rosserAncestor,hl]
  have h3 : rosserAncestor 3 h = rosserAncestor 3 (pre p) :=
    rosserAncestor_append 3 later (pre p) (by omega)
  have h1 : rosserAncestor 1 h = rosserAncestor 1 (pre p) :=
    rosserAncestor_append 1 later (pre p) (by omega)
  have hx : P4AOriginalFiniteFallbackPolicy.point (N:ℝ) 1 h 0 ≤ VariableEnvelope.mu := by
    rw [P4AOriginalFiniteFallbackPolicy.point,h1,
      primeHistoryLogCoordinates_ancestor (N:ℝ) hl (by decide : 1≤6),pre_log]
    exact (ordered i ht).2.2.2
  have hsup : P1ThirdFallbackSupport.frozenSupported d.e d.chi d.m d.omega (N:ℝ) h := by
    change P1ThirdFallbackSupport.supported _ _ _ _ _ (rosserAncestor 3 h)
    rw [h3]
    exact ho.active.2
  have hsix : P4AOriginalFull87DataPolicy.sixthPolicy n d (N:ℝ) pos h =
      ordinaryParityRosserPolicy false ((N:ℝ)^licensedCap n d (N:ℝ) (pre p)) pos h := by
    simp only [P4AOriginalFull87DataPolicy.sixthPolicy,firstExitDepthSplicePolicy,
      if_neg (not_le.mpr hmore),frozenParityRosserPolicy,ancestorFrozenPolicy,h6,
      P4AOriginalFull87DataPolicy.level6Exponent,if_pos ho.active]
  dsimp only
  rw [P4AOriginalFiniteFallbackPolicy.lower_history B δ n d ω (N:ℝ) pos h hx,
    P4AOriginalOrderedThirdFullPolicy.policy_on_old_owner
      (by exact_mod_cast hs.1 : 0 ≤ (d.e:ℝ)) (by exact_mod_cast hN.le) hw hsup]
  change firstExitDepthSplicePolicy 8 _ _ pos h = _
  by_cases hr : h.length ≤ 8
  · simpa only [firstExitDepthSplicePolicy,if_pos hr] using hsix
  · simp only [firstExitDepthSplicePolicy,if_neg hr,P4AOriginalFull87DataPolicy.eighthContinuation]
    cases hz : selectedCap δ n (N:ℝ) h <;> simp only [hz,hsix]

end
end ImbalancedChen.P1OriginalSavedRowsFinalRead
