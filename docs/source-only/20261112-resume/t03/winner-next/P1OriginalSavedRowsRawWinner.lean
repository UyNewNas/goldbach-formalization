import ImbalancedChen.P4AOriginalSixthTaggedWinner
import ImbalancedChen.P4AOriginalFull87CompleteSixthDispatch

/-! Provenance for the unrounded original raw read. Its own fifth and
sixth values can differ even when their protected finite labels agree.
The comparison and action witness use the existing original programs. -/
namespace ImbalancedChen.P1OriginalSavedRowsRawWinner
noncomputable section
open scoped Classical
open P1AffineTaggedDecision P4AOriginalFourthFifthAffinePrograms
open P4AOriginalCompleteSixthAffinePrograms (fifthAtSix completeProgram fifthAtSix_at_history completeProgram_at_history)
open P4AOriginalSixthTaggedWinner (entries mem_entries witnessTests witnessTests_at_history)
open P4AOriginalSixthActionBank (Entry ActualEligible endpoint mem_allActions)
open P5OriginalCommonRefinedConstructor
open P4AOriginalCompleteSixthChronology (data fifth currentSixthExponent fifth_le_current)

def trace (d : OriginalData) (b : ℚ) : Trace 6 (Option Entry) :=
  .branch (LT (fifthAtSix d b) (completeProgram d b))
    (firstWitness (witnessTests d b) entries) (.leaf none)

theorem actual_read (e : ℚ) (q : ℕ) (a N : ℝ) (b : ℚ) (h : List ℕ)
    (hl : h.length = 6) (hb : lambda3 (data e q a) N h = (b:ℝ)) :
    let t := primeHistoryLogCoordinates N 6 h
    let tag := (trace (data e q a) b).eval t
    (tag = none ↔ currentSixthExponent e q a N h = fifth e q a N h) ∧
    (∀ win : Entry, tag = some win → fifth e q a N h < currentSixthExponent e q a N h ∧
      ActualEligible e q a N h win.val ∧ currentSixthExponent e q a N h = endpoint win.val t) := by
  let d := data e q a
  let t := primeHistoryLogCoordinates N 6 h
  have hf : (fifthAtSix d b).eval t = fifth e q a N h := fifthAtSix_at_history d b N h hl hb
  have hc := completeProgram_at_history e q a N b h hl hb
  dsimp only
  rw [trace,Trace.eval,holds_LT,hf,hc]
  by_cases hlt : fifth e q a N h < currentSixthExponent e q a N h
  · rw [if_pos hlt]
    obtain hinh | ⟨win,hel,hval⟩ := P4AOriginalSixthWinningAction.current_attained e q a N h
    · exact (ne_of_gt hlt hinh).elim
    let entry : Entry := ⟨win,mem_allActions win⟩
    have hpass := (witnessTests_at_history e q a N b h hl hb entry).mpr ⟨hel,hval⟩
    obtain ⟨chosen,hchosen⟩ := firstWitness_exists (witnessTests d b) entries t
      ⟨entry,mem_entries entry,hpass⟩
    refine ⟨?_,?_⟩
    · constructor
      · intro hn
        rw [hn] at hchosen
        cases hchosen
      · intro heq
        exact (ne_of_gt hlt heq).elim
    · intro w hw
      exact ⟨hlt,(witnessTests_at_history e q a N b h hl hb w).mp
        (firstWitness_sound (witnessTests d b) entries t w hw).2⟩
  · rw [if_neg hlt]
    have heq := le_antisymm (le_of_not_gt hlt) (fifth_le_current e q a N h)
    exact ⟨⟨fun _ => heq,fun _ => rfl⟩,fun _ hbad => by cases hbad⟩

/-- Read the unrounded parent in the actual raw policy, down to its
original eighth override. It may vary within a fixed winning-mask box. -/
theorem raw_descendant (e : ℚ) (q : ℕ) (a N : ℝ) (h later : List ℕ)
    (hl : h.length = 6) (hmore : 6 < (later ++ h).length) (pos : Bool) :
    let word := later ++ h
    let keep := ordinaryParityRosserPolicy false (N^currentSixthExponent e q a N h) pos word
    P4AOriginalFull87CompleteSixthDispatch.policy e q a N pos word =
      (if word.length ≤ 8 then keep else
        match P4AOriginalFull87SourceDispatch.ownerAtPrefix N word with
        | none => keep
        | some c => ordinaryParityRosserPolicy false
            (N^P4AOriginalFull87SourceDictionary.newCap c
              (P4AOriginalFull87SourceDispatch.point8 N word)) pos word) := by
  let word := later ++ h
  have hanc : rosserAncestor 6 word = h := by
    rw [show word = later ++ h from rfl,rosserAncestor_append 6 later h hl.ge]
    simp [rosserAncestor,hl]
  have hc : P4AOriginalCompleteSixthChronology.currentSixthPolicy e q a N pos word =
      ordinaryParityRosserPolicy false (N^currentSixthExponent e q a N h) pos word := by
    simp only [P4AOriginalCompleteSixthChronology.currentSixthPolicy,
      firstExitDepthSplicePolicy,if_neg (not_le.mpr hmore),frozenParityRosserPolicy,ancestorFrozenPolicy,hanc]
  dsimp only
  by_cases h8 : word.length ≤ 8
  · rw [if_pos h8,P4AOriginalFull87CompleteSixthDispatch.policy_through_eight e q a N pos word h8,hc]
  · rw [if_neg h8]
    cases own : P4AOriginalFull87SourceDispatch.ownerAtPrefix N word with
    | none => exact (P4AOriginalFull87CompleteSixthDispatch.policy_outside e q a N pos word own).trans hc
    | some c => exact P4AOriginalFull87CompleteSixthDispatch.policy_selected e q a N c pos word
        (lt_of_not_ge h8) own

end
end ImbalancedChen.P1OriginalSavedRowsRawWinner
