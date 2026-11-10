import ImbalancedChen.Part5OriginalH430W1SignedOrdinaryBase
import ImbalancedChen.Part5OriginalH430W2SignedOrdinaryBase
import ImbalancedChen.Part5OriginalH430ActualSelectedRowBudget
import ImbalancedChen.Part5OriginalH430SelectedBankGlobalFloorBaseLedger

/-! The 106 genuine signed ordinary count estimates at the physical marked
positions where the original selector actually chooses that action. A single
threshold precedes the root, history, row and immutable generation. -/
namespace ImbalancedChen.Part5OriginalH430AllBankSignedCounts
noncomputable section
open Finset
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P5CanonicalUpperCancellation (upperA)
open P2OriginalChildPhysicalNormalization (thetaAtom)
open P2Selected430CausalOccurrenceExporter (iterate)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430BankSlotTargets Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedLevelBankSupply Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430FixedReadDictionary Part5OriginalH430SelectedFixedReadSupply
open Part5OriginalH430ImmutableBankProfiles (precedingH)
open Part5OriginalH430ActualFeedbackQuotientRemainders
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger
open Part5OriginalH430ActualSelectedRowBudget
open Part5OriginalH430SeedHistoryMass Part5OriginalH430SelectedOrdinaryPairCounts (trueAt)
open scoped Classical BigOperators

def debt (N : ℕ) (Q L : ℝ) (d : ℕ) (g : Fin 430) : Original106Action → ℝ
  | .inl (i,j) => Part5OriginalH430W1SignedOrdinaryBase.fixedDebt N Q d i j g +
      Part5OriginalH430W1SignedOrdinaryBase.lowerDebt N Q L d i j g/2 +
      Part5OriginalH430W1SignedOrdinaryBase.switchedDebt N Q d i j
  | .inr j => Part5OriginalH430W2SignedOrdinaryBase.rowDebt N Q L d j g

/-- Count minus the old canonical upper function less the *selected current*
table improvement. Both are evaluated at this occurrence's own request. -/
def physicalDefect {N n p : ℕ} {root : Root} {t : ℝ} {g : Fin 430}
    (l : Index N n root t p g) : ℝ :=
  let r := (levelOccurrence l).current
  trueAt l-thetaAtom N (rootQ N n root t p) (wordProduct l)*
    (upperA r.node.physical.argument-requestValue (iterate (g.val+1)) r)

theorem all_106_signed_count_bases {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N → ∀ (n : ℕ) (root : Root) (t : ℝ) (p : ℕ),
      0≤t → t≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈originalBand N root →
      ∀ g : Fin 430,
        (∑ a : Original106Action, ∑ l∈selectedLevel N n root t p g a,
          levelMark l*physicalDefect l) + selectedBankRoundingLoss N n root t p g ≤
        (∑ a : Original106Action, ∑ l∈selectedLevel N n root t p g a,
          levelMark l*debt N (rootQ N n root t p) (wordLevel l) (wordProduct l) g a) +
          ε*actualBankTheta N n root t p g := by
  obtain ⟨T1,h1,w1⟩ := Part5OriginalH430W1SignedOrdinaryBase.selected_W1_signed_base he
  obtain ⟨T2,h2,w2⟩ := Part5OriginalH430W2SignedOrdinaryBase.selected_W2_signed_base he
  refine ⟨max T1 T2,h1.trans (le_max_left _ _),?_⟩
  intro N hN hEven n root t p ht ht' hn hp g
  let Q := rootQ N n root t p
  let S := selectedLevel N n root t p g
  let prior := fun (a : Original106Action) (l : Index N n root t p g) =>
    trueAt l-thetaAtom N Q (wordProduct l)*(upperA (levelOccurrence l).current.node.physical.argument-
      baseValue a-fixedValue (precedingH g) a-idealFeedbackValue (iterate g.val) a)
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have row (a : Original106Action) :
      (∑ l∈S a,levelMark l*prior a l) ≤
        (∑ l∈S a,levelMark l*debt N Q (wordLevel l) (wordProduct l) g a)+ε*markedTheta (S a) := by
    rcases a with ⟨i,j⟩ | j
    · exact w1 N hN1 n root t p ht ht' hn hp g i j
    · exact w2 N hN2 hEven n root t p ht ht' hn hp g j
  have atRow (a : Original106Action) :
      (∑ l∈S a,levelMark l*physicalDefect l) +
      (∑ l∈S a,occurrenceScale N n root t p g l*feedbackRoundingLoss (iterate g.val) a) ≤
        ∑ l∈S a,levelMark l*prior a l := by
    rw [←sum_add_distrib]
    apply sum_le_sum
    intro l hl
    obtain ⟨i,hsel⟩ := (mem_filter.mp hl).2
    have hv := selected_bank_candidate_upper hsel
    rw [action_slot] at hv
    have hi := ideal_feedback_exact (iterate g.val) a
    have hw : requestValue (iterate (g.val+1)) (levelOccurrence l).current +
          feedbackRoundingLoss (iterate g.val) a ≤
        baseValue a+fixedValue (precedingH g) a+idealFeedbackValue (iterate g.val) a := by
      change requestValue (iterate (g.val+1)) (levelOccurrence l).current ≤
        baseValue a+fixedValue (precedingH g) a+feedbackValue (iterate g.val) a at hv
      linarith only [hv,hi]
    have hscale := occurrenceScale_nonneg N n root t p g l (h1.trans hN1) ht ht' hn
      (original_band_prime hp) (original_band_geometry (by omega) hp)
    have hmul := mul_le_mul_of_nonneg_left hw hscale
    dsimp only [occurrenceScale,occurrenceTheta] at hmul
    change (levelMark l*thetaAtom N Q (wordProduct l))*_ ≤
      (levelMark l*thetaAtom N Q (wordProduct l))*_ at hmul
    dsimp only [physicalDefect,prior,occurrenceScale,occurrenceTheta]
    change levelMark l*(trueAt l-thetaAtom N Q (wordProduct l)*_) +
      (levelMark l*thetaAtom N Q (wordProduct l))*_ ≤
      levelMark l*(trueAt l-thetaAtom N Q (wordProduct l)*_)
    linarith only [hmul]
  unfold selectedBankRoundingLoss actualBankTheta
  rw [←sum_add_distrib,mul_sum,←sum_add_distrib]
  apply sum_le_sum
  intro a _
  exact (atRow a).trans (row a)

end
end ImbalancedChen.Part5OriginalH430AllBankSignedCounts
