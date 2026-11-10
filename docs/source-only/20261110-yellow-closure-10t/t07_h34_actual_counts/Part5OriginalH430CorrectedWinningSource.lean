import ImbalancedChen.Part5OriginalH430ActualNextTableThetaFloorBridge
import ImbalancedChen.Part5OriginalH430BuchstabCutoffCancellation

/-! The signed new-table gaps at the actual occurrence list, with their own
physical normalizers. The Buchstab upper payment reuses the integer-suffix
and strict-prime estimates at one Q. The bank ledger retains the literal
specified-cell reads and the unapplied base. -/

namespace ImbalancedChen.Part5OriginalH430CorrectedWinningSource

noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open P2EnhancedLowerPrimeChildCarriers
open P2OriginalChildPhysicalNormalization
open P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430BankSlotTargets Part5OriginalH430FixedReadDictionary
open Part5OriginalH430ArithmeticAtomRows Part5OriginalH430ImmutableBankProfiles
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430RequestedCandidateLevel Part5OriginalH430RequestedNonbankLevel
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430ActualRequestNonbankQuantitative
open Part5OriginalH430ActualSelectedRowBudget Part5OriginalH430ActualReadEdgeDefect
open Part5OriginalH430ActualFeedbackQuotientRemainders
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger
open Part5OriginalH430ActualNextTableSignedSourceResidual
open Part5OriginalH430ActualNextTableThetaFloorBridge
open Part5OriginalH430BuchstabDefectIntegralBridge
open Part5OriginalH430BuchstabCutoffCancellation

/-- Restriction of the actual signed Theta change to any set of original
list positions. In the applications the resolver fixes that set. -/
def correctionOn (N n : ℕ) (k : Root) (t : ℝ) (p : ℕ) (g : Fin 430)
    (S : Finset (Index N n k t p g)) : ℝ :=
  ∑ l ∈ S, levelMark l * ((occurrenceTheta N n k t p g l - 1) *
    requestValue (iterate (g.val + 1)) (levelOccurrence l).current)

theorem correction_partition (N n : ℕ) (k : Root) (t : ℝ) (p : ℕ) (g : Fin 430) :
    actualThetaReadCorrection N n k t p g =
      correctionOn N n k t p g (retainedLevel N n k t p g) +
      correctionOn N n k t p g (buchstabLevel N n k t p g) +
      ∑ a : Original106Action, correctionOn N n k t p g (selectedLevel N n k t p g a) :=
  actual_theta_correction_all_actions N n k t p g

private theorem restricted_signed_read (N n : ℕ) (k : Root) (t : ℝ)
    (p : ℕ) (g : Fin 430) (S : Finset (Index N n k t p g)) :
    (∑ l ∈ S, levelMark l *
      requestValue (iterate (g.val + 1)) (levelOccurrence l).current) -
      (∑ b : RowAtom, (∑ l ∈ S, levelMark l *
        edgeRow (rootQ N n k t p) (levelOccurrence l).current
          (children N (rootQ N n k t p) g.val (levelOccurrence l).current) b) *
            oldAtomValue (precedingH g) (precedingh g) b) +
      correctionOn N n k t p g S =
      ∑ l ∈ S, levelDefect N n k t p g l := by
  have hedges :
      (∑ b : RowAtom, (∑ l ∈ S, levelMark l *
        edgeRow (rootQ N n k t p) (levelOccurrence l).current
          (children N (rootQ N n k t p) g.val (levelOccurrence l).current) b) *
            oldAtomValue (precedingH g) (precedingh g) b) =
      ∑ l ∈ S, levelMark l * childTerm N n k t p g l := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    unfold childTerm
    rw [← edgeRow_value, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hedges, ← Finset.sum_sub_distrib, correctionOn, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  unfold levelDefect readTerm occurrenceTheta
  ring

/-- A signed identity at each generation, including zero parent mass.
The new-table read and the entire previous physical coefficient row occur
on the same original Buchstab positions. -/
theorem corrected_buchstab_gap_eq_defects (N n : ℕ) (k : Root)
    (t : ℝ) (p : ℕ) (g : Fin 430) :
    actualBuchstabSourceGap N n k t p g +
      correctionOn N n k t p g (buchstabLevel N n k t p g) =
      ∑ l ∈ buchstabLevel N n k t p g, levelDefect N n k t p g l :=
  restricted_signed_read N n k t p g (buchstabLevel N n k t p g)

/-- The suffix uses the actual selected cell, the inherited ceiling and the
preceding table. Its signed integral residual is nonpositive. The only
positive expense in this Buchstab comparison is the existing row error. -/
theorem corrected_buchstab_gap_le_error (N n : ℕ) (k : Root)
    (t : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 4 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384) (hp : p.Prime ∧ p.Coprime N)
    (hb : physicalPrime N p ∈ rootBand k) :
    actualBuchstabSourceGap N n k t p g +
      correctionOn N n k t p g (buchstabLevel N n k t p g) ≤
      actualBuchstabError N n k t p g := by
  rw [corrected_buchstab_gap_eq_defects, actual_buchstab_error_eq_existing]
  have h := buchstab_defect_le_integral_residual N n k t p g
    (by omega : 1 < N) ht ht' hn hp hb
  have hz := actual_buchstab_residual_nonpos N n k t p g hN ht ht' hn hp hb
  linarith only [h, hz]

theorem uniform_corrected_buchstab_gap {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
    ∀ (n : ℕ) (k : Root) (t : ℝ) (p : ℕ) (g : Fin 430),
      0 ≤ t → t ≤ 1/12 → 1 / ((n : ℝ) + 1) ≤ 11/384 →
      (p.Prime ∧ p.Coprime N) → physicalPrime N p ∈ rootBand k →
      actualBuchstabSourceGap N n k t p g +
        correctionOn N n k t p g (buchstabLevel N n k t p g) ≤
        ε * actualBuchstabTheta N n k t p g := by
  obtain ⟨T, hT4, hT⟩ := uniform_level_buchstab_supply hε
  refine ⟨T, hT4, ?_⟩
  intro N hN n k t p g ht ht' hn hp hb
  have h := corrected_buchstab_gap_le_error N n k t p g
    (hT4.trans hN) ht ht' hn hp hb
  rw [actual_buchstab_error_eq_existing] at h
  rw [actual_buchstab_theta_eq_existing]
  exact h.trans (hT N hN n k t ht ht' hn p hp hb g).1

theorem corrected_bank_gap_eq_defects (N n : ℕ) (k : Root)
    (t : ℝ) (p : ℕ) (g : Fin 430) :
    actualBankSourceGap N n k t p g +
      (∑ a : Original106Action, correctionOn N n k t p g (selectedLevel N n k t p g a)) =
      ∑ a : Original106Action, ∑ l ∈ selectedLevel N n k t p g a,
        levelDefect N n k t p g l := by
  rw [actual_bank_source_gap_eq_original_actions, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  exact restricted_signed_read N n k t p g (selectedLevel N n k t p g a)

/-- The producer's actual specified-cell channel, including both W2
anchor coefficients. A value on a seam can differ from the scalar lookup. -/
def literalFixedMass (N n : ℕ) (k : Root) (t : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action, ∑ l ∈ selectedLevel N n k t p g a,
    occurrenceScale N n k t p g l * fixedValue (iterate g.val true) a

/-- The bank's exact signed comparison before replacing any fixed-cell
entry by an arithmetic defect function. This keeps the positive floor
credit on the left. Base and coefficient-integral adoption are still due. -/
theorem corrected_bank_gap_with_floor (N n : ℕ) (k : Root)
    (t : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 4 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384) (hp : p.Prime ∧ p.Coprime N)
    (hb : physicalPrime N p ∈ rootBand k) :
    actualBankSourceGap N n k t p g +
      (∑ a : Original106Action, correctionOn N n k t p g (selectedLevel N n k t p g a)) +
      selectedBankRoundingLoss N n k t p g +
      selectedBankPrimeChildMass N n k t p g ≤
      selectedBankBaseMass N n k t p g + literalFixedMass N n k t p g +
      selectedBankIdealFeedbackMass N n k t p g := by
  rw [corrected_bank_gap_eq_defects]
  have h := bank_defect_sum_le N n k t p g hN ht ht' hn hp hb
  apply (add_le_add_right (add_le_add_right h _) _).trans
  apply le_of_eq
  unfold selectedBankRoundingLoss selectedBankPrimeChildMass selectedBankBaseMass
    literalFixedMass selectedBankIdealFeedbackMass
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro l _
  rw [ideal_feedback_exact (iterate g.val) a]
  unfold bankCandidateGap occurrenceScale occurrenceTheta
  ring



/-- The variable-prime channels of the actual selected bank positions.
W1 uses its single strict band. W2 uses its three singleton and four pair
bands, with the original 1/5 and the old specified-cell convention. -/
def strictFeedbackMass (N n : ℕ) (k : Root) (t : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action, ∑ l ∈ selectedLevel N n k t p g a,
    levelMark l * (∑ b : RowAtom,
      Part5OriginalH430FixedReadRows.dynamicRow N (rootQ N n k t p)
        (levelOccurrence l).current.old (levelOccurrence l).current.node.physical a b *
        oldAtomValue (precedingH g) (precedingh g) b)

/-- The predecessor edge list actually contains the unchanged-prefix W1
read and both W2 reads as well as strict prime children. -/
theorem actual_bank_children_eq_fixed_add_strict (N n : ℕ) (k : Root)
    (t : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 4 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384) (hp : p.Prime ∧ p.Coprime N)
    (hb : physicalPrime N p ∈ rootBand k) :
    selectedBankPrimeChildMass N n k t p g =
      literalFixedMass N n k t p g + strictFeedbackMass N n k t p g := by
  unfold selectedBankPrimeChildMass literalFixedMass strictFeedbackMass
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro l hl
  obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hl).2
  have hc := Part5OriginalH430RequestedMember.rootHistory_coherent
    (by omega : 1 < N) ht ht' hn hp hb (levelOccurrence_source l).1
  unfold childTerm
  rw [Part5OriginalH430RequestedLocalBankSupply.children_eq_bank hi,
    action_slot, Part5OriginalH430RequestedBankRows.bank_edgeValue_eq
      (Part5OriginalH430RequestedAdmission.coherent_window hc)
      (Part5OriginalH430RequestedAdmission.coherent_residual hc)]
  unfold Part5OriginalH430FixedReadRows.cellReadProfile occurrenceScale occurrenceTheta
  ring

/-- Cancels the specified fixed-cell channel at the same parent Theta and
old array. The remaining bank payment involves the original base and two
explicit dynamic channels. No predecessor count inequality enters here. -/
theorem corrected_bank_gap_after_fixed_cancellation (N n : ℕ) (k : Root)
    (t : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 4 ≤ N) (ht : 0 ≤ t) (ht' : t ≤ 1/12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11/384) (hp : p.Prime ∧ p.Coprime N)
    (hb : physicalPrime N p ∈ rootBand k) :
    actualBankSourceGap N n k t p g +
      (∑ a : Original106Action, correctionOn N n k t p g (selectedLevel N n k t p g a)) +
      selectedBankRoundingLoss N n k t p g + strictFeedbackMass N n k t p g ≤
      selectedBankBaseMass N n k t p g + selectedBankIdealFeedbackMass N n k t p g := by
  have h := corrected_bank_gap_with_floor N n k t p g hN ht ht' hn hp hb
  rw [actual_bank_children_eq_fixed_add_strict N n k t p g hN ht ht' hn hp hb] at h
  linarith only [h]

end
end ImbalancedChen.Part5OriginalH430CorrectedWinningSource

