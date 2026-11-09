import ImbalancedChen.Part5OriginalH430ActualRetainedSelectedSameQEnvelope

/-!
P5.6 / h34 — literal next-table to predecessor-row source residual.

The actual generation-(g+1) resolver's bank and Buchstab reads are
NOT definitionally the generation-g coefficient rows. The two exact
signed discrepancies below use the real previous array and the real
winning positions. They are UNPAID arithmetic source terms, not
additional coefficient-error permissions.

The resulting identity and two-sided estimate join the complete
generated next-table read to the previous same-root-Q ideal consumer.
The original 106 bank candidate inequality also yields a strictly
one-sided source estimate. Neither result asserts that a source gap
vanishes or is small. Root weights, U3/U4 count ownership, base/seed,
PP/same-rho and CLOSED-CELL induction remain open.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualNextTableSignedSourceResidual

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430RequestedCandidateLevel
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430ActualRequestNonbankQuantitative
open Part5OriginalH430ActualSelectedRowBudget
open Part5OriginalH430ActualSelectedFeedbackOperator
open Part5OriginalH430ActualSelectedSameQIdealGap
open Part5OriginalH430ActualRetainedSelectedSameQEnvelope

/-- The literal, complete generated next-table request read, at the
original Fin-list occurrence positions (including unresolved zeroes). -/
def actualNewTableRead (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l : Index N n root tau p g,
    levelMark l * requestValue (iterate (g.val + 1))
      (levelOccurrence l).current

/-- Bank next-table winners minus the actually selected 106 bank
coefficient rows evaluated on the literal predecessor array. -/
def actualBankSourceGap (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  actualBankRead N n root tau p g -
    ∑ b : RowAtom, actualBankRow N n root tau p g b *
      oldAtomValue (precedingH g) (precedingh g) b

/-- Buchstab next-table winners minus their ACTUAL coefficient rows
evaluated on the same predecessor array. -/
def actualBuchstabSourceGap (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  actualBuchstabRead N n root tau p g -
    ∑ b : RowAtom, actualBuchstabRow N n root tau p g b *
      oldAtomValue (precedingH g) (precedingh g) b

/-- The bank source gap is an exact sum across the original 106 slots,
not an unexplained free scalar supplied by a downstream consumer. -/
theorem actual_bank_source_gap_eq_original_actions
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    actualBankSourceGap N n root tau p g =
      ∑ a : Original106Action,
        (markedBankRead N n root tau p g a -
          ∑ b : RowAtom, levelRow N n root tau p g a b *
            oldAtomValue (precedingH g) (precedingh g) b) := by
  unfold actualBankSourceGap actualBankRead actualBankRow
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]

/-- The Buchstab source gap is the signed sum over the exact
generation-(g+1) winning Fin positions. In particular, equal
physical products at different positions are not identified. -/
theorem actual_buchstab_source_gap_eq_winning_positions
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    actualBuchstabSourceGap N n root tau p g =
      ∑ l ∈ buchstabLevel N n root tau p g,
        levelMark l *
          (requestValue (iterate (g.val + 1))
              (levelOccurrence l).current -
            ∑ b : RowAtom,
              edgeRow (rootQ N n root tau p)
                (levelOccurrence l).current
                (children N (rootQ N n root tau p) g.val
                  (levelOccurrence l).current) b *
              oldAtomValue (precedingH g) (precedingh g) b) := by
  have hOld :
      (∑ b : RowAtom, actualBuchstabRow N n root tau p g b *
        oldAtomValue (precedingH g) (precedingh g) b) =
      ∑ l ∈ buchstabLevel N n root tau p g,
        levelMark l * (∑ b : RowAtom,
          edgeRow (rootQ N n root tau p)
            (levelOccurrence l).current
            (children N (rootQ N n root tau p) g.val
              (levelOccurrence l).current) b *
          oldAtomValue (precedingH g) (precedingh g) b) := by
    unfold actualBuchstabRow
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  unfold actualBuchstabSourceGap actualBuchstabRead
  rw [hOld, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- Exact source bridge. The old selected physical coefficient read
differs from the complete new-table read by these TWO real unpaid gaps.
Retention is reused literally and never replaced by a row charge. -/
theorem actual_new_table_eq_retained_physical_plus_source_gaps
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    actualNewTableRead N n root tau p g =
      actualRetainedSelectedPhysicalRead N n root tau p g +
        actualBankSourceGap N n root tau p g +
        actualBuchstabSourceGap N n root tau p g := by
  unfold actualNewTableRead
  rw [actual_new_table_read_exact]
  unfold actualRetainedSelectedPhysicalRead
    actualBankSourceGap actualBuchstabSourceGap
  rw [actual_selected_old_read_split]
  ring

/-- Two-sided comparison with the true selected same-Q ideal.
Coefficient error is charged ONCE. The two literal next-table
source gaps remain visible and are not silently paid by 12/5 Theta. -/
theorem actual_new_table_same_q_gap_le_source_residuals
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    |actualNewTableRead N n root tau p g -
      actualRetainedSelectedIdealRead N n root tau p g| ≤
      (|actualBankSourceGap N n root tau p g| +
        |actualBuchstabSourceGap N n root tau p g|) +
        actualSelectedError N n root tau p g := by
  calc
    |actualNewTableRead N n root tau p g -
        actualRetainedSelectedIdealRead N n root tau p g| =
      |(actualBankSourceGap N n root tau p g +
          actualBuchstabSourceGap N n root tau p g) +
        (actualRetainedSelectedPhysicalRead N n root tau p g -
          actualRetainedSelectedIdealRead N n root tau p g)| := by
            rw [actual_new_table_eq_retained_physical_plus_source_gaps]
            congr 1
            ring
    _ ≤ |actualBankSourceGap N n root tau p g +
          actualBuchstabSourceGap N n root tau p g| +
        |actualRetainedSelectedPhysicalRead N n root tau p g -
          actualRetainedSelectedIdealRead N n root tau p g| :=
          abs_add_le _ _
    _ ≤ (|actualBankSourceGap N n root tau p g| +
          |actualBuchstabSourceGap N n root tau p g|) +
        |actualRetainedSelectedPhysicalRead N n root tau p g -
          actualRetainedSelectedIdealRead N n root tau p g| :=
          add_le_add_right (abs_add_le _ _) _
    _ ≤ (|actualBankSourceGap N n root tau p g| +
          |actualBuchstabSourceGap N n root tau p g|) +
        actualSelectedError N n root tau p g :=
          add_le_add_left
            (actual_retained_selected_same_q_gap_le_error
              N n root tau p g) _

/-- The original marked bank candidate provides only a ONE-SIDED
upper payment for the real bank source gap; its sign is NOT presumed. -/
def actualBankCandidateGap (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  (∑ a : Original106Action,
      markedBankCandidate N n root tau p g a) -
    ∑ b : RowAtom, actualBankRow N n root tau p g b *
      oldAtomValue (precedingH g) (precedingh g) b

theorem actual_bank_source_gap_le_candidate_gap
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    actualBankSourceGap N n root tau p g ≤
      actualBankCandidateGap N n root tau p g := by
  unfold actualBankSourceGap actualBankCandidateGap actualBankRead
  exact sub_le_sub_right
    (all_markedBankRead_le_candidate N n root tau p g) _

/-- Actual next-table excess above the same-Q ideal admits a
one-sided source budget with the genuine 106 bank candidate gap,
the UNCONTROLLED Buchstab new-table gap, and the already-paid
selected coefficient error. No nonnegative candidate-gap hypothesis
is inserted. -/
theorem actual_new_table_same_q_one_sided_source_budget
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    actualNewTableRead N n root tau p g -
      actualRetainedSelectedIdealRead N n root tau p g ≤
        (actualBankCandidateGap N n root tau p g +
          actualBuchstabSourceGap N n root tau p g) +
        actualSelectedError N n root tau p g := by
  calc
    actualNewTableRead N n root tau p g -
        actualRetainedSelectedIdealRead N n root tau p g =
      (actualBankSourceGap N n root tau p g +
        actualBuchstabSourceGap N n root tau p g) +
      (actualRetainedSelectedPhysicalRead N n root tau p g -
        actualRetainedSelectedIdealRead N n root tau p g) := by
          rw [actual_new_table_eq_retained_physical_plus_source_gaps]
          ring
    _ ≤ (actualBankCandidateGap N n root tau p g +
        actualBuchstabSourceGap N n root tau p g) +
      (actualRetainedSelectedPhysicalRead N n root tau p g -
        actualRetainedSelectedIdealRead N n root tau p g) :=
          add_le_add_right
            (add_le_add_right
              (actual_bank_source_gap_le_candidate_gap
                N n root tau p g) _) _
    _ ≤ (actualBankCandidateGap N n root tau p g +
        actualBuchstabSourceGap N n root tau p g) +
        actualSelectedError N n root tau p g :=
          add_le_add_left
            ((le_abs_self _).trans
              (actual_retained_selected_same_q_gap_le_error
                N n root tau p g)) _

/-- One uniform pre-N threshold for the coefficient error in the
LITERAL new-table comparison. The bank/Buchstab signed source gaps
remain unbounded here and cannot be declared closed-cell counts. -/
theorem uniform_actual_new_table_same_q_source_residual_bound
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N →
      ∀ n : ℕ, ∀ root : Root, ∀ tau : ℝ,
        0 ≤ tau → tau ≤ 1/12 →
        1/((n:ℝ)+1) ≤ 11/384 →
      ∀ p : ℕ, (p.Prime ∧ p.Coprime N) →
        physicalPrime N p ∈ rootBand root →
      ∀ g : Fin 430,
        |actualNewTableRead N n root tau p g -
          actualRetainedSelectedIdealRead N n root tau p g| ≤
          (|actualBankSourceGap N n root tau p g| +
            |actualBuchstabSourceGap N n root tau p g|) +
            epsilon * actualSelectedTheta N n root tau p g := by
  obtain ⟨T, hT4, hT⟩ :=
    uniform_actual_retained_selected_same_q_envelope he
  refine ⟨T, hT4, ?_⟩
  intro N hN n root tau ht ht' hn p hp hband g
  have hGap := (hT N hN n root tau ht ht' hn p hp hband g).1
  exact (actual_new_table_same_q_gap_le_source_residuals
    N n root tau p g).trans (add_le_add_left hGap _)

end
end ImbalancedChen.Part5OriginalH430ActualNextTableSignedSourceResidual
