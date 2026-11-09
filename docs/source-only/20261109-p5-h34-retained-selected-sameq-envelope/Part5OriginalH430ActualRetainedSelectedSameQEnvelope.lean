import ImbalancedChen.Part5OriginalH430ActualSelectedSameQIdealGap

/-!
P5.6 / h34 — the ACTUAL retained-read and selected-row same-Q envelope.

This packet combines the literal next-table retention winners with the
already constructed original 106 bank/Buchstab selected physical and same-Q
ideal reads. Retention remains an EXACT new-table request read. The bank and
Buchstab parts are PREDECESSOR old-array coefficient reads. Their sum is
a mixed-generation accounting expression, NOT yet the original full new-table
U3/U4 count: no false equality of markedBankCandidate with old-row values.

The analytic ideal is the literal preceding-array cellReadIdeal/integralRow
target of the previous packet, not yet the manuscript's PP/same-rho integral.
One selected absolute error is paid; the original row budgets 12/5 remain
separate. Root count weights, seed, floor, owner, and the full CLOSED-CELL
arithmetic induction remain OPEN.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualRetainedSelectedSameQEnvelope

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430ActualRequestNonbankQuantitative
open Part5OriginalH430ActualSelectedRowBudget
open Part5OriginalH430ActualSelectedFeedbackOperator
open Part5OriginalH430ActualPredecessorAbsStability
open Part5OriginalH430ActualSelectedSameQIdealGap

/-- Retention at the literal g+1 request table, plus the physical
non-retention winning rows evaluated at the literal preceding array.
This is NOT definitionally the full new-table count. -/
def actualRetainedSelectedPhysicalRead (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  actualRetainedRead N n root tau p g +
    actualSelectedOldRead N n root tau p g

/-- Identical real retention request, replacing ONLY the selected
bank/Buchstab physical coefficient row by its genuine same-Q ideal. -/
def actualRetainedSelectedIdealRead (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  actualRetainedRead N n root tau p g +
    actualSelectedSameQIdealRead N n root tau p g

/-- Adding actual retention does not pay a new coefficient error.
The original scalar/specified-cell resolver is not rerun. -/
theorem actual_retained_selected_same_q_gap_le_error
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    |actualRetainedSelectedPhysicalRead N n root tau p g -
      actualRetainedSelectedIdealRead N n root tau p g| ≤
      actualSelectedError N n root tau p g := by
  have heq :
      actualRetainedSelectedPhysicalRead N n root tau p g -
        actualRetainedSelectedIdealRead N n root tau p g =
      actualSelectedOldRead N n root tau p g -
        actualSelectedSameQIdealRead N n root tau p g := by
    unfold actualRetainedSelectedPhysicalRead actualRetainedSelectedIdealRead
    ring
  rw [heq]
  exact actual_selected_same_q_gap_le_error N n root tau p g

/-- The actual SAME-Q ideal selected row has a numerical bound in terms
of the LITERAL previous-array finite absolute mass, plus the same
already-paid selected coefficient error. No caller-supplied M or ideal
vector and no positivity assumption on preceding atoms. -/
theorem actual_selected_same_q_ideal_abs_envelope
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430)
    (hRow : ∀ b : RowAtom,
      0 ≤ actualSelectedRow N n root tau p g b)
    (hMass :
      (∑ b : RowAtom, actualSelectedRow N n root tau p g b) ≤
        12 * actualBankTheta N n root tau p g +
          5 * actualBuchstabTheta N n root tau p g) :
    |actualSelectedSameQIdealRead N n root tau p g| ≤
      (12 * actualBankTheta N n root tau p g +
        5 * actualBuchstabTheta N n root tau p g) *
          predecessorAbsMass g +
        actualSelectedError N n root tau p g := by
  have hOld := actual_selected_old_read_l1_envelope
    N n root tau p g hRow hMass
  have hGap := actual_selected_same_q_gap_le_error N n root tau p g
  calc
    |actualSelectedSameQIdealRead N n root tau p g| =
      |(actualSelectedSameQIdealRead N n root tau p g -
          actualSelectedOldRead N n root tau p g) +
        actualSelectedOldRead N n root tau p g| := by
          congr 1
          ring
    _ ≤ |actualSelectedSameQIdealRead N n root tau p g -
          actualSelectedOldRead N n root tau p g| +
        |actualSelectedOldRead N n root tau p g| := abs_add_le _ _
    _ = |actualSelectedOldRead N n root tau p g -
          actualSelectedSameQIdealRead N n root tau p g| +
        |actualSelectedOldRead N n root tau p g| := by
          rw [abs_sub_comm]
    _ ≤ actualSelectedError N n root tau p g +
      (12 * actualBankTheta N n root tau p g +
        5 * actualBuchstabTheta N n root tau p g) *
          predecessorAbsMass g := add_le_add hGap hOld
    _ = _ := by ring

/-- An effective bound for the actual retention-plus-ideal accounting
expression. The exact retention term is NOT hidden in a paid 12/5 row. -/
theorem actual_retained_selected_ideal_abs_envelope
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430)
    (hRow : ∀ b : RowAtom,
      0 ≤ actualSelectedRow N n root tau p g b)
    (hMass :
      (∑ b : RowAtom, actualSelectedRow N n root tau p g b) ≤
        12 * actualBankTheta N n root tau p g +
          5 * actualBuchstabTheta N n root tau p g) :
    |actualRetainedSelectedIdealRead N n root tau p g| ≤
      (|actualRetainedRead N n root tau p g| +
        (12 * actualBankTheta N n root tau p g +
          5 * actualBuchstabTheta N n root tau p g) *
            predecessorAbsMass g) +
      actualSelectedError N n root tau p g := by
  unfold actualRetainedSelectedIdealRead
  calc
    |actualRetainedRead N n root tau p g +
        actualSelectedSameQIdealRead N n root tau p g| ≤
      |actualRetainedRead N n root tau p g| +
        |actualSelectedSameQIdealRead N n root tau p g| :=
          abs_add_le _ _
    _ ≤ |actualRetainedRead N n root tau p g| +
        ((12 * actualBankTheta N n root tau p g +
          5 * actualBuchstabTheta N n root tau p g) *
            predecessorAbsMass g +
          actualSelectedError N n root tau p g) := by
          exact add_le_add_left
            (actual_selected_same_q_ideal_abs_envelope
              N n root tau p g hRow hMass) _
    _ = _ := by ring

/-- Zero true bank and Buchstab Theta annihilate both actual selected
physical and selected same-Q ideal rows. Retention is NOT set to zero.
The selected error is the same previously controlled one. -/
theorem actual_selected_same_q_ideal_zero_of_zero_thetas
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (epsilon : ℝ)
    (hRow : ∀ b : RowAtom,
      0 ≤ actualSelectedRow N n root tau p g b)
    (hMass :
      (∑ b : RowAtom, actualSelectedRow N n root tau p g b) ≤
        12 * actualBankTheta N n root tau p g +
          5 * actualBuchstabTheta N n root tau p g)
    (hError : actualSelectedError N n root tau p g ≤
      epsilon * actualSelectedTheta N n root tau p g)
    (hBank : actualBankTheta N n root tau p g = 0)
    (hBuch : actualBuchstabTheta N n root tau p g = 0) :
    actualSelectedSameQIdealRead N n root tau p g = 0 := by
  have hOld := actual_selected_old_read_zero_of_zero_thetas
    N n root tau p g hRow hMass hBank hBuch
  have hGap :
      |actualSelectedOldRead N n root tau p g -
        actualSelectedSameQIdealRead N n root tau p g| ≤ 0 := by
    calc
      _ ≤ actualSelectedError N n root tau p g :=
        actual_selected_same_q_gap_le_error N n root tau p g
      _ ≤ epsilon * actualSelectedTheta N n root tau p g := hError
      _ = 0 := by simp [actualSelectedTheta, hBank, hBuch]
  have hEq : actualSelectedOldRead N n root tau p g =
      actualSelectedSameQIdealRead N n root tau p g := by
    exact sub_eq_zero.mp
      (abs_eq_zero.mp (le_antisymm hGap (abs_nonneg _)))
  exact hEq.symm.trans hOld

/-- A SINGLE N-threshold controls the actual retained+selected physical
to same-Q ideal gap and the absolute size of the resulting ideal
accounting expression. This is a finite feedback operator bound, not a
manuscript PP/same-rho or original U3/U4 CLOSED-CELL count theorem. -/
theorem uniform_actual_retained_selected_same_q_envelope
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N →
      ∀ n : ℕ, ∀ root : Root, ∀ tau : ℝ,
        0 ≤ tau → tau ≤ 1/12 →
        1/((n:ℝ)+1) ≤ 11/384 →
      ∀ p : ℕ, (p.Prime ∧ p.Coprime N) →
        physicalPrime N p ∈ rootBand root →
      ∀ g : Fin 430,
        |actualRetainedSelectedPhysicalRead N n root tau p g -
          actualRetainedSelectedIdealRead N n root tau p g| ≤
          epsilon * actualSelectedTheta N n root tau p g ∧
        |actualRetainedSelectedIdealRead N n root tau p g| ≤
          (|actualRetainedRead N n root tau p g| +
            (12 * actualBankTheta N n root tau p g +
              5 * actualBuchstabTheta N n root tau p g) *
                predecessorAbsMass g) +
          epsilon * actualSelectedTheta N n root tau p g := by
  obtain ⟨T,hT4,hT⟩ := uniform_actual_selected_error_row_budget he
  refine ⟨T,hT4,?_⟩
  intro N hN n root tau ht ht' hn p hp hband g
  have h := hT N hN n root tau ht ht' hn p hp hband g
  constructor
  · exact (actual_retained_selected_same_q_gap_le_error
      N n root tau p g).trans h.2.2.2.1
  · exact (actual_retained_selected_ideal_abs_envelope
      N n root tau p g h.2.2.2.2.1 h.2.2.2.2.2).trans
      (add_le_add_left h.2.2.2.1 _)

end
end ImbalancedChen.Part5OriginalH430ActualRetainedSelectedSameQEnvelope
