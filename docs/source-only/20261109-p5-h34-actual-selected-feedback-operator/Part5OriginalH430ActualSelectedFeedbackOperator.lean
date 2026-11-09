import ImbalancedChen.Part5OriginalH430ActualSelectedRowBudget

/-!
P5.6 / h34: consume the exact actual selected Buchstab-or-106-bank row
as a linear operator on the LITERAL predecessor feedback array.

Unlike an abstract 12*Theta (or 5*Theta) bound, this packet exposes
the exact old-array consumer, its disjoint actual-Fin-position source,
and a uniform signed-input operator estimate.  Neither signed cancellation
nor positivity of the old array is assumed.  The original 12-bank and
5-Buchstab budgets remain distinct.

This does NOT identify original arithmetic U3/U4 q/tag counts, prove
CLOSED-CELL induction, or pay the first-excluded signed Euler remainder.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualSelectedFeedbackOperator

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels
open P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430RequestedHistory
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430ActualRequestNonbankQuantitative
open Part5OriginalH430ActualSelectedRowBudget

/-- The actual selected winning row applied to the ORIGINAL preceding
feedback array.  Retention is an exact predecessor read and is NOT
included as a charged coefficient row. -/
def actualSelectedOldRead (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ b : RowAtom, actualSelectedRow N n root tau p g b *
    oldAtomValue (precedingH g) (precedingh g) b

/-- Literal bank/Buchstab split on the preceding old array.  The
original 106 bank alternatives that did not win are not counted. -/
theorem actual_selected_old_read_split
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    actualSelectedOldRead N n root tau p g =
      (∑ b : RowAtom, actualBankRow N n root tau p g b *
        oldAtomValue (precedingH g) (precedingh g) b) +
      (∑ b : RowAtom, actualBuchstabRow N n root tau p g b *
        oldAtomValue (precedingH g) (precedingh g) b) := by
  simp only [actualSelectedOldRead, actualSelectedRow, add_mul,
    Finset.sum_add_distrib]

/-- Exact occurrence-level source, before any arithmetic count-owner
or original-q/tag quotient.  Every generated Fin LIST position is
preserved, even when physical products happen to coincide. -/
theorem actual_selected_old_read_eq_winning_positions
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    actualSelectedOldRead N n root tau p g =
      ∑ l ∈ (buchstabLevel N n root tau p g ∪
        bankLevel N n root tau p g),
        levelMark l *
          (∑ b : RowAtom,
            edgeRow (rootQ N n root tau p)
              (levelOccurrence l).current
              (children N (rootQ N n root tau p) g.val
                (levelOccurrence l).current) b *
            oldAtomValue (precedingH g) (precedingh g) b) := by
  unfold actualSelectedOldRead
  rw [actual_selected_row_eq_positions]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Elementary signed-input estimate: a nonnegative finite row
is bounded on the whole absolute-value ball, not merely on
nonnegative predecessor arrays. -/
theorem nonnegative_row_old_input_bound
    (r v : RowAtom → ℝ) (M : ℝ)
    (hr : ∀ b, 0 ≤ r b)
    (hv : ∀ b, |v b| ≤ M) :
    |∑ b : RowAtom, r b * v b| ≤
      (∑ b : RowAtom, r b) * M := by
  calc
    |∑ b : RowAtom, r b * v b| ≤
        ∑ b : RowAtom, |r b * v b| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b : RowAtom, r b * |v b| := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [abs_mul, abs_of_nonneg (hr b)]
    _ ≤ ∑ b : RowAtom, r b * M := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (hv b) (hr b)
    _ = (∑ b : RowAtom, r b) * M := by
      rw [Finset.sum_mul]

/-- If the true old predecessor entries are absolutely bounded by M,
the actual selected feedback read has exactly the old 12/5 weighted
budget.  No alternative action, negative cancellation, or U3/U4
root-count identity is used. -/
theorem actual_selected_old_read_le_row_budget
    (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (M : ℝ)
    (hM : 0 ≤ M)
    (hOld : ∀ b : RowAtom,
      |oldAtomValue (precedingH g) (precedingh g) b| ≤ M)
    (hRow : ∀ b : RowAtom,
      0 ≤ actualSelectedRow N n root tau p g b)
    (hMass :
      (∑ b : RowAtom, actualSelectedRow N n root tau p g b) ≤
        12 * actualBankTheta N n root tau p g +
        5 * actualBuchstabTheta N n root tau p g) :
    |actualSelectedOldRead N n root tau p g| ≤
      (12 * actualBankTheta N n root tau p g +
        5 * actualBuchstabTheta N n root tau p g) * M := by
  calc
    |actualSelectedOldRead N n root tau p g| ≤
        (∑ b : RowAtom, actualSelectedRow N n root tau p g b) *
          M := by
            exact nonnegative_row_old_input_bound
              (actualSelectedRow N n root tau p g)
              (oldAtomValue (precedingH g) (precedingh g))
              M hRow hOld
    _ ≤ (12 * actualBankTheta N n root tau p g +
        5 * actualBuchstabTheta N n root tau p g) * M :=
      mul_le_mul_of_nonneg_right hMass hM

/-- Uniform manuscript-local consumer: one threshold before N, roots,
generation, actual resolver and ORIGINAL 106 actions.  Unlike the
previous row-mass theorem, this now bounds the true OLD-ARRAY linear
functional of the selected row, even when its entries are signed.

M is a per-generation bound supplied by the preceding feedback
array; it is NOT an asserted arithmetic count hypothesis, and it
cannot replace the missing base/seed or U3/U4 count-source proof. -/
theorem uniform_actual_selected_old_read_operator
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N →
      ∀ n : ℕ, ∀ root : Root, ∀ tau : ℝ,
        0 ≤ tau → tau ≤ 1/12 →
        1/((n:ℝ)+1) ≤ 11/384 →
      ∀ p : ℕ, (p.Prime ∧ p.Coprime N) →
        physicalPrime N p ∈ rootBand root →
      ∀ g : Fin 430,
      ∀ M : ℝ, 0 ≤ M →
        (∀ b : RowAtom,
          |oldAtomValue (precedingH g) (precedingh g) b| ≤ M) →
        actualSelectedError N n root tau p g ≤
          epsilon * actualSelectedTheta N n root tau p g ∧
        actualBankAppliedError N n root tau p g ≤
          epsilon * actualBankTheta N n root tau p g ∧
        |actualSelectedOldRead N n root tau p g| ≤
          (12 * actualBankTheta N n root tau p g +
            5 * actualBuchstabTheta N n root tau p g) * M := by
  obtain ⟨T, hT4, hT⟩ :=
    uniform_actual_selected_error_row_budget he
  refine ⟨T, hT4, ?_⟩
  intro N hN n root tau ht ht' hn p hp hband g M hM hOld
  have h := hT N hN n root tau ht ht' hn p hp hband g
  refine ⟨h.2.2.2.1, h.2.1, ?_⟩
  exact actual_selected_old_read_le_row_budget
    N n root tau p g M hM hOld
    h.2.2.2.2.1 h.2.2.2.2.2

end
end ImbalancedChen.Part5OriginalH430ActualSelectedFeedbackOperator
