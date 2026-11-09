import ImbalancedChen.Part5OriginalH430ActualPredecessorAbsStability

/-!
P5.6 / h34: compare the TRUE winning bank/Buchstab physical coefficient
read with the SAME rootQ and same list-position fixed-cell ideal read.

For a bank winner, the ideal coefficient is the existing cellReadIdeal of
its original 106 slot. For a Buchstab winner, it is the existing integralRow
at the original request's upper/physical node coordinates. Both use the
literal thetaAtom, physical rootQ, previous oldAtomValue, and list mark.
No scalar-mode replacement, q/tag quotient, or new ideal-count licence.

The actual source-level error is controlled by the already-defined
absolute coefficient errors, with no double payment. This is NOT the
complete analytic same-rho integration, base/seed, U3/U4 arithmetic count
identity, or CLOSED-CELL induction.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualSelectedSameQIdealGap

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430RequestedLocalBankSupply
open Part5OriginalH430SelectedFixedReadSupply
open Part5OriginalH430RequestedBankRows
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430ActualRequestNonbankQuantitative
open Part5OriginalH430ActualSelectedRowBudget
open Part5OriginalH430ActualSelectedFeedbackOperator
open Part5OriginalH430ActualPredecessorAbsStability

/-- Finite, fully signed error rule.  The index set and weights are the
actual source positions. No positivity of the predecessor values is used. -/
theorem marked_row_read_gap {ι β : Type*} [Fintype β]
    (S : Finset ι) (mark : ι → ℝ) (r ideal : ι → β → ℝ)
    (v : β → ℝ) (hm : ∀ i ∈ S, 0 ≤ mark i) :
    |(∑ b : β, (∑ i ∈ S, mark i * r i b) * v b) -
       (∑ b : β, (∑ i ∈ S, mark i * ideal i b) * v b)| ≤
      ∑ i ∈ S, mark i * (∑ b : β, |r i b - ideal i b| * |v b|) := by
  have heq :
      (∑ b : β, (∑ i ∈ S, mark i * r i b) * v b) -
        (∑ b : β, (∑ i ∈ S, mark i * ideal i b) * v b) =
        ∑ i ∈ S, mark i * (∑ b : β, (r i b - ideal i b) * v b) := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_mul]
    have hpoint (b : β) :
        (∑ i ∈ S, mark i * r i b) -
          (∑ i ∈ S, mark i * ideal i b) =
          ∑ i ∈ S, mark i * (r i b - ideal i b) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    simp_rw [hpoint, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [heq]
  calc
    |∑ i ∈ S, mark i * (∑ b : β, (r i b - ideal i b) * v b)| ≤
        ∑ i ∈ S, |mark i * (∑ b : β, (r i b - ideal i b) * v b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ S, mark i * |∑ b : β, (r i b - ideal i b) * v b| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (hm i hi)]
    _ ≤ ∑ i ∈ S, mark i * (∑ b : β, |r i b - ideal i b| * |v b|) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (hm i hi)
      calc
        |∑ b : β, (r i b - ideal i b) * v b| ≤
            ∑ b : β, |(r i b - ideal i b) * v b| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ b : β, |r i b - ideal i b| * |v b| := by
          simp only [abs_mul]

/-- Bank ideal read is the exact original 106 winning-cell fixed-read
integral coefficient evaluated on the literal preceding feedback array. -/
def actualBankSameQIdealRead (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action, ∑ b : RowAtom,
    (∑ l ∈ selectedLevel N n root tau p g a,
      levelMark l * (thetaAtom N (rootQ N n root tau p)
        (parentProduct (levelOccurrence l).current.old) * cellReadIdeal a b)) *
      oldAtomValue (precedingH g) (precedingh g) b

/-- Buchstab ideal read uses the ACTUAL original history coordinates
and the same physical Q as the corresponding physical edge row. -/
def actualBuchstabSameQIdealRead (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ b : RowAtom,
    (∑ l ∈ buchstabLevel N n root tau p g,
      levelMark l * (thetaAtom N (rootQ N n root tau p)
        (parentProduct (levelOccurrence l).current.old) *
        integralRow (levelOccurrence l).current.node.upper
          (levelOccurrence l).current.node.physical b)) *
      oldAtomValue (precedingH g) (precedingh g) b

def actualSelectedSameQIdealRead (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  actualBankSameQIdealRead N n root tau p g +
    actualBuchstabSameQIdealRead N n root tau p g

/-- The bank coefficientwise error already charged by all 106 genuine
winners controls the whole signed physical-minus-ideal bank read. -/
theorem actual_bank_same_q_ideal_gap
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    |(∑ b : RowAtom, actualBankRow N n root tau p g b *
        oldAtomValue (precedingH g) (precedingh g) b) -
      actualBankSameQIdealRead N n root tau p g| ≤
        actualBankError N n root tau p g := by
  have hlocal (a : Original106Action) :
      |(∑ b : RowAtom, levelRow N n root tau p g a b *
          oldAtomValue (precedingH g) (precedingh g) b) -
        (∑ b : RowAtom,
          (∑ l ∈ selectedLevel N n root tau p g a,
            levelMark l * (thetaAtom N (rootQ N n root tau p)
              (parentProduct (levelOccurrence l).current.old) * cellReadIdeal a b)) *
            oldAtomValue (precedingH g) (precedingh g) b)| ≤
          levelError N n root tau p g a := by
    simpa only [levelRow, levelError, requestError, mul_assoc] using
      (marked_row_read_gap
        (selectedLevel N n root tau p g a)
        (fun l => levelMark l)
        (fun l b => edgeRow (rootQ N n root tau p)
          (levelOccurrence l).current
          (children N (rootQ N n root tau p) g.val
            (levelOccurrence l).current) b)
        (fun l b => thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) * cellReadIdeal a b)
        (fun b => oldAtomValue (precedingH g) (precedingh g) b)
        (fun l hl => (mark_pos _).le))
  have hphysical :
      (∑ b : RowAtom, actualBankRow N n root tau p g b *
        oldAtomValue (precedingH g) (precedingh g) b) =
      ∑ a : Original106Action, ∑ b : RowAtom,
        levelRow N n root tau p g a b *
          oldAtomValue (precedingH g) (precedingh g) b := by
    simp only [actualBankRow, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hphysical]
  unfold actualBankSameQIdealRead actualBankError
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun a _ => hlocal a))

/-- One actual Buchstab family, indexed by true winning Fin occurrences,
with its literal physical upper/physical integralRow profile. -/
theorem actual_buchstab_same_q_ideal_gap
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    |(∑ b : RowAtom, actualBuchstabRow N n root tau p g b *
        oldAtomValue (precedingH g) (precedingh g) b) -
      actualBuchstabSameQIdealRead N n root tau p g| ≤
        actualBuchstabError N n root tau p g := by
  simpa only [actualBuchstabRow, actualBuchstabSameQIdealRead,
    actualBuchstabError, mul_assoc] using
    (marked_row_read_gap
      (buchstabLevel N n root tau p g)
      (fun l => levelMark l)
      (fun l b => edgeRow (rootQ N n root tau p)
        (levelOccurrence l).current
        (children N (rootQ N n root tau p) g.val
          (levelOccurrence l).current) b)
      (fun l b => thetaAtom N (rootQ N n root tau p)
        (parentProduct (levelOccurrence l).current.old) *
        integralRow (levelOccurrence l).current.node.upper
          (levelOccurrence l).current.node.physical b)
      (fun b => oldAtomValue (precedingH g) (precedingh g) b)
      (fun l hl => (mark_pos _).le))

/-- The exact actual winning physical read has no more same-Q
fixed-cell/integral discrepancy than the existing selected absolute
coefficient error. This is NOT yet the full original arithmetic count. -/
theorem actual_selected_same_q_gap_le_error
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    |actualSelectedOldRead N n root tau p g -
      actualSelectedSameQIdealRead N n root tau p g| ≤
        actualSelectedError N n root tau p g := by
  have hbank := actual_bank_same_q_ideal_gap N n root tau p g
  have hbuch := actual_buchstab_same_q_ideal_gap N n root tau p g
  have heq :
      actualSelectedOldRead N n root tau p g -
        actualSelectedSameQIdealRead N n root tau p g =
      ((∑ b : RowAtom, actualBankRow N n root tau p g b *
        oldAtomValue (precedingH g) (precedingh g) b) -
        actualBankSameQIdealRead N n root tau p g) +
      ((∑ b : RowAtom, actualBuchstabRow N n root tau p g b *
        oldAtomValue (precedingH g) (precedingh g) b) -
        actualBuchstabSameQIdealRead N n root tau p g) := by
    rw [actual_selected_old_read_split]
    unfold actualSelectedSameQIdealRead
    ring
  rw [heq]
  calc
    |((∑ b : RowAtom, actualBankRow N n root tau p g b *
        oldAtomValue (precedingH g) (precedingh g) b) -
        actualBankSameQIdealRead N n root tau p g) +
      ((∑ b : RowAtom, actualBuchstabRow N n root tau p g b *
        oldAtomValue (precedingH g) (precedingh g) b) -
        actualBuchstabSameQIdealRead N n root tau p g)| ≤
      |(∑ b : RowAtom, actualBankRow N n root tau p g b *
        oldAtomValue (precedingH g) (precedingh g) b) -
        actualBankSameQIdealRead N n root tau p g| +
      |(∑ b : RowAtom, actualBuchstabRow N n root tau p g b *
        oldAtomValue (precedingH g) (precedingh g) b) -
        actualBuchstabSameQIdealRead N n root tau p g| := abs_add_le _ _
    _ ≤ actualBankError N n root tau p g +
        actualBuchstabError N n root tau p g := add_le_add hbank hbuch
    _ = actualSelectedError N n root tau p g := rfl

/-- One pre-N threshold controls the TRUE selected physical feedback
versus the actual same-Q integral/fixed-read vector with no invented
ideal array and no extra fee. This does not identify the manuscript's
PP/same-rho integral or prove a closed-cell arithmetic count licence. -/
theorem uniform_actual_selected_same_q_gap
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N →
      ∀ n : ℕ, ∀ root : Root, ∀ tau : ℝ,
        0 ≤ tau → tau ≤ 1/12 →
        1/((n:ℝ)+1) ≤ 11/384 →
      ∀ p : ℕ, (p.Prime ∧ p.Coprime N) →
        physicalPrime N p ∈ rootBand root →
      ∀ g : Fin 430,
        |actualSelectedOldRead N n root tau p g -
          actualSelectedSameQIdealRead N n root tau p g| ≤
          epsilon * actualSelectedTheta N n root tau p g := by
  obtain ⟨T,hT4,hT⟩ := uniform_actual_selected_error_row_budget he
  refine ⟨T,hT4,?_⟩
  intro N hN n root tau ht ht' hn p hp hband g
  exact (actual_selected_same_q_gap_le_error N n root tau p g).trans
    (hT N hN n root tau ht ht' hn p hp hband g).2.2.2.1

end
end ImbalancedChen.Part5OriginalH430ActualSelectedSameQIdealGap
