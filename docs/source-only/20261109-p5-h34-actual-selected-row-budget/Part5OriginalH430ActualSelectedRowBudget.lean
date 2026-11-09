import ImbalancedChen.Part5OriginalH430ActualRequestNonbankQuantitative

/-!
P5.6 / h34: one pre-N quantitative budget for BOTH genuinely selected
non-retention action families on the same request-generation Fin list.

The genuine g+1 resolver chooses at most one action.  The original
106 winning bank rows carry their original 12*Theta allowance, while
the selected Buchstab winners carry their DIFFERENT 5*Theta allowance.
Their errors are paid once each, with a single uniform threshold.
Retention is an exact predecessor read, NOT a charged bank/Buchstab row.

This is a manuscript-local source bridge, not the arithmetic U3/U4
CLOSED-CELL count induction or a new external analytic input.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualSelectedRowBudget

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430ActualRequestNonbankQuantitative

/-- Original 106 bank Theta, summed only over actually selected action rows. -/
def actualBankTheta (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : ℝ :=
  ∑ a : Original106Action, levelTheta N n root tau p g a

/-- Original 106 bank absolute error on their actual winner positions. -/
def actualBankError (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : ℝ :=
  ∑ a : Original106Action, levelError N n root tau p g a

/-- The applied old-cell bank error, not a second independent charge. -/
def actualBankAppliedError (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action, levelAppliedError N n root tau p g a

/-- Actual nonnegative selected bank row, preserving each Fin occurrence. -/
def actualBankRow (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (b : RowAtom) : ℝ :=
  ∑ a : Original106Action, levelRow N n root tau p g a b

/-- Only bank and Buchstab need a coefficient-row budget; genuine retention
is a direct old-cell value and is not charged as a selected bank row. -/
def actualSelectedTheta (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  actualBankTheta N n root tau p g +
    actualBuchstabTheta N n root tau p g

def actualSelectedError (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  actualBankError N n root tau p g +
    actualBuchstabError N n root tau p g

def actualSelectedRow (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (b : RowAtom) : ℝ :=
  actualBankRow N n root tau p g b +
    actualBuchstabRow N n root tau p g b

/-- Exact bank Theta counts only winning positions, not the 106 alternatives
at every resolved node.  This keeps duplicate physical products when
they occur at distinct original list indices. -/
theorem actual_bank_theta_eq_positions (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) :
    actualBankTheta N n root tau p g =
      ∑ l ∈ bankLevel N n root tau p g,
        levelMark l *
          thetaAtom N (rootQ N n root tau p)
            (parentProduct (levelOccurrence l).current.old) := by
  simpa only [actualBankTheta, levelTheta] using
    (bank_level_sum_eq_original_106 N n root tau p g (fun l =>
      levelMark l *
        thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old))).symm

/-- The bank row is likewise the literal sum over genuinely selected
bank-list positions, not a sum of unchosen candidates. -/
theorem actual_bank_row_eq_positions (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (b : RowAtom) :
    actualBankRow N n root tau p g b =
      ∑ l ∈ bankLevel N n root tau p g,
        levelMark l * edgeRow (rootQ N n root tau p)
          (levelOccurrence l).current
          (children N (rootQ N n root tau p) g.val
            (levelOccurrence l).current) b := by
  simpa only [actualBankRow, levelRow] using
    (bank_level_sum_eq_original_106 N n root tau p g (fun l =>
      levelMark l * edgeRow (rootQ N n root tau p)
        (levelOccurrence l).current
        (children N (rootQ N n root tau p) g.val
          (levelOccurrence l).current) b)).symm

/-- Both paid row families together are exactly the actual Buchstab-or-bank
winner positions.  The two sets are disjoint by the literal resolver,
rather than by any assumption on a scalar selected owner. -/
theorem actual_selected_theta_eq_positions (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) :
    actualSelectedTheta N n root tau p g =
      ∑ l ∈ (buchstabLevel N n root tau p g ∪
        bankLevel N n root tau p g),
        levelMark l *
          thetaAtom N (rootQ N n root tau p)
            (parentProduct (levelOccurrence l).current.old) := by
  rw [actualSelectedTheta, actual_bank_theta_eq_positions,
    actualBuchstabTheta]
  rw [add_comm]
  exact (Finset.sum_union
    (buchstab_bank_disjoint N n root tau p g)).symm

/-- The actual physical row has the same exact occurrence-level union.
No historical product identification or quotient-prime injection is used. -/
theorem actual_selected_row_eq_positions (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (b : RowAtom) :
    actualSelectedRow N n root tau p g b =
      ∑ l ∈ (buchstabLevel N n root tau p g ∪
        bankLevel N n root tau p g),
        levelMark l * edgeRow (rootQ N n root tau p)
          (levelOccurrence l).current
          (children N (rootQ N n root tau p) g.val
            (levelOccurrence l).current) b := by
  rw [actualSelectedRow, actual_bank_row_eq_positions,
    actualBuchstabRow]
  rw [add_comm]
  exact (Finset.sum_union
    (buchstab_bank_disjoint N n root tau p g)).symm

/-- A SINGLE threshold, chosen before all roots, precisions, generations
and original 106 bank actions.  The two genuinely selected families
receive separate 12*Theta and 5*Theta row-mass charges, rather than
inflating the immutable bank norm from 12 to 17.

The absolute error for the combined winners is at most epsilon times
the sum of their genuine Theta masses.  The literal previous-array
bank applied-error term is also controlled by the same bank allowance.
Nothing here assumes or proves original arithmetic CLOSED-CELL counts,
the correct base/seed, root weights, or U3/U4 count-source identity. -/
theorem uniform_actual_selected_error_row_budget
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N →
      ∀ n : ℕ, ∀ root : Root, ∀ tau : ℝ,
        0 ≤ tau → tau ≤ 1/12 →
        1/((n:ℝ)+1) ≤ 11/384 →
      ∀ p : ℕ, (p.Prime ∧ p.Coprime N) →
        physicalPrime N p ∈ rootBand root →
      ∀ g : Fin 430,
        actualBankError N n root tau p g ≤
          epsilon * actualBankTheta N n root tau p g ∧
        actualBankAppliedError N n root tau p g ≤
          epsilon * actualBankTheta N n root tau p g ∧
        actualBuchstabError N n root tau p g ≤
          epsilon * actualBuchstabTheta N n root tau p g ∧
        actualSelectedError N n root tau p g ≤
          epsilon * actualSelectedTheta N n root tau p g ∧
        (∀ b : RowAtom, 0 ≤ actualSelectedRow N n root tau p g b) ∧
        (∑ b : RowAtom, actualSelectedRow N n root tau p g b) ≤
          12 * actualBankTheta N n root tau p g +
          5 * actualBuchstabTheta N n root tau p g := by
  obtain ⟨TB, hTB4, hBank⟩ := uniform_level_bank_supply he
  obtain ⟨TU, hTU4, hNonbank⟩ :=
    uniform_actual_nonbank_quantitative he
  have hT4 : 4 ≤ max TB TU :=
    hTB4.trans (le_max_left TB TU)
  refine ⟨max TB TU, hT4, ?_⟩
  intro N hN n root tau ht ht' hn p hp hband g
  have hBN : TB ≤ N := (le_max_left TB TU).trans hN
  have hUN : TU ≤ N := (le_max_right TB TU).trans hN
  have hbank (a : Original106Action) :=
    hBank N hBN n root tau ht ht' hn p hp hband g a
  have hbuch :=
    hNonbank N hUN n root tau ht ht' hn p hp hband g
  have hBankErr : actualBankError N n root tau p g ≤
      epsilon * actualBankTheta N n root tau p g := by
    unfold actualBankError actualBankTheta
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ => (hbank a).1)
  have hApplied : actualBankAppliedError N n root tau p g ≤
      epsilon * actualBankTheta N n root tau p g := by
    unfold actualBankAppliedError actualBankTheta
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ => (hbank a).2.1)
  have hBankNonneg (b : RowAtom) :
      0 ≤ actualBankRow N n root tau p g b := by
    unfold actualBankRow
    exact Finset.sum_nonneg (fun a _ => (hbank a).2.2.1 b)
  have hBankMass :
      (∑ b : RowAtom, actualBankRow N n root tau p g b) ≤
        12 * actualBankTheta N n root tau p g := by
    unfold actualBankRow actualBankTheta
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ => (hbank a).2.2.2.1)
  have hCombinedErr :
      actualSelectedError N n root tau p g ≤
        epsilon * actualSelectedTheta N n root tau p g := by
    unfold actualSelectedError actualSelectedTheta
    calc
      actualBankError N n root tau p g +
          actualBuchstabError N n root tau p g ≤
        epsilon * actualBankTheta N n root tau p g +
          epsilon * actualBuchstabTheta N n root tau p g :=
            add_le_add hBankErr hbuch.2.1
      _ = epsilon * (actualBankTheta N n root tau p g +
          actualBuchstabTheta N n root tau p g) := by ring
  refine ⟨hBankErr, hApplied, hbuch.2.1, hCombinedErr, ?_, ?_⟩
  · intro b
    unfold actualSelectedRow
    exact add_nonneg (hBankNonneg b) (hbuch.2.2.1 b)
  · calc
      (∑ b : RowAtom, actualSelectedRow N n root tau p g b) =
          (∑ b : RowAtom, actualBankRow N n root tau p g b) +
          (∑ b : RowAtom, actualBuchstabRow N n root tau p g b) := by
            simp only [actualSelectedRow, Finset.sum_add_distrib]
      _ ≤ 12 * actualBankTheta N n root tau p g +
          5 * actualBuchstabTheta N n root tau p g :=
            add_le_add hBankMass hbuch.2.2.2.1

end
end ImbalancedChen.Part5OriginalH430ActualSelectedRowBudget
