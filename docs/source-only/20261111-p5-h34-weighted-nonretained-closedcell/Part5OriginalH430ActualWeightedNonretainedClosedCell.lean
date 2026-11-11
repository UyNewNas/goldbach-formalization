import ImbalancedChen.Part5OriginalH430ActualRetainedThetaCancellation

/-!
P5.6 / h34: genuine PHYSICAL read-minus-child ledger for the actual
nonretention winners, with exact signed bank/Buchstab source gaps.

The retained Theta term cancels exactly. This packet identifies the
remaining physical read with the actual prior-row read and BOTH literal
new-table source gaps, rather than treating a Theta-normalized request as
an unweighted count. It then bounds the discrepancy from the existing
same-Q selected ideal by the previously declared nonretention payment,
without claiming this payment has a U3/U4 count-side upper bound.

The original child/read mass and the same-Q ideal retain their literal
definitions; no arbitrary owner, positive count, additional analytic
input or closed-cell induction premise is invented.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualWeightedNonretainedClosedCell

noncomputable section
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430ActualRequestNonbankQuantitative
open Part5OriginalH430ActualSelectedFeedbackOperator
open Part5OriginalH430ActualSelectedSameQIdealGap
open Part5OriginalH430ActualRetainedSelectedSameQEnvelope
open Part5OriginalH430ActualNextTableSignedSourceResidual
open Part5OriginalH430ActualNextTableThetaFloorBridge
open Part5OriginalH430ActualThetaAbsolutePayment
open Part5OriginalH430ActualRetainedThetaCancellation
open Part5OriginalH430ActualReadEdgeDefect

/-- The *entire* physical nonretention Theta correction is controlled
on BOTH sides by the smaller retained-cancelled payment. In particular,
the earlier one-sided lower bound is not silently used as an absolute
bound. The sum is over actual Buchstab/bank Fin winners only. -/
theorem actual_nonretained_theta_correction_abs_le_payment
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    |actualNonretainedThetaCorrection N n root tau p g| ≤
      actualNonretainedThetaPayment N n root tau p g := by
  unfold actualNonretainedThetaCorrection actualNonretainedThetaPayment
  calc
    |∑ l ∈ buchstabLevel N n root tau p g ∪
        bankLevel N n root tau p g,
        levelMark l *
          ((thetaAtom N (rootQ N n root tau p)
              (parentProduct (levelOccurrence l).current.old) - 1) *
            requestValue (iterate (g.val + 1))
              (levelOccurrence l).current)| ≤
      ∑ l ∈ buchstabLevel N n root tau p g ∪
        bankLevel N n root tau p g,
        |levelMark l *
          ((thetaAtom N (rootQ N n root tau p)
              (parentProduct (levelOccurrence l).current.old) - 1) *
            requestValue (iterate (g.val + 1))
              (levelOccurrence l).current)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      simp only [abs_mul]
      ring

/-- EXACT physical read on the true nonretention part of generation g+1.
The retained child is subtracted BEFORE comparison with previous rows.
Both source gaps and the signed Theta correction are genuine, unpaid
quantities; no mark is quotiented by its physical product. -/
theorem actual_weighted_nonretention_read_exact
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    levelReadMass N n root tau p g -
        retainedLevelValue N n root tau p g =
      actualSelectedOldRead N n root tau p g +
        actualBankSourceGap N n root tau p g +
        actualBuchstabSourceGap N n root tau p g +
        actualNonretainedThetaCorrection N n root tau p g := by
  have hWeighted := actual_weighted_new_table_exact N n root tau p g
  have hSources :=
    actual_new_table_eq_retained_physical_plus_source_gaps
      N n root tau p g
  have hSplit :=
    actual_theta_correction_retained_nonretained N n root tau p g
  have hRet :=
    actual_retained_theta_cancels_to_child N n root tau p g
  unfold actualRetainedSelectedPhysicalRead at hSources
  linarith only [hWeighted, hSources, hSplit, hRet]

/-- A signed, literal defect against the existing SAME-Q fixed-cell /
Buchstab ideal. This is the exact boundary between physical read and
prior-row feedback, not the manuscript's still-open PP/same-rho theorem. -/
theorem actual_weighted_nonretention_same_q_defect_exact
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    levelReadMass N n root tau p g -
        retainedLevelValue N n root tau p g -
        actualSelectedSameQIdealRead N n root tau p g =
      actualBankSourceGap N n root tau p g +
        actualBuchstabSourceGap N n root tau p g +
        actualNonretainedThetaCorrection N n root tau p g +
        (actualSelectedOldRead N n root tau p g -
          actualSelectedSameQIdealRead N n root tau p g) := by
  rw [actual_weighted_nonretention_read_exact N n root tau p g]
  ring

/-- Exactly one selected coefficient error and exactly one nonretention
Theta payment; neither genuine new-table gap is marked paid. -/
theorem actual_weighted_nonretention_same_q_defect_bound
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    |levelReadMass N n root tau p g -
        retainedLevelValue N n root tau p g -
        actualSelectedSameQIdealRead N n root tau p g| ≤
      (|actualBankSourceGap N n root tau p g| +
        |actualBuchstabSourceGap N n root tau p g|) +
        actualNonretainedThetaPayment N n root tau p g +
        actualSelectedError N n root tau p g := by
  rw [actual_weighted_nonretention_same_q_defect_exact N n root tau p g]
  let B := actualBankSourceGap N n root tau p g
  let U := actualBuchstabSourceGap N n root tau p g
  let C := actualNonretainedThetaCorrection N n root tau p g
  let O := actualSelectedOldRead N n root tau p g
  let I := actualSelectedSameQIdealRead N n root tau p g
  let P := actualNonretainedThetaPayment N n root tau p g
  let E := actualSelectedError N n root tau p g
  have hP : |C| ≤ P :=
    actual_nonretained_theta_correction_abs_le_payment N n root tau p g
  have hE : |O - I| ≤ E :=
    actual_selected_same_q_gap_le_error N n root tau p g
  change |B + U + C + (O - I)| ≤ (|B| + |U|) + P + E
  calc
    |B + U + C + (O - I)| =
        |(B + U) + (C + (O - I))| := by congr 1; ring
    _ ≤ |B + U| + |C + (O - I)| := abs_add_le _ _
    _ ≤ (|B| + |U|) + (|C| + |O - I|) :=
      add_le_add (abs_add_le _ _) (abs_add_le _ _)
    _ ≤ (|B| + |U|) + P + E := by
      linarith only [hP, hE]

/-- Read-minus-CHILD on the ORIGINAL physical edge, rather than an
invented closed-cell consumer. The genuine child mass and retained
child cancel algebraically, leaving the same four source obligations. -/
theorem actual_weighted_closedcell_ideal_defect_exact
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    (levelReadMass N n root tau p g -
        levelChildMass N n root tau p g) -
      (actualSelectedSameQIdealRead N n root tau p g -
        (levelChildMass N n root tau p g -
          retainedLevelValue N n root tau p g)) =
      actualBankSourceGap N n root tau p g +
        actualBuchstabSourceGap N n root tau p g +
        actualNonretainedThetaCorrection N n root tau p g +
        (actualSelectedOldRead N n root tau p g -
          actualSelectedSameQIdealRead N n root tau p g) := by
  have h := actual_weighted_nonretention_same_q_defect_exact
    N n root tau p g
  linarith only [h]

/-- Actual physical read-minus-child, with the real retained-child
subtraction and actual old-array same-Q ideal; no previous-cell
CLOSED-CELL induction is asserted or silently discharged. -/
theorem actual_weighted_closedcell_ideal_defect_bound
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    |(levelReadMass N n root tau p g -
        levelChildMass N n root tau p g) -
      (actualSelectedSameQIdealRead N n root tau p g -
        (levelChildMass N n root tau p g -
          retainedLevelValue N n root tau p g))| ≤
      (|actualBankSourceGap N n root tau p g| +
        |actualBuchstabSourceGap N n root tau p g|) +
        actualNonretainedThetaPayment N n root tau p g +
        actualSelectedError N n root tau p g := by
  calc
    _ = |levelReadMass N n root tau p g -
          retainedLevelValue N n root tau p g -
          actualSelectedSameQIdealRead N n root tau p g| := by
          congr 1
          ring
    _ ≤ _ :=
      actual_weighted_nonretention_same_q_defect_bound
        N n root tau p g

end
end ImbalancedChen.Part5OriginalH430ActualWeightedNonretainedClosedCell
