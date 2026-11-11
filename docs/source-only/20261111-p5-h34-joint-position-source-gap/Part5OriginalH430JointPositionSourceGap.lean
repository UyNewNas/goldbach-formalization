import ImbalancedChen.Part5OriginalH430PhysicalNonretainedAbsoluteControl

/-!
P5.6 / h34 — joint actual bank/Buchstab new-table source gap
at the ORIGINAL winning Fin positions.

The previous physical CLOSED-CELL envelope charged the absolute bank
and Buchstab source gaps separately. This packet identifies their
SIGNED JOINT gap with the exact per-request discrepancy between
generation-(g+1) table values and generation-g selected coefficient
rows, then pays it by a termwise absolute source-residual mass.

This retains every actual position (including repeated physical
products), the original 106 bank actions, true same-Q, selected
specified-cell/scalar reads, and one occurrence mark per winner.
The residual is NOT claimed small or identified with original U3/U4
q/tag selected counts. No new analytic assumption is introduced.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430JointPositionSourceGap

noncomputable section
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430ActualRequestNonbankQuantitative
open Part5OriginalH430ActualSelectedFeedbackOperator
open Part5OriginalH430ActualSelectedSameQIdealGap
open Part5OriginalH430ActualNextTableSignedSourceResidual
open Part5OriginalH430ActualRetainedThetaCancellation
open Part5OriginalH430ActualWeightedNonretainedClosedCell
open Part5OriginalH430PhysicalNonretainedAbsoluteControl

/-- Sum of absolute NEW-TABLE versus ACTUAL predecessor-row residuals.
The sum is over genuine Buchstab/106-bank winning Fin occurrences.
A repeated product is charged once per actual historical occurrence,
not once per distinct product, and retention has already cancelled. -/
def actualNonretainedSourceResidualMass (N n : ℕ)
    (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l ∈ buchstabLevel N n root tau p g ∪
      bankLevel N n root tau p g,
    |levelMark l *
      (requestValue (iterate (g.val + 1)) (levelOccurrence l).current -
        ∑ b : RowAtom,
          edgeRow (rootQ N n root tau p)
            (levelOccurrence l).current
            (children N (rootQ N n root tau p) g.val
              (levelOccurrence l).current) b *
            oldAtomValue (precedingH g) (precedingh g) b)|

/-- The TWO formerly separate source gaps are EXACTLY one signed
per-occurrence sum. This is a row/table identity, NOT an original
arithmetic selected-count identity. -/
theorem actual_joint_source_gap_eq_position_residuals
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    actualBankSourceGap N n root tau p g +
        actualBuchstabSourceGap N n root tau p g =
      ∑ l ∈ buchstabLevel N n root tau p g ∪
          bankLevel N n root tau p g,
        levelMark l *
          (requestValue (iterate (g.val + 1))
              (levelOccurrence l).current -
            ∑ b : RowAtom,
              edgeRow (rootQ N n root tau p)
                (levelOccurrence l).current
                (children N (rootQ N n root tau p) g.val
                  (levelOccurrence l).current) b *
              oldAtomValue (precedingH g) (precedingh g) b) := by
  have hbank :
      actualBankRead N n root tau p g =
        ∑ l ∈ bankLevel N n root tau p g,
          levelMark l *
            requestValue (iterate (g.val + 1))
              (levelOccurrence l).current := by
    unfold actualBankRead
    simpa only [markedBankRead] using
      (bank_level_sum_eq_original_106 N n root tau p g
        (fun l => levelMark l *
          requestValue (iterate (g.val + 1))
            (levelOccurrence l).current)).symm
  have hnew :
      actualBuchstabRead N n root tau p g +
        actualBankRead N n root tau p g =
      ∑ l ∈ buchstabLevel N n root tau p g ∪
          bankLevel N n root tau p g,
        levelMark l *
          requestValue (iterate (g.val + 1))
            (levelOccurrence l).current := by
    calc
      _ = (∑ l ∈ buchstabLevel N n root tau p g,
            levelMark l *
              requestValue (iterate (g.val + 1))
                (levelOccurrence l).current) +
          (∑ l ∈ bankLevel N n root tau p g,
            levelMark l *
              requestValue (iterate (g.val + 1))
                (levelOccurrence l).current) := by
              rw [hbank]
              rfl
      _ = _ := (Finset.sum_union
        (buchstab_bank_disjoint N n root tau p g)).symm
  have hold :=
    actual_selected_old_read_eq_winning_positions
      N n root tau p g
  have hgap :
      actualBankSourceGap N n root tau p g +
          actualBuchstabSourceGap N n root tau p g =
        (actualBuchstabRead N n root tau p g +
          actualBankRead N n root tau p g) -
          actualSelectedOldRead N n root tau p g := by
    unfold actualBankSourceGap actualBuchstabSourceGap
    rw [actual_selected_old_read_split]
    ring
  rw [hgap, hnew, hold, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem actual_nonretained_source_residual_nonneg
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    0 ≤ actualNonretainedSourceResidualMass N n root tau p g := by
  unfold actualNonretainedSourceResidualMass
  apply Finset.sum_nonneg
  intro l _
  exact abs_nonneg _

/-- An exact finite source identifies the presently UNPAID sum of
real next-table residuals. No new smallness assumption is inserted. -/
theorem actual_joint_source_gap_abs_le_position_residuals
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    |actualBankSourceGap N n root tau p g +
        actualBuchstabSourceGap N n root tau p g| ≤
      actualNonretainedSourceResidualMass N n root tau p g := by
  rw [actual_joint_source_gap_eq_position_residuals]
  unfold actualNonretainedSourceResidualMass
  exact Finset.abs_sum_le_sum_abs _ _

/-- Keep the bank+Buchstab source gap JOINT. Its signed cancellation
is legitimate in the exact physical CLOSED-CELL identity; replacing
this by two independent absolute payments is optional, not required.
The physical Theta correction is still genuinely unpaid. -/
theorem actual_weighted_closedcell_joint_source_bound
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    |(levelReadMass N n root tau p g -
        levelChildMass N n root tau p g) -
      (actualSelectedSameQIdealRead N n root tau p g -
        (levelChildMass N n root tau p g -
          retainedLevelValue N n root tau p g))| ≤
      |actualBankSourceGap N n root tau p g +
        actualBuchstabSourceGap N n root tau p g| +
      actualNonretainedThetaPayment N n root tau p g +
      actualSelectedError N n root tau p g := by
  rw [actual_weighted_closedcell_ideal_defect_exact]
  let B := actualBankSourceGap N n root tau p g
  let U := actualBuchstabSourceGap N n root tau p g
  let C := actualNonretainedThetaCorrection N n root tau p g
  let O := actualSelectedOldRead N n root tau p g
  let I := actualSelectedSameQIdealRead N n root tau p g
  let P := actualNonretainedThetaPayment N n root tau p g
  let E := actualSelectedError N n root tau p g
  have hP : |C| ≤ P :=
    actual_nonretained_theta_correction_abs_le_payment
      N n root tau p g
  have hE : |O - I| ≤ E :=
    actual_selected_same_q_gap_le_error N n root tau p g
  change |B + U + C + (O - I)| ≤ |B + U| + P + E
  calc
    |B + U + C + (O - I)| =
        |(B + U) + (C + (O - I))| := by
          congr 1
          ring
    _ ≤ |B + U| + |C + (O - I)| := abs_add_le _ _
    _ ≤ |B + U| + P + E := by
      have htriangle := abs_add_le C (O - I)
      linarith only [htriangle, hP, hE]

/-- Final actionable local envelope: the actual per-request table
residual plus the two physical/unweighted absolute source masses and
the already charged selected coefficient error. Each term has an
explicit original Fin-position definition. It is NOT an H430 count
estimate, and none of the first three masses is declared small. -/
theorem actual_weighted_closedcell_position_source_envelope
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    |(levelReadMass N n root tau p g -
        levelChildMass N n root tau p g) -
      (actualSelectedSameQIdealRead N n root tau p g -
        (levelChildMass N n root tau p g -
          retainedLevelValue N n root tau p g))| ≤
      actualNonretainedSourceResidualMass N n root tau p g +
      actualNonretainedPhysicalAbsoluteRead N n root tau p g +
      actualNonretainedUnweightedAbsoluteRead N n root tau p g +
      actualSelectedError N n root tau p g := by
  have hjoint :=
    actual_weighted_closedcell_joint_source_bound
      N n root tau p g
  have hsource :=
    actual_joint_source_gap_abs_le_position_residuals
      N n root tau p g
  have htheta :=
    actual_nonretained_theta_payment_le_physical_absolute_reads
      N n root tau p g
  linarith only [hjoint, hsource, htheta]

end
end ImbalancedChen.Part5OriginalH430JointPositionSourceGap
