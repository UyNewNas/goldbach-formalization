import ImbalancedChen.Part5OriginalH430JointPositionSourceGap

/-!
P5.6 / h34: combine the two ACTUAL unpaid source terms before
taking absolute values.

The preceding packet bounded the new-table minus old-row residual
and the physical Theta-1 correction separately. Both occur at the
SAME selected bank/Buchstab Fin position. Here their signed sum is
identified with one physical successor-minus-predecessor-row residual:

  (Vnew - RowOld) + (Theta - 1) * Vnew = Theta * Vnew - RowOld.

This avoids charging the same new-table value in two independently
absolute budgets. The physical successor is the original readTerm:
no new q/tag owner, artificial positivity, or smallness condition
is introduced. Original U3/U4 owner/count, base/seed/floor,
PP/same-rho, and common 430+11 closure remain OPEN.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430PhysicalJointSourceDebt

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
open Part5OriginalH430JointPositionSourceGap

/-- The one physical successor-minus-predecessor-row debt at the
ORIGINAL selected nonretention Fin positions. Repeated physical
products and repeated q/tag candidates are NOT merged. -/
def actualPhysicalJointSourceResidualMass (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l ∈ buchstabLevel N n root tau p g ∪
      bankLevel N n root tau p g,
    |levelMark l| *
      |readTerm N n root tau p g l -
        ∑ b : RowAtom,
          edgeRow (rootQ N n root tau p)
            (levelOccurrence l).current
            (children N (rootQ N n root tau p) g.val
              (levelOccurrence l).current) b *
            oldAtomValue (precedingH g) (precedingh g) b|

theorem actual_physical_joint_source_residual_nonneg
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    0 ≤ actualPhysicalJointSourceResidualMass N n root tau p g := by
  unfold actualPhysicalJointSourceResidualMass
  apply Finset.sum_nonneg
  intro l _
  positivity

/-- An exact merger of the joint signed table source discrepancy
AND the remaining physical Theta correction, at the same original
winner position. Retention has already cancelled against its child. -/
theorem actual_joint_physical_gap_eq_position_residuals
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    actualBankSourceGap N n root tau p g +
        actualBuchstabSourceGap N n root tau p g +
        actualNonretainedThetaCorrection N n root tau p g =
      ∑ l ∈ buchstabLevel N n root tau p g ∪
          bankLevel N n root tau p g,
        levelMark l *
          (readTerm N n root tau p g l -
            ∑ b : RowAtom,
              edgeRow (rootQ N n root tau p)
                (levelOccurrence l).current
                (children N (rootQ N n root tau p) g.val
                  (levelOccurrence l).current) b *
              oldAtomValue (precedingH g) (precedingh g) b) := by
  rw [actual_joint_source_gap_eq_position_residuals]
  unfold actualNonretainedThetaCorrection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  unfold readTerm
  ring

/-- The SIGNED physical gap can be paid by ONE absolute residual sum,
not an independent bank/Buchstab source budget plus a Theta budget. -/
theorem actual_joint_physical_gap_abs_le_position_residuals
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    |actualBankSourceGap N n root tau p g +
        actualBuchstabSourceGap N n root tau p g +
        actualNonretainedThetaCorrection N n root tau p g| ≤
      actualPhysicalJointSourceResidualMass N n root tau p g := by
  rw [actual_joint_physical_gap_eq_position_residuals]
  unfold actualPhysicalJointSourceResidualMass
  calc
    |∑ l ∈ buchstabLevel N n root tau p g ∪
        bankLevel N n root tau p g,
        levelMark l *
          (readTerm N n root tau p g l -
            ∑ b : RowAtom,
              edgeRow (rootQ N n root tau p)
                (levelOccurrence l).current
                (children N (rootQ N n root tau p) g.val
                  (levelOccurrence l).current) b *
              oldAtomValue (precedingH g) (precedingh g) b)| ≤
      ∑ l ∈ buchstabLevel N n root tau p g ∪
        bankLevel N n root tau p g,
        |levelMark l *
          (readTerm N n root tau p g l -
            ∑ b : RowAtom,
              edgeRow (rootQ N n root tau p)
                (levelOccurrence l).current
                (children N (rootQ N n root tau p) g.val
                  (levelOccurrence l).current) b *
              oldAtomValue (precedingH g) (precedingh g) b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      rw [abs_mul]

private theorem physical_term_le_split
    (m t v r : ℝ) :
    |m| * |t * v - r| ≤
      |m * (v - r)| + |m| * |t - 1| * |v| := by
  have htri :
      |t * v - r| ≤ |v - r| + |(t - 1) * v| := by
    calc
      |t * v - r| = |(v - r) + (t - 1) * v| := by
        congr 1
        ring
      _ ≤ |v - r| + |(t - 1) * v| := abs_add_le _ _
  calc
    |m| * |t * v - r| ≤
      |m| * (|v - r| + |(t - 1) * v|) :=
        mul_le_mul_of_nonneg_left htri (abs_nonneg m)
    _ = |m * (v - r)| + |m| * |t - 1| * |v| := by
      rw [abs_mul, abs_mul]
      ring

/-- The merged physical debt is NEVER larger than the two previously
defined separate absolute debts. This is a termwise fact, not an
unproved cancellation assumption or a quantitative U3/U4 count bound. -/
theorem actual_physical_joint_source_le_separate_debts
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    actualPhysicalJointSourceResidualMass N n root tau p g ≤
      actualNonretainedSourceResidualMass N n root tau p g +
        actualNonretainedThetaPayment N n root tau p g := by
  unfold actualPhysicalJointSourceResidualMass
    actualNonretainedSourceResidualMass
    actualNonretainedThetaPayment
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro l _
  exact physical_term_le_split
    (levelMark l)
    (thetaAtom N (rootQ N n root tau p)
      (parentProduct (levelOccurrence l).current.old))
    (requestValue (iterate (g.val + 1))
      (levelOccurrence l).current)
    (∑ b : RowAtom,
      edgeRow (rootQ N n root tau p)
        (levelOccurrence l).current
        (children N (rootQ N n root tau p) g.val
          (levelOccurrence l).current) b *
      oldAtomValue (precedingH g) (precedingh g) b)

/-- A tighter actual physical CLOSED-CELL mismatch, charged by
one real physical next-table versus predecessor row residual and
the existing selected coefficient error. NO new smallness premise. -/
theorem actual_weighted_closedcell_physical_joint_source_bound
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    |(levelReadMass N n root tau p g -
        levelChildMass N n root tau p g) -
      (actualSelectedSameQIdealRead N n root tau p g -
        (levelChildMass N n root tau p g -
          retainedLevelValue N n root tau p g))| ≤
      actualPhysicalJointSourceResidualMass N n root tau p g +
        actualSelectedError N n root tau p g := by
  rw [actual_weighted_closedcell_ideal_defect_exact]
  let B := actualBankSourceGap N n root tau p g
  let U := actualBuchstabSourceGap N n root tau p g
  let C := actualNonretainedThetaCorrection N n root tau p g
  let O := actualSelectedOldRead N n root tau p g
  let I := actualSelectedSameQIdealRead N n root tau p g
  let S := actualPhysicalJointSourceResidualMass N n root tau p g
  let E := actualSelectedError N n root tau p g
  have hsource : |B + U + C| ≤ S :=
    actual_joint_physical_gap_abs_le_position_residuals
      N n root tau p g
  have hselected : |O - I| ≤ E :=
    actual_selected_same_q_gap_le_error N n root tau p g
  change |B + U + C + (O - I)| ≤ S + E
  exact (abs_add_le (B + U + C) (O - I)).trans
    (add_le_add hsource hselected)

end
end ImbalancedChen.Part5OriginalH430PhysicalJointSourceDebt
