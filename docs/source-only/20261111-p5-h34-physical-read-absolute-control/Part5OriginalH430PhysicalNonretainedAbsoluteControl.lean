import ImbalancedChen.Part5OriginalH430ActualWeightedNonretainedClosedCell

/-!
P5.6 / h34 — expose the residual nonretention Theta payment in terms
of the ACTUAL physical and unweighted request reads.

The predecessor proved an exact retained-child cancellation, leaving
the genuine bank/Buchstab physical Theta-1 correction. This packet
proves a literal signed difference of the TWO actual reads and a
two-sided upper envelope using their ABSOLUTE masses at the ORIGINAL
Fin positions, not a freely chosen row or a replacement source.

This does NOT show the two source masses are small or identify a
U3/U4 original full/selected/inherited count owner.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430PhysicalNonretainedAbsoluteControl

noncomputable section
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430AllActionOccurrenceSource
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430ActualRequestNonbankQuantitative
open Part5OriginalH430ActualSelectedRowBudget
open Part5OriginalH430ActualSelectedFeedbackOperator
open Part5OriginalH430ActualSelectedSameQIdealGap
open Part5OriginalH430ActualReadEdgeDefect
open Part5OriginalH430ActualRetainedThetaCancellation
open Part5OriginalH430ActualWeightedNonretainedClosedCell
open Part5OriginalH430ActualNextTableSignedSourceResidual
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger

/-- The actual PHYSICAL Theta-weighted read, restricted to selected
nonretention winners, with their original path marks and multiplicity. -/
def actualNonretainedPhysicalSignedRead (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l ∈ buchstabLevel N n root tau p g ∪
      bankLevel N n root tau p g,
    levelMark l * readTerm N n root tau p g l

/-- The very same winners, but without physical Theta scaling.
No scalar-owner replacement and no synthetic q/tag multiplicity. -/
def actualNonretainedUnweightedSignedRead (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l ∈ buchstabLevel N n root tau p g ∪
      bankLevel N n root tau p g,
    levelMark l *
      requestValue (iterate (g.val + 1)) (levelOccurrence l).current

/-- Absolute ORIGINAL physical read mass at nonretention winners.
Absolute values are taken termwise before summation, not after. -/
def actualNonretainedPhysicalAbsoluteRead (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l ∈ buchstabLevel N n root tau p g ∪
      bankLevel N n root tau p g,
    |levelMark l| * |readTerm N n root tau p g l|

/-- Absolute unweighted request mass on those SAME actual Fin positions.
The two terms have not been paid by the selected coefficient error. -/
def actualNonretainedUnweightedAbsoluteRead (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l ∈ buchstabLevel N n root tau p g ∪
      bankLevel N n root tau p g,
    |levelMark l| *
      |requestValue (iterate (g.val + 1)) (levelOccurrence l).current|

/-- The remaining signed Theta correction is EXACTLY the difference
of the original physical read and the unweighted new-table read.
Retention is absent because it was already cancelled against child. -/
theorem actual_nonretained_theta_correction_is_read_difference
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    actualNonretainedThetaCorrection N n root tau p g =
      actualNonretainedPhysicalSignedRead N n root tau p g -
        actualNonretainedUnweightedSignedRead N n root tau p g := by
  unfold actualNonretainedThetaCorrection
    actualNonretainedPhysicalSignedRead
    actualNonretainedUnweightedSignedRead
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  unfold readTerm
  ring

theorem actual_nonretained_physical_absolute_nonneg
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    0 ≤ actualNonretainedPhysicalAbsoluteRead N n root tau p g := by
  unfold actualNonretainedPhysicalAbsoluteRead
  apply Finset.sum_nonneg
  intro l _
  positivity

theorem actual_nonretained_unweighted_absolute_nonneg
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    0 ≤ actualNonretainedUnweightedAbsoluteRead N n root tau p g := by
  unfold actualNonretainedUnweightedAbsoluteRead
  apply Finset.sum_nonneg
  intro l _
  positivity

private theorem abs_sub_one_le_abs_add_one (t : ℝ) :
    |t - 1| ≤ |t| + 1 := by
  have h := abs_add_le t (-1 : ℝ)
  simpa [sub_eq_add_neg] using h

/-- Actual remaining Theta payment is bounded by the TWO genuine
absolute request read masses, not by an invented epsilon*Theta or a
synthetic U3/U4 owner. No sign or closeness-to-one is assumed for
thetaAtom, and every original winner is charged at most once. -/
theorem actual_nonretained_theta_payment_le_physical_absolute_reads
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    actualNonretainedThetaPayment N n root tau p g ≤
      actualNonretainedPhysicalAbsoluteRead N n root tau p g +
        actualNonretainedUnweightedAbsoluteRead N n root tau p g := by
  unfold actualNonretainedThetaPayment
    actualNonretainedPhysicalAbsoluteRead
    actualNonretainedUnweightedAbsoluteRead
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro l _
  let m : ℝ := levelMark l
  let t : ℝ := thetaAtom N (rootQ N n root tau p)
    (parentProduct (levelOccurrence l).current.old)
  let v : ℝ := requestValue (iterate (g.val + 1))
    (levelOccurrence l).current
  change |m| * |t - 1| * |v| ≤
    |m| * |t * v| + |m| * |v|
  rw [abs_mul]
  calc
    |m| * |t - 1| * |v| =
        (|m| * |v|) * |t - 1| := by ring
    _ ≤ (|m| * |v|) * (|t| + 1) :=
      mul_le_mul_of_nonneg_left
        (abs_sub_one_le_abs_add_one t)
        (mul_nonneg (abs_nonneg m) (abs_nonneg v))
    _ = |m| * |t| * |v| + |m| * |v| := by ring

/-- A TWO-SIDED physical correction estimate, with no assumption that
the new-table source or the physical read has a sign. -/
theorem actual_nonretained_correction_abs_le_physical_absolute_reads
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    |actualNonretainedThetaCorrection N n root tau p g| ≤
      actualNonretainedPhysicalAbsoluteRead N n root tau p g +
        actualNonretainedUnweightedAbsoluteRead N n root tau p g := by
  exact (actual_nonretained_theta_correction_abs_le_payment
    N n root tau p g).trans
      (actual_nonretained_theta_payment_le_physical_absolute_reads
        N n root tau p g)

/-- The genuine physical read-minus-child CLOSED-CELL mismatch now
exposes ONLY original absolute physical/new-table reads, the actual
bank/Buchstab source gaps, and the previously paid selected error.
It does not claim an original arithmetic selected-count bound. -/
theorem actual_weighted_closedcell_abs_read_envelope
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    |(levelReadMass N n root tau p g -
        levelChildMass N n root tau p g) -
      (actualSelectedSameQIdealRead N n root tau p g -
        (levelChildMass N n root tau p g -
          retainedLevelValue N n root tau p g))| ≤
      (|actualBankSourceGap N n root tau p g| +
        |actualBuchstabSourceGap N n root tau p g|) +
      (actualNonretainedPhysicalAbsoluteRead N n root tau p g +
        actualNonretainedUnweightedAbsoluteRead N n root tau p g) +
      actualSelectedError N n root tau p g := by
  have hdefect :=
    actual_weighted_closedcell_ideal_defect_bound N n root tau p g
  have hpayment :=
    actual_nonretained_theta_payment_le_physical_absolute_reads
      N n root tau p g
  linarith only [hdefect, hpayment]

end
end ImbalancedChen.Part5OriginalH430PhysicalNonretainedAbsoluteControl
