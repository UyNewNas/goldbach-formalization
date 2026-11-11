import ImbalancedChen.Part5OriginalH430PhysicalJointSourceDebt
import ImbalancedChen.Part5OriginalH430OriginalUpperOverlapCount

/-!
P5.6 / h34 — transport the ACTUAL physical successor/old-row debt
onto the two ORIGINAL U3/U4 prime bands, without erasing the U4
overlap or postulating any q/tag owner.

The preceding physical joint packet gave a local Fin-occurrence
closed-cell discrepancy estimate. Here the outer indexing is the
manuscript's existing originalBand, not a new artificial prime range.
Each (root,p) keeps its own frozen physical Q and its own actual
generation selected by depth. In the U4 overlap the U3 and U4
physical histories are DISTINCT and both remain in the ledger.

The depth argument only chooses a genuine Fin430 level at each root;
it does NOT assert that one such level is a complete original
selected-count source or that different levels can be counted
simultaneously. Root count weights, q/tag owners, filters, seeds,
PP/same-rho and the nested 430+11 refinement remain OPEN.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430OriginalPrimeBandPhysicalGap

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OriginalUpperOverlapCount
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430ActualRequestNonbankQuantitative
open Part5OriginalH430ActualSelectedFeedbackOperator
open Part5OriginalH430ActualSelectedSameQIdealGap
open Part5OriginalH430ActualWeightedNonretainedClosedCell
open Part5OriginalH430PhysicalJointSourceDebt

/-- Exactly the original physical CLOSED-CELL read-minus-child
discrepancy from the already instantiated same-Q selected ideal.
There is no new free reference array or arithmetic count licence. -/
def actualRootPhysicalClosedCellGap (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  (levelReadMass N n root tau p g -
    levelChildMass N n root tau p g) -
  (actualSelectedSameQIdealRead N n root tau p g -
    (levelChildMass N n root tau p g -
      retainedLevelValue N n root tau p g))

/-- Original U3 and U4 p bands, with the two physical Q values and
the two distinct tagged histories still kept separately. Summing
these residuals is only a SOURCE ledger, not a count theorem. -/
def actualOriginalU34PhysicalSourceDebt (N n : ℕ) (tau : ℝ)
    (depth : Root → ℕ → Fin 430) : ℝ :=
  (∑ p ∈ originalBand N .U3,
    actualPhysicalJointSourceResidualMass
      N n .U3 tau p (depth .U3 p)) +
  (∑ p ∈ originalBand N .U4,
    actualPhysicalJointSourceResidualMass
      N n .U4 tau p (depth .U4 p))

/-- The old-row coefficient error is paid ONCE at each selected
original (root,p) history. This does not replace the true outer
count weights or charge a second time for the physical debt. -/
def actualOriginalU34SelectedRowError (N n : ℕ) (tau : ℝ)
    (depth : Root → ℕ → Fin 430) : ℝ :=
  (∑ p ∈ originalBand N .U3,
    actualSelectedError N n .U3 tau p (depth .U3 p)) +
  (∑ p ∈ originalBand N .U4,
    actualSelectedError N n .U4 tau p (depth .U4 p))

/-- Signed outer sum of actual local closed-cell discrepancies.
This is indexed by the original U3/U4 p selectors, not q receipts. -/
def actualOriginalU34PhysicalClosedCellGap (N n : ℕ) (tau : ℝ)
    (depth : Root → ℕ → Fin 430) : ℝ :=
  (∑ p ∈ originalBand N .U3,
    actualRootPhysicalClosedCellGap
      N n .U3 tau p (depth .U3 p)) +
  (∑ p ∈ originalBand N .U4,
    actualRootPhysicalClosedCellGap
      N n .U4 tau p (depth .U4 p))

/-- The local exact physical source is the one used by this
actual outer p-band consumer, with no new hypotheses. -/
theorem actual_root_physical_closedcell_gap_abs_le
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    |actualRootPhysicalClosedCellGap N n root tau p g| ≤
      actualPhysicalJointSourceResidualMass N n root tau p g +
      actualSelectedError N n root tau p g := by
  simpa only [actualRootPhysicalClosedCellGap] using
    (actual_weighted_closedcell_physical_joint_source_bound
      N n root tau p g)

/-- The original-p-band physical source debt is nonnegative even
when new-table values and physical Theta weights have arbitrary sign. -/
theorem actual_original_u34_physical_source_debt_nonneg
    (N n : ℕ) (tau : ℝ) (depth : Root → ℕ → Fin 430) :
    0 ≤ actualOriginalU34PhysicalSourceDebt N n tau depth := by
  unfold actualOriginalU34PhysicalSourceDebt
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro p hp
    exact actual_physical_joint_source_residual_nonneg
      N n .U3 tau p (depth .U3 p)
  · apply Finset.sum_nonneg
    intro p hp
    exact actual_physical_joint_source_residual_nonneg
      N n .U4 tau p (depth .U4 p)

/-- Exact U3-only plus U4-overlap accounting for the PHYSICAL
selected requests. In an original U4 p band there are TWO
different root-tagged physical histories, hence two separate
source debts, not one artificially shared owner or Q. -/
theorem actual_original_u34_physical_source_overlap
    (N n : ℕ) (tau : ℝ) (depth : Root → ℕ → Fin 430)
    (hN : 1 ≤ N) :
    actualOriginalU34PhysicalSourceDebt N n tau depth =
      (∑ p ∈ upperExclusiveBand N,
        actualPhysicalJointSourceResidualMass
          N n .U3 tau p (depth .U3 p)) +
      (∑ p ∈ originalBand N .U4,
        (actualPhysicalJointSourceResidualMass
           N n .U3 tau p (depth .U3 p) +
         actualPhysicalJointSourceResidualMass
           N n .U4 tau p (depth .U4 p))) := by
  have hd : Disjoint (upperExclusiveBand N)
      (originalBand N .U4) := by
    apply Finset.disjoint_left.mpr
    intro p hp h4
    exact (Finset.mem_sdiff.mp hp).2 h4
  unfold actualOriginalU34PhysicalSourceDebt
  rw [original_u3_band_partition N hN,
    Finset.sum_union hd, Finset.sum_add_distrib]
  ac_rfl

/-- An ACTUAL outer physical CLOSED-CELL discrepancy bound on
the two original p bands. It uses the ONE physical source residual
per winning Fin occurrence and ONE prior selected-row error.
No q/tag count, root-weight-7/2 transport, or smallness claim
is inferred by summing these separate root histories. -/
theorem actual_original_u34_physical_closedcell_gap_bound
    (N n : ℕ) (tau : ℝ) (depth : Root → ℕ → Fin 430) :
    |actualOriginalU34PhysicalClosedCellGap N n tau depth| ≤
      actualOriginalU34PhysicalSourceDebt N n tau depth +
      actualOriginalU34SelectedRowError N n tau depth := by
  have h3 :
      |∑ p ∈ originalBand N .U3,
        actualRootPhysicalClosedCellGap
          N n .U3 tau p (depth .U3 p)| ≤
      ∑ p ∈ originalBand N .U3,
        (actualPhysicalJointSourceResidualMass
          N n .U3 tau p (depth .U3 p) +
         actualSelectedError N n .U3 tau p (depth .U3 p)) := by
    calc
      _ ≤ ∑ p ∈ originalBand N .U3,
        |actualRootPhysicalClosedCellGap
          N n .U3 tau p (depth .U3 p)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        exact actual_root_physical_closedcell_gap_abs_le
          N n .U3 tau p (depth .U3 p)
  have h4 :
      |∑ p ∈ originalBand N .U4,
        actualRootPhysicalClosedCellGap
          N n .U4 tau p (depth .U4 p)| ≤
      ∑ p ∈ originalBand N .U4,
        (actualPhysicalJointSourceResidualMass
          N n .U4 tau p (depth .U4 p) +
         actualSelectedError N n .U4 tau p (depth .U4 p)) := by
    calc
      _ ≤ ∑ p ∈ originalBand N .U4,
        |actualRootPhysicalClosedCellGap
          N n .U4 tau p (depth .U4 p)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        exact actual_root_physical_closedcell_gap_abs_le
          N n .U4 tau p (depth .U4 p)
  have houter :=
    (abs_add_le
      (∑ p ∈ originalBand N .U3,
        actualRootPhysicalClosedCellGap
          N n .U3 tau p (depth .U3 p))
      (∑ p ∈ originalBand N .U4,
        actualRootPhysicalClosedCellGap
          N n .U4 tau p (depth .U4 p))).trans
      (add_le_add h3 h4)
  simpa only [actualOriginalU34PhysicalClosedCellGap,
    actualOriginalU34PhysicalSourceDebt,
    actualOriginalU34SelectedRowError, Finset.sum_add_distrib,
    add_assoc, add_left_comm, add_comm] using houter

end
end ImbalancedChen.Part5OriginalH430OriginalPrimeBandPhysicalGap
