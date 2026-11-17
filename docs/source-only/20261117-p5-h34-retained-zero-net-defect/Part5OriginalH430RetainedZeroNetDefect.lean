import ImbalancedChen.Part5OriginalH430ActualNetDefect

/-!
P5.6/h34: the genuinely SELECTED retention branch has ZERO combined
one-sided request deficit, rather than merely a signed Theta cancellation.

The original Q80 integer interpreter selects the old cell integer for
retention. Its successor request reads exactly that SAME specified cell
in the predecessor table. Neither an assumed Theta=1 nor a scalar-owner
substitution is used. This eliminates the retained action's contribution
to the net positive-defect ledger at every actual indexed occurrence.

No estimate for the Buchstab or 106-bank positive deficits, count-source
owner, or full CLOSED-CELL induction is asserted.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430RetainedZeroNetDefect
noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels
open Part5OriginalH430DecisionProvenance
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430RequestWaveTelescoping
open Part5OriginalH430PhysicalRequestDefectBridge
open Part5OriginalH430ActualNetDefect

/-- A literal retained successor reads the exact predecessor cell.
Its mode stays specified-cell; its upper/lower type stays unchanged. -/
theorem retained_successor_reads_old_cell
    (N : ℕ) (t : Table) (r : Request) (i : Fin 200) :
    requestValue t (nextRequest r (Edge.retained (N := N) i)) =
      floorValue (t r.node.upper) i := by
  simp [requestValue, nextRequest, edgeMode, edgeShape, edgeCoordinates,
    appendedWord, advance, childUpper, perform]

/-- Exact Q80 integer-retention identity, on the actual g+1 winner.
Unlike a bounded rounding residual, the selected retained numerator
is literally the previous integer: it has NO rounding loss. -/
theorem selected_retention_request_fixed
    (N g : ℕ) (r : Request) (i : Fin 200)
    (hs : Selected g r i .retained) :
    iteratedRequest (g+1) r =
      iteratedRequest g (nextRequest r (Edge.retained (N := N) i)) := by
  have hv := selected_value hs
  have hq :
      (choiceValue (iterate g) r.node.upper i .retained : ℝ) /
        (2^80 : ℝ) = floorValue (iterate g r.node.upper) i := rfl
  rw [hq] at hv
  calc
    iteratedRequest (g+1) r = floorValue (iterate g r.node.upper) i := hv
    _ = iteratedRequest g (nextRequest r (Edge.retained (N := N) i)) :=
      (retained_successor_reads_old_cell N (iterate g) r i).symm

/-- Consequently the *unweighted* one-step retained request defect
vanishes, even though its three separate physical Theta terms need
not vanish individually. -/
theorem selected_retention_local_defect_zero
    (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request) (i : Fin 200)
    (hs : Selected g r i .retained) :
    localDefect N Q iteratedRequest (g+1) r = 0 := by
  rw [selected_retention_defect N Q iteratedRequest g r i hs]
  rw [selected_retention_request_fixed N g r i hs]
  ring

/-- The actual combined positive deficit of a retained node is zero.
The result is stronger than the previous nonnegative max-gap ledger. -/
theorem selected_retention_combined_unpaid_zero
    (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request) (i : Fin 200)
    (hs : Selected g r i .retained) :
    combinedPhysicalUnpaid N Q (g+1) r = 0 := by
  rw [combinedPhysicalUnpaid_eq_positiveDefect]
  simp [positiveDefect, selected_retention_local_defect_zero N Q g r i hs]

/-- Its genuine signed physical parent/source/child TOTAL is zero.
This does NOT claim the individual physical source error is zero. -/
theorem selected_retention_physical_total_zero
    (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request) (i : Fin 200)
    (hs : Selected g r i .retained) :
    parentThetaAt N Q (g+1) r +
      (physicalDefectAt N Q (g+1) r + childThetaAt N Q (g+1) r) = 0 := by
  have h := selected_retention_total_gap N Q g r i hs
  rw [selected_retention_request_fixed N g r i hs, sub_self] at h
  simpa only [parentThetaAt, physicalDefectAt, childThetaAt] using h

/-- The actual retained Fin positions, with their original positive
history occurrence multiplicities, contribute ZERO to the one-sided
unpaid request ledger. The same-Q root and resolved cell are fixed. -/
theorem actual_retained_level_combined_unpaid_zero
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    (∑ l ∈ retainedLevel N n root tau p g,
      levelMark l *
        combinedPhysicalUnpaid N (rootQ N n root tau p)
          (g.val+1) (levelOccurrence l).current) = 0 := by
  apply Finset.sum_eq_zero
  intro l hl
  have hs := retained_level_actual_cell_selected N n root tau p g l hl
  rw [selected_retention_combined_unpaid_zero N
    (rootQ N n root tau p) g.val (levelOccurrence l).current
    (actualRetainedCell N n root tau p g l) hs]
  ring

/-- The corresponding signed triple has the SAME exact zero total.
In particular a retained Theta fee must not be charged again downstream. -/
theorem actual_retained_level_physical_total_zero
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    (∑ l ∈ retainedLevel N n root tau p g,
      levelMark l *
        (parentThetaAt N (rootQ N n root tau p) (g.val+1)
             (levelOccurrence l).current +
         (physicalDefectAt N (rootQ N n root tau p) (g.val+1)
             (levelOccurrence l).current +
          childThetaAt N (rootQ N n root tau p) (g.val+1)
             (levelOccurrence l).current))) = 0 := by
  apply Finset.sum_eq_zero
  intro l hl
  have hs := retained_level_actual_cell_selected N n root tau p g l hl
  rw [selected_retention_physical_total_zero N
    (rootQ N n root tau p) g.val (levelOccurrence l).current
    (actualRetainedCell N n root tau p g l) hs]
  ring

end
end ImbalancedChen.Part5OriginalH430RetainedZeroNetDefect
