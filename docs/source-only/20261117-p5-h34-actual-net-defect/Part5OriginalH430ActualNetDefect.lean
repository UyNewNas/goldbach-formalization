import ImbalancedChen.Part5OriginalH430PhysicalRequestDefectBridge
import ImbalancedChen.Part5OriginalH430ActualRequestAllActionPartition

/-!
P5.6/h34: one-sided ACTUAL selected-request physical residual.
Take the positive part AFTER parent Theta, same-Q source, and child
Theta corrections combine. Charging all three separately would count
retention normalization more than once. The true retained Fin positions
are summed with original occurrence marks and the root's physical Q.
No original U3/U4 count owner or CLOSED-CELL quantitative bound is
asserted. SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualNetDefect
noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430PhysicalRoots
open P5OriginalFeedbackTableKernels
open P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430ActualRequestAllActionWave
open Part5OriginalH430RequestWaveTelescoping
open Part5OriginalH430PhysicalRequestDefectBridge

/-- One combined unpaid positive part, not three positive charges. -/
def combinedPhysicalUnpaid (N : ℕ) (Q : ℝ)
    (j : ℕ) (r : Request) : ℝ :=
  max 0 (parentThetaAt N Q j r +
    (physicalDefectAt N Q j r + childThetaAt N Q j r))

theorem combinedPhysicalUnpaid_eq_positiveDefect
    (N : ℕ) (Q : ℝ) (j : ℕ) (r : Request) :
    combinedPhysicalUnpaid N Q j r =
      positiveDefect N Q iteratedRequest j r := by
  rw [combinedPhysicalUnpaid, positiveDefect,
    every_generation_physical_split]

theorem combinedPhysicalUnpaid_nonneg
    (N : ℕ) (Q : ℝ) (j : ℕ) (r : Request) :
    0 ≤ combinedPhysicalUnpaid N Q j r :=
  le_max_left (0 : ℝ) _

/-- True full request wave, bounded by seed and the COMBINED physical
positive part. Unpaid does not mean small or controlled by counts. -/
theorem root_le_terminal_plus_combined_physical_unpaid
    (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request) :
    iteratedRequest g r ≤
      waveAccount N Q g r (terminalSeed iteratedRequest) +
      waveAccount N Q g r (combinedPhysicalUnpaid N Q) := by
  have h := root_le_terminal_plus_unpaid_defects
    N Q iteratedRequest g r
  simpa only [waveAccount, combinedPhysicalUnpaid_eq_positiveDefect]
    using h

/-- The retained position's entire unpaid source is a predecessor
request difference with no additional parent/child Theta fee. -/
theorem selected_retention_combined_unpaid
    (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request)
    (i : Fin 200) (hs : Selected g r i .retained) :
    combinedPhysicalUnpaid N Q (g+1) r =
      max 0 (iteratedRequest (g+1) r -
        iteratedRequest g (nextRequest r (.retained i))) := by
  rw [combinedPhysicalUnpaid_eq_positiveDefect, positiveDefect,
    selected_retention_defect N Q iteratedRequest g r i hs]

/-- All actual strict-prime Buchstab successors, not a scalar proxy. -/
theorem selected_buchstab_combined_unpaid
    (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request)
    (i : Fin 200) (hs : Selected g r i .buchstab) :
    combinedPhysicalUnpaid N Q (g+1) r =
      max 0 (iteratedRequest (g+1) r -
        ((singleChildren
          (.buchstab r.node.upper r.node.physical.argument)
          N Q r.old r.node.physical.ceiling).toList.map
          (fun p => iteratedRequest g
            (nextRequest r (.buchstab r.node.upper p)))).sum) := by
  rw [combinedPhysicalUnpaid_eq_positiveDefect, positiveDefect,
    selected_buchstab_defect N Q iteratedRequest g r i hs]

/-- Only the original bank winner's row, with literal edge weights. -/
theorem selected_bank_combined_unpaid
    (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request)
    (i : Fin 200) (k : Fin 106)
    (hs : Selected g r i (.bank k)) :
    combinedPhysicalUnpaid N Q (g+1) r =
      max 0 (iteratedRequest (g+1) r -
        ((bankEdges N Q r (actionOfSlot k)).map
          (fun e => edgeWeight e *
            iteratedRequest g (nextRequest r e))).sum) := by
  rw [combinedPhysicalUnpaid_eq_positiveDefect, positiveDefect,
    selected_bank_defect N Q iteratedRequest g r i k hs]

/-- The actual retained predecessor cell. The default is not used on
an actual retained Fin index. -/
def actualRetainedCell (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (l : Index N n root tau p g) : Fin 200 :=
  (resolve (g.val+1) (levelOccurrence l).current).getD 0

theorem retained_level_actual_cell_selected
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (l : Index N n root tau p g)
    (hl : l ∈ retainedLevel N n root tau p g) :
    Selected g.val (levelOccurrence l).current
      (actualRetainedCell N n root tau p g l) .retained := by
  have hc : actualChoice N n root tau p g l = some .retained :=
    (Finset.mem_filter.mp hl).2
  obtain ⟨i, hs⟩ :=
    (actual_choice_iff_selected N n root tau p g l .retained).1 hc
  have hi : resolve (g.val+1) (levelOccurrence l).current = some i := hs.1
  simpa [actualRetainedCell, hi] using hs

/-- Signed retention correction cancels at EVERY genuine Fin occurrence,
under exactly the original path mark and SAME physical root Q. -/
theorem actual_retained_level_signed_cancellation
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    (∑ l ∈ retainedLevel N n root tau p g,
      levelMark l *
        (parentThetaAt N (rootQ N n root tau p) (g.val+1)
            (levelOccurrence l).current +
         (physicalDefectAt N (rootQ N n root tau p) (g.val+1)
            (levelOccurrence l).current +
          childThetaAt N (rootQ N n root tau p) (g.val+1)
            (levelOccurrence l).current))) =
    (∑ l ∈ retainedLevel N n root tau p g,
      levelMark l *
        (iteratedRequest (g.val+1) (levelOccurrence l).current -
         iteratedRequest g.val
           (nextRequest (levelOccurrence l).current
             (.retained (actualRetainedCell N n root tau p g l))))) := by
  apply Finset.sum_congr rfl
  intro l hl
  exact congrArg (fun x : ℝ => levelMark l * x)
    (selected_retention_total_gap N (rootQ N n root tau p) g.val
      (levelOccurrence l).current (actualRetainedCell N n root tau p g l)
      (retained_level_actual_cell_selected N n root tau p g l hl))

/-- The one-sided bill retains the exact same chosen cell and Fin-list
multiplicity, with max taken AFTER the signed physical cancellation. -/
theorem actual_retained_level_unpaid_exact
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    (∑ l ∈ retainedLevel N n root tau p g,
      levelMark l *
        combinedPhysicalUnpaid N (rootQ N n root tau p)
          (g.val+1) (levelOccurrence l).current) =
    (∑ l ∈ retainedLevel N n root tau p g,
      levelMark l *
        max 0 (iteratedRequest (g.val+1) (levelOccurrence l).current -
          iteratedRequest g.val
            (nextRequest (levelOccurrence l).current
              (.retained (actualRetainedCell N n root tau p g l))))) := by
  apply Finset.sum_congr rfl
  intro l hl
  exact congrArg (fun x : ℝ => levelMark l * x)
    (selected_retention_combined_unpaid N (rootQ N n root tau p) g.val
      (levelOccurrence l).current (actualRetainedCell N n root tau p g l)
      (retained_level_actual_cell_selected N n root tau p g l hl))

end
end ImbalancedChen.Part5OriginalH430ActualNetDefect
