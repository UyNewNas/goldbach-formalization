import ImbalancedChen.Part5OriginalH430ActualNonretainedNetDebt
import ImbalancedChen.Part5OriginalH430RequestedCandidateLevel

/-!
P5.6 / h34: replace the remaining ACTUAL Buchstab and winning-106-bank
positive request debts by their literal old-table Q80 numerators or the
already proved original bank candidate upper bound.

This does NOT estimate the resulting surplus by Theta, identify it with
original U3/U4 counting, or license a CLOSED-CELL assertion. The right hand
side is a concrete still-unpaid manuscript-local arithmetic discrepancy.
No discarded bank row, independent retention fee, or quotient of repeated
Fin history positions is introduced.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualQ80CandidateSurplus
noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels
open P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430DecisionProvenance
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430ActualNetDefect
open Part5OriginalH430ActualNonretainedNetDebt

/-- Literal original Q80 Buchstab suffix minus the actual strict-prime
successor sum, at each selected cell and original physical root Q. -/
def buchstabQ80Surplus (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : ℝ :=
  ∑ l ∈ buchstabLevel N n root tau p g,
    levelMark l *
      max 0
        (((buchstabValue (iterate g.val) (levelOccurrence l).current.node.upper
            (actualBuchstabCell N n root tau p g l) : ℝ) / (2^80 : ℝ)) -
          ((singleChildren
              (.buchstab (levelOccurrence l).current.node.upper
                (levelOccurrence l).current.node.physical.argument)
              N (rootQ N n root tau p) (levelOccurrence l).current.old
              (levelOccurrence l).current.node.physical.ceiling).toList.map
            (fun q => iteratedRequest g.val
              (nextRequest (levelOccurrence l).current
                (.buchstab (levelOccurrence l).current.node.upper q)))).sum)

/-- The winning bank's LITERAL base/fixed/feedback expression bounds its
new Q80 read. The original actual bankEdges predecessor sum is not replaced
by an ideal row, and the max is taken only after subtraction. -/
def bankCandidateSurplus (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      levelMark l *
        max 0
          ((baseValue a + fixedValue (iterate g.val true) a +
              feedbackValue (iterate g.val) a) -
            ((bankEdges N (rootQ N n root tau p)
                (levelOccurrence l).current a).map
              (fun e => edgeWeight e *
                iteratedRequest g.val
                  (nextRequest (levelOccurrence l).current e))).sum)

/-- The ACTUAL selected Buchstab request is exactly the old integer
suffix / 2^80; no analytic prime-sum equality is assumed. -/
theorem selected_buchstab_q80_exact (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430)
    (l : Index N n root tau p g)
    (hl : l ∈ buchstabLevel N n root tau p g) :
    iteratedRequest (g.val+1) (levelOccurrence l).current =
      (buchstabValue (iterate g.val) (levelOccurrence l).current.node.upper
        (actualBuchstabCell N n root tau p g l) : ℝ) / (2^80 : ℝ) := by
  have hs := actual_buchstab_cell_selected N n root tau p g l hl
  simpa only [choiceValue] using (selected_value hs)

/-- This is an exact, not just upper, identification of the remaining
strict-prime debt with the original finite Q80 suffix discrepancy. -/
theorem buchstab_net_debt_eq_q80_surplus
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    buchstabNetDebt N n root tau p g =
      buchstabQ80Surplus N n root tau p g := by
  unfold buchstabNetDebt buchstabQ80Surplus
  apply Finset.sum_congr rfl
  intro l hl
  let r := (levelOccurrence l).current
  have hs := actual_buchstab_cell_selected N n root tau p g l hl
  have hdefect := selected_buchstab_combined_unpaid N
    (rootQ N n root tau p) g.val r
    (actualBuchstabCell N n root tau p g l) hs
  have hq := selected_buchstab_q80_exact N n root tau p g l hl
  rw [hdefect, hq]

/-- One-sided pointwise comparison with the ORIGINAL candidate. No
signed cancellation is used to bound the positive part. -/
theorem selected_bank_gap_le_candidate
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (a : Original106Action)
    (l : Index N n root tau p g)
    (hl : l ∈ selectedLevel N n root tau p g a) :
    combinedPhysicalUnpaid N (rootQ N n root tau p)
      (g.val+1) (levelOccurrence l).current ≤
      max 0
        ((baseValue a + fixedValue (iterate g.val true) a +
            feedbackValue (iterate g.val) a) -
          ((bankEdges N (rootQ N n root tau p)
              (levelOccurrence l).current a).map
            (fun e => edgeWeight e *
              iteratedRequest g.val
                (nextRequest (levelOccurrence l).current e))).sum) := by
  obtain ⟨i, hs⟩ := (Finset.mem_filter.mp hl).2
  let r := (levelOccurrence l).current
  let s : ℝ := ((bankEdges N (rootQ N n root tau p) r a).map
    (fun e => edgeWeight e * iteratedRequest g.val (nextRequest r e))).sum
  have hv : iteratedRequest (g.val+1) r ≤
      baseValue a + fixedValue (iterate g.val true) a +
        feedbackValue (iterate g.val) a := by
    simpa only [action_slot] using (selected_bank_candidate_upper hs)
  have hg : max 0 (iteratedRequest (g.val+1) r - s) ≤
      max 0 ((baseValue a + fixedValue (iterate g.val true) a +
        feedbackValue (iterate g.val) a) - s) := by
    apply max_le
    · exact le_max_left _ _
    · exact (sub_le_sub_right hv s).trans (le_max_right _ _)
  have hd := selected_bank_combined_unpaid N (rootQ N n root tau p)
    g.val r i (slotOfAction a) hs
  change combinedPhysicalUnpaid N (rootQ N n root tau p)
    (g.val+1) r ≤ max 0
      ((baseValue a + fixedValue (iterate g.val true) a +
        feedbackValue (iterate g.val) a) - s)
  rw [hd]
  simpa only [action_slot] using hg

/-- The original positive occurrence mark preserves the pointwise
one-sided direction. No unselected alternative is accumulated. -/
theorem bank_net_debt_le_candidate_surplus
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    bankNetDebt N n root tau p g ≤
      bankCandidateSurplus N n root tau p g := by
  unfold bankNetDebt bankCandidateSurplus
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro l hl
  exact mul_le_mul_of_nonneg_left
    (selected_bank_gap_le_candidate N n root tau p g a l hl)
    (mark_pos _).le

/-- Exact chosen-Buchstab suffix gap plus an explicit, still-unpaid
winning-bank candidate gap bounds the FULL nonretained level deficit. -/
theorem full_net_debt_le_actual_candidate_surpluses
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    fullNetDebt N n root tau p g ≤
      buchstabQ80Surplus N n root tau p g +
        bankCandidateSurplus N n root tau p g := by
  rw [full_net_debt_eq_nonretained, buchstab_net_debt_eq_q80_surplus]
  exact add_le_add_left (bank_net_debt_le_candidate_surplus N n root tau p g) _

/-- Do not turn the displayed 430-level total into an H430 payment:
these true Q80 surpluses have not been bounded by Theta/count. -/
theorem all_430_net_debt_le_actual_candidate_surpluses
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) :
    (∑ g : Fin 430, fullNetDebt N n root tau p g) ≤
      ∑ g : Fin 430,
        (buchstabQ80Surplus N n root tau p g +
          bankCandidateSurplus N n root tau p g) := by
  apply Finset.sum_le_sum
  intro g _
  exact full_net_debt_le_actual_candidate_surpluses N n root tau p g

end
end ImbalancedChen.Part5OriginalH430ActualQ80CandidateSurplus
