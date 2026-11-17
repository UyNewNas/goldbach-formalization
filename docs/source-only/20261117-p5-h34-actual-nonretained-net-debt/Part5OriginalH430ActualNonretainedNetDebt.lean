import ImbalancedChen.Part5OriginalH430RetainedZeroNetDefect

/-!
P5.6 / h34: isolate the genuine remaining one-sided request debt on the
ACTUAL 430-level selected request program, after the previously proved
selected-retention cancellation.

The original resolver, Fin 200 specified-cell read, strict-prime carrier,
all 106 bank slots, physical root Q, and original level occurrence marks
are preserved. Unresolved/exterior requests contribute zero: their new
read and selected child list are both zero.

This is an exact localization of positive physical request deficits to
Buchstab and bank. It does NOT prove that either deficit is small, that
their signed sums bound their positive parts, or that request values own
the original U3/U4 selected-count arithmetic source.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualNonretainedNetDebt
noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels
open P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430PhysicalRequestDefectBridge
open Part5OriginalH430ActualNetDefect
open Part5OriginalH430RetainedZeroNetDefect

/-- The actual g+1 list-position total, with original marks and the same
root Q. No history positions are identified by product or catalogue key. -/
def fullNetDebt (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : ℝ :=
  ∑ l : Index N n root tau p g,
    levelMark l *
      combinedPhysicalUnpaid N (rootQ N n root tau p)
        (g.val+1) (levelOccurrence l).current

/-- Only genuinely selected strict-prime Buchstab occurrences. -/
def buchstabNetDebt (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : ℝ :=
  ∑ l ∈ buchstabLevel N n root tau p g,
    levelMark l *
      combinedPhysicalUnpaid N (rootQ N n root tau p)
        (g.val+1) (levelOccurrence l).current

/-- Only the winning original 106-bank action at each actual Fin position.
The partition counts a position once, not once per candidate row. -/
def bankNetDebt (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      levelMark l *
        combinedPhysicalUnpaid N (rootQ N n root tau p)
          (g.val+1) (levelOccurrence l).current

/-- No exterior/unresolved positive physical debit. This must be
established separately from the fact that the exterior new read is zero:
the selected children are also empty. -/
theorem unresolved_net_defect_zero
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (l : Index N n root tau p g)
    (hl : l ∉ resolvedLevel N n root tau p g) :
    combinedPhysicalUnpaid N (rootQ N n root tau p)
      (g.val+1) (levelOccurrence l).current = 0 := by
  let r := (levelOccurrence l).current
  cases hr : resolve (g.val+1) r with
  | none =>
      have hc : children N (rootQ N n root tau p) g.val r = [] :=
        (exterior_children_empty hr).1
      have hv : iteratedRequest (g.val+1) r = 0 := by
        change requestValue (iterate (g.val+1)) r = 0
        exact resolve_none_value hr
      rw [combinedPhysicalUnpaid_eq_positiveDefect]
      simp [positiveDefect, localDefect, hc, hv, r]
  | some i =>
      have hm : l ∈ resolvedLevel N n root tau p g := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simp [actualChoice, hr, r]
      exact (hl hm).elim

/-- The entire actual g+1 level's unpaid positive part is precisely
Buchstab plus the winning bank source. Retention and exterior terms are
zero; no independent charge for parent/child Theta is reintroduced. -/
theorem full_net_debt_eq_nonretained
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    fullNetDebt N n root tau p g =
      buchstabNetDebt N n root tau p g +
        bankNetDebt N n root tau p g := by
  let Q := rootQ N n root tau p
  let F : Index N n root tau p g → ℝ := fun l =>
    levelMark l * combinedPhysicalUnpaid N Q (g.val+1)
      (levelOccurrence l).current
  have hresolved :
      (∑ l : Index N n root tau p g, F l) =
        ∑ l ∈ resolvedLevel N n root tau p g, F l := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : l ∈ resolvedLevel N n root tau p g
    · simp [hl]
    · have hz := unresolved_net_defect_zero N n root tau p g l hl
      simp [F, Q, hl, hz]
  change (∑ l : Index N n root tau p g, F l) =
    (∑ l ∈ buchstabLevel N n root tau p g, F l) +
      (∑ a : Original106Action,
        ∑ l ∈ selectedLevel N n root tau p g a, F l)
  calc
    _ = ∑ l ∈ resolvedLevel N n root tau p g, F l := hresolved
    _ = (∑ l ∈ retainedLevel N n root tau p g, F l) +
        (∑ l ∈ buchstabLevel N n root tau p g, F l) +
          (∑ a : Original106Action,
            ∑ l ∈ selectedLevel N n root tau p g a, F l) :=
        resolved_level_sum_all_actions N n root tau p g F
    _ = _ := by
      have hzero :=
        actual_retained_level_combined_unpaid_zero N n root tau p g
      change (∑ l ∈ retainedLevel N n root tau p g, F l) = 0 at hzero
      rw [hzero]
      ring

/-- The genuinely chosen Buchstab cell, never a scalar substitute. -/
def actualBuchstabCell (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (l : Index N n root tau p g) : Fin 200 :=
  (resolve (g.val+1) (levelOccurrence l).current).getD 0

theorem actual_buchstab_cell_selected
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (l : Index N n root tau p g)
    (hl : l ∈ buchstabLevel N n root tau p g) :
    Selected g.val (levelOccurrence l).current
      (actualBuchstabCell N n root tau p g l) .buchstab := by
  have hc : actualChoice N n root tau p g l = some .buchstab :=
    (Finset.mem_filter.mp hl).2
  obtain ⟨i, hs⟩ :=
    (actual_choice_iff_selected N n root tau p g l .buchstab).1 hc
  have hi : resolve (g.val+1) (levelOccurrence l).current = some i := hs.1
  simpa [actualBuchstabCell, hi] using hs

/-- Explicit genuine strict-prime predecessor gap, with every true q
successor and no substitution of a rounded integral for the integer sum. -/
theorem buchstab_net_debt_exact
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    buchstabNetDebt N n root tau p g =
      ∑ l ∈ buchstabLevel N n root tau p g,
        levelMark l *
          max 0 (iteratedRequest (g.val+1) (levelOccurrence l).current -
            (((singleChildren
                (.buchstab (levelOccurrence l).current.node.upper
                  (levelOccurrence l).current.node.physical.argument)
                N (rootQ N n root tau p) (levelOccurrence l).current.old
                (levelOccurrence l).current.node.physical.ceiling).toList.map
              (fun q => iteratedRequest g.val
                (nextRequest (levelOccurrence l).current
                  (.buchstab (levelOccurrence l).current.node.upper q)))).sum) := by
  unfold buchstabNetDebt
  apply Finset.sum_congr rfl
  intro l hl
  exact congrArg (fun x : ℝ => levelMark l * x)
    (selected_buchstab_combined_unpaid N (rootQ N n root tau p)
      g.val (levelOccurrence l).current
      (actualBuchstabCell N n root tau p g l)
      (actual_buchstab_cell_selected N n root tau p g l hl))

/-- Exactly the selected 106-bank row, not the sum of all bank offers. -/
theorem bank_net_debt_exact
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    bankNetDebt N n root tau p g =
      ∑ a : Original106Action,
        ∑ l ∈ selectedLevel N n root tau p g a,
          levelMark l *
            max 0 (iteratedRequest (g.val+1) (levelOccurrence l).current -
              ((bankEdges N (rootQ N n root tau p)
                (levelOccurrence l).current a).map
                  (fun e => edgeWeight e *
                    iteratedRequest g.val
                      (nextRequest (levelOccurrence l).current e))).sum) := by
  unfold bankNetDebt
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro l hl
  obtain ⟨i, hs⟩ := (Finset.mem_filter.mp hl).2
  have h := selected_bank_combined_unpaid N (rootQ N n root tau p)
    g.val (levelOccurrence l).current i (slotOfAction a) hs
  simpa only [action_slot] using
    congrArg (fun x : ℝ => levelMark l * x) h

theorem buchstab_net_debt_nonneg
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    0 ≤ buchstabNetDebt N n root tau p g := by
  unfold buchstabNetDebt
  apply Finset.sum_nonneg
  intro l _
  exact mul_nonneg (mark_pos _).le
    (combinedPhysicalUnpaid_nonneg N (rootQ N n root tau p)
      (g.val+1) (levelOccurrence l).current)

theorem bank_net_debt_nonneg
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    0 ≤ bankNetDebt N n root tau p g := by
  unfold bankNetDebt
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro l _
  exact mul_nonneg (mark_pos _).le
    (combinedPhysicalUnpaid_nonneg N (rootQ N n root tau p)
      (g.val+1) (levelOccurrence l).current)

/-- Across all 430 actual predecessor levels, the exact unpaid total
has NO retention or unresolved debt. This is not a common 430+11 count
refinement: each level still indexes its genuine history occurrences. -/
theorem all_430_net_debt_eq_nonretained
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) :
    (∑ g : Fin 430, fullNetDebt N n root tau p g) =
      ∑ g : Fin 430,
        (buchstabNetDebt N n root tau p g +
          bankNetDebt N n root tau p g) := by
  apply Finset.sum_congr rfl
  intro g _
  exact full_net_debt_eq_nonretained N n root tau p g

end
end ImbalancedChen.Part5OriginalH430ActualNonretainedNetDebt
