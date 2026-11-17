import ImbalancedChen.Part5OriginalH430ActualQ80CandidateSurplus
import ImbalancedChen.Part5OriginalH430ActualSelectedRowBudget

/-!
P5.6/h34: a one-sided, genuine selected-bank candidate-surplus comparison.

The previous Q80 packet left the winning bank's positive candidate-minus-RAW
predecessor gap unpaid. Here this gap is bounded by (i) the original winning
candidate's POSITIVE overshoot above the same-Q bank IDEAL, (ii) the already
supplied absolute selected-row applied error, and (iii) the absolute CHILD
Theta normalization drift. Crucially the last term is not silently erased:
the physical edgeValue is NOT the raw request tree's predecessor sum.

Every summation is over actual selected Fin history positions and their
original marks, never over all 106 unchosen offers. Retention stays free,
and no U3/U4 count owner or CLOSED-CELL base licence is assumed.
The existing bank epsilon*Theta payment is reused ONCE, not repaid.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430BankSurplusPhysicalSplit
noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels
open P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLocalBankSupply
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430PhysicalRequestDefectBridge
open Part5OriginalH430ActualQ80CandidateSurplus
open Part5OriginalH430ActualSelectedRowBudget

/-- The original chosen candidate's positive excess above its OLD physical
ideal at precisely the same root Q and same selected bank action. This
quantity is OPEN: no base/fixed/feedback versus ideal inequality is assumed. -/
def bankIdealOvershoot (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      levelMark l *
        max 0
          ((baseValue a + fixedValue (iterate g.val true) a +
              feedbackValue (iterate g.val) a) -
            thetaAtom N (rootQ N n root tau p)
              (parentProduct (levelOccurrence l).current.old) *
              idealCellProfile (precedingH g) (precedingh g) a)

/-- Literal unsigned child-Theta drift on actual winning 106-bank
positions. Never identify this physical correction with zero. -/
def bankChildThetaDriftAbs (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      levelMark l *
        |childThetaDrift N (rootQ N n root tau p)
          g.val (levelOccurrence l).current|

/-- One-sided finite-arithmetic fact. The two absolute errors cannot be
replaced by an absolute value of a signed sum. -/
private theorem positive_gap_le_ideal_error_drift
    (candidate ideal physical raw : ℝ) :
    max 0 (candidate - raw) ≤
      max 0 (candidate - ideal) +
        |physical - ideal| + |physical - raw| := by
  have h1 : candidate - ideal ≤ max 0 (candidate - ideal) :=
    le_max_right _ _
  have h2 : ideal - physical ≤ |physical - ideal| := by
    calc
      ideal - physical ≤ |ideal - physical| := le_abs_self _
      _ = |physical - ideal| := abs_sub_comm _ _
  have h3 : physical - raw ≤ |physical - raw| := le_abs_self _
  apply max_le
  · exact add_nonneg
      (add_nonneg (le_max_left _ _) (abs_nonneg _))
      (abs_nonneg _)
  · linarith only [h1, h2, h3]

/-- For a REAL selected bank slot, physical edgeValue minus the RAW
predecessor list is exactly the previously exposed child-Theta drift.
The proof uses the selected action, not a scalar default or an ideal row. -/
theorem selected_bank_physical_minus_raw_eq_child_drift
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (a : Original106Action)
    (l : Index N n root tau p g) (i : Fin 200)
    (hs : Selected g.val (levelOccurrence l).current i
      (.bank (slotOfAction a))) :
    edgeValue (rootQ N n root tau p) (iterate g.val)
        (levelOccurrence l).current
        (children N (rootQ N n root tau p) g.val
          (levelOccurrence l).current) -
      ((bankEdges N (rootQ N n root tau p)
        (levelOccurrence l).current a).map
          (fun e => edgeWeight e *
            iteratedRequest g.val
              (nextRequest (levelOccurrence l).current e))).sum =
      childThetaDrift N (rootQ N n root tau p) g.val
        (levelOccurrence l).current := by
  let r := (levelOccurrence l).current
  let Q := rootQ N n root tau p
  have hchildren : children N Q g.val r = bankEdges N Q r a := by
    simpa only [action_slot] using (children_eq_bank hs)
  have hphysical := physical_step_eq_raw_plus_drift N Q g.val r
  unfold actualStep at hphysical
  rw [hchildren] at hphysical
  change edgeValue Q (iterate g.val) r (bankEdges N Q r a) -
      ((bankEdges N Q r a).map
        (fun e => edgeWeight e *
          iteratedRequest g.val (nextRequest r e))).sum =
      childThetaDrift N Q g.val r
  linarith only [hphysical]

/-- For every chosen bank position, a pointwise positive gap is dominated
by a positive ORIGINAL ideal overshoot and two genuine absolute errors.
All request modes and exact Q80 bank candidates remain unchanged. -/
theorem selected_bank_candidate_gap_split
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (a : Original106Action)
    (l : Index N n root tau p g)
    (hl : l ∈ selectedLevel N n root tau p g a) :
    max 0
      ((baseValue a + fixedValue (iterate g.val true) a +
          feedbackValue (iterate g.val) a) -
        ((bankEdges N (rootQ N n root tau p)
            (levelOccurrence l).current a).map
          (fun e => edgeWeight e *
            iteratedRequest g.val
              (nextRequest (levelOccurrence l).current e))).sum) ≤
    max 0
      ((baseValue a + fixedValue (iterate g.val true) a +
          feedbackValue (iterate g.val) a) -
        thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) *
          idealCellProfile (precedingH g) (precedingh g) a) +
    |edgeValue (rootQ N n root tau p) (iterate g.val)
        (levelOccurrence l).current
        (children N (rootQ N n root tau p) g.val
          (levelOccurrence l).current) -
      thetaAtom N (rootQ N n root tau p)
        (parentProduct (levelOccurrence l).current.old) *
        idealCellProfile (precedingH g) (precedingh g) a| +
    |childThetaDrift N (rootQ N n root tau p)
        g.val (levelOccurrence l).current| := by
  obtain ⟨i, hs⟩ := (Finset.mem_filter.mp hl).2
  have h := positive_gap_le_ideal_error_drift
    (baseValue a + fixedValue (iterate g.val true) a +
      feedbackValue (iterate g.val) a)
    (thetaAtom N (rootQ N n root tau p)
      (parentProduct (levelOccurrence l).current.old) *
      idealCellProfile (precedingH g) (precedingh g) a)
    (edgeValue (rootQ N n root tau p) (iterate g.val)
      (levelOccurrence l).current
      (children N (rootQ N n root tau p) g.val
        (levelOccurrence l).current))
    (((bankEdges N (rootQ N n root tau p)
        (levelOccurrence l).current a).map
      (fun e => edgeWeight e *
        iteratedRequest g.val
          (nextRequest (levelOccurrence l).current e))).sum)
  rw [selected_bank_physical_minus_raw_eq_child_drift
    N n root tau p g a l i hs] at h
  exact h

/-- A real all-selected-Fin comparison. The old absolute bank row payment
is exactly levelAppliedError; no signed-row cancellation is used. -/
theorem bank_candidate_surplus_le_ideal_plus_applied_and_drift
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    bankCandidateSurplus N n root tau p g ≤
      bankIdealOvershoot N n root tau p g +
        actualBankAppliedError N n root tau p g +
          bankChildThetaDriftAbs N n root tau p g := by
  unfold bankCandidateSurplus bankIdealOvershoot
    actualBankAppliedError bankChildThetaDriftAbs levelAppliedError
  calc
    (∑ a : Original106Action,
      ∑ l ∈ selectedLevel N n root tau p g a,
        levelMark l *
          max 0
            ((baseValue a + fixedValue (iterate g.val true) a +
                feedbackValue (iterate g.val) a) -
              ((bankEdges N (rootQ N n root tau p)
                  (levelOccurrence l).current a).map
                (fun e => edgeWeight e *
                  iteratedRequest g.val
                    (nextRequest (levelOccurrence l).current e))).sum)) ≤
      ∑ a : Original106Action,
        ∑ l ∈ selectedLevel N n root tau p g a,
          levelMark l *
            (max 0
              ((baseValue a + fixedValue (iterate g.val true) a +
                  feedbackValue (iterate g.val) a) -
                thetaAtom N (rootQ N n root tau p)
                  (parentProduct (levelOccurrence l).current.old) *
                  idealCellProfile (precedingH g) (precedingh g) a) +
              |edgeValue (rootQ N n root tau p) (iterate g.val)
                  (levelOccurrence l).current
                  (children N (rootQ N n root tau p) g.val
                    (levelOccurrence l).current) -
                thetaAtom N (rootQ N n root tau p)
                  (parentProduct (levelOccurrence l).current.old) *
                  idealCellProfile (precedingH g) (precedingh g) a| +
              |childThetaDrift N (rootQ N n root tau p)
                  g.val (levelOccurrence l).current|) := by
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro l hl
        exact mul_le_mul_of_nonneg_left
          (selected_bank_candidate_gap_split N n root tau p g a l hl)
          (mark_pos _).le
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      ring

/-- The pinned ORIGINAL selected-bank absolute coefficient supplier pays
the applied-error term once, uniformly BEFORE N/root/precision/g. It does
NOT pay either ideal overshoot or child-Theta drift. -/
theorem uniform_bank_candidate_surplus_open_remainder
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N →
      ∀ n : ℕ, ∀ root : Root, ∀ tau : ℝ,
        0 ≤ tau → tau ≤ 1/12 →
        1/((n:ℝ)+1) ≤ 11/384 →
      ∀ p : ℕ, (p.Prime ∧ p.Coprime N) →
        physicalPrime N p ∈ rootBand root →
      ∀ g : Fin 430,
        bankCandidateSurplus N n root tau p g ≤
          bankIdealOvershoot N n root tau p g +
            epsilon * actualBankTheta N n root tau p g +
              bankChildThetaDriftAbs N n root tau p g := by
  obtain ⟨T, hT4, hT⟩ := uniform_actual_selected_error_row_budget he
  refine ⟨T, hT4, ?_⟩
  intro N hN n root tau ht ht' hn p hp hband g
  have hpaid :=
    (hT N hN n root tau ht ht' hn p hp hband g).2.1
  have hsplit :=
    bank_candidate_surplus_le_ideal_plus_applied_and_drift
      N n root tau p g
  linarith only [hpaid, hsplit]

end
end ImbalancedChen.Part5OriginalH430BankSurplusPhysicalSplit
