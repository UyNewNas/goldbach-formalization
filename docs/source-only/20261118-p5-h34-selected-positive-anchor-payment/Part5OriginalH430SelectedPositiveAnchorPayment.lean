import ImbalancedChen.Part5OriginalH430ExplicitAnchorDefect

/-!
P5.6 / h34: pay fixed-reference slack at the ORIGINAL selected 106-bank
action, instead of charging every winning action the largest defect from
all 82 available original anchor appearances.

At a W1 winner the candidate allowance is the positive part of the
ONE genuine W1 anchor deficit. At a W2 winner it is 4/5 of the first
genuine positive endpoint deficit plus 1/5 of the second. This keeps
the original specified-cell reading, true Q80 predecessor table,
selected Fin occurrences, marks and same-Q physical Theta.

The payment is nonnegative without predecessor CLOSED-CELL. It bounds
the old fixed slack without an arbitrary supplied delta, and is no
larger than the earlier 82-anchor uniform-max payment. Hence the frozen
root gets a genuinely finer finite payment ledger, but NO smallness
bound for this ledger is asserted.

Source-only, UNCOMPILED, UNEVALUATED, FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430SelectedPositiveAnchorPayment

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430FixedReadDictionary
open Part5OriginalH430ActualFixedClosedCell
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger
open Part5OriginalH430TrueBankFeedbackFloorCredit
open Part5OriginalH430ClosedCellIdealSplit
open Part5OriginalH430FixedAnchorSlackPayment
open Part5OriginalH430ExplicitAnchorDefect

/-- Per-action nonnegative finite allowance at the original Q80
predecessor table. Only the actual W1 endpoint or W2 pair selected
by this action is charged; W2 retains the literal 4:1 mixture. -/
def actionPositiveAnchorAllowance (g : Fin 430) (F : ℝ → ℝ) :
    Original106Action → ℝ
  | .inl ij =>
      max 0 (F (W1Anchor ij.2) -
        floorValue (precedingH g) (w1Cell ij.2))
  | .inr j =>
      (4 * max 0 (F (originalW2At j).s0 -
          floorValue (precedingH g) (w2Cell j true)) +
        max 0 (F (originalW2At j).phi1 -
          floorValue (precedingH g) (w2Cell j false))) / 5

/-- No predecessor majorant hypothesis is needed for positivity. -/
theorem actionPositiveAnchorAllowance_nonneg
    (g : Fin 430) (a : Original106Action) (F : ℝ → ℝ) :
    0 ≤ actionPositiveAnchorAllowance g F a := by
  rcases a with ⟨i, j⟩ | j
  · change 0 ≤ max 0 (F (W1Anchor j) -
        floorValue (precedingH g) (w1Cell j))
    exact le_max_left _ _
  · change 0 ≤
      (4 * max 0 (F (originalW2At j).s0 -
          floorValue (precedingH g) (w2Cell j true)) +
        max 0 (F (originalW2At j).phi1 -
          floorValue (precedingH g) (w2Cell j false))) / 5
    positivity

/-- The genuine original fixed-read slack is no larger than the
action's original clipped endpoint deficits. For W2 this uses the
precise convex 4:1 weights, NOT a doubled absolute error. -/
theorem fixedReadSlack_le_actionPositiveAnchorAllowance
    (g : Fin 430) (a : Original106Action) (F : ℝ → ℝ) :
    fixedReadSlack g a F ≤ actionPositiveAnchorAllowance g F a := by
  rcases a with ⟨i, j⟩ | j
  · change F (W1Anchor j) -
        floorValue (precedingH g) (w1Cell j) ≤
        max 0 (F (W1Anchor j) -
          floorValue (precedingH g) (w1Cell j))
    exact le_max_right _ _
  · have h0 :
        F (originalW2At j).s0 -
          floorValue (precedingH g) (w2Cell j true) ≤
        max 0 (F (originalW2At j).s0 -
          floorValue (precedingH g) (w2Cell j true)) :=
      le_max_right _ _
    have h1 :
        F (originalW2At j).phi1 -
          floorValue (precedingH g) (w2Cell j false) ≤
        max 0 (F (originalW2At j).phi1 -
          floorValue (precedingH g) (w2Cell j false)) :=
      le_max_right _ _
    change
      (4 * F (originalW2At j).s0 +
        F (originalW2At j).phi1) / 5 -
      (4 * floorValue (precedingH g) (w2Cell j true) +
        floorValue (precedingH g) (w2Cell j false)) / 5 ≤
      (4 * max 0 (F (originalW2At j).s0 -
          floorValue (precedingH g) (w2Cell j true)) +
        max 0 (F (originalW2At j).phi1 -
          floorValue (precedingH g) (w2Cell j false))) / 5
    linarith only [h0, h1]

/-- Every per-action clipped allowance is at most the concrete
82-anchor uniform maximum from the previous packet. -/
theorem actionPositiveAnchorAllowance_le_actualAnchorDefect
    (g : Fin 430) (a : Original106Action) (F : ℝ → ℝ) :
    actionPositiveAnchorAllowance g F a ≤ actualAnchorDefect g F := by
  have hd := actualAnchorDefect_nonneg g F
  have hu := actualAnchorDefect_supplies_upper g F
  rcases a with ⟨i, j⟩ | j
  · change max 0 (F (W1Anchor j) -
        floorValue (precedingH g) (w1Cell j)) ≤
        actualAnchorDefect g F
    exact max_le hd (hu.1 j)
  · have h0 : max 0 (F (originalW2At j).s0 -
        floorValue (precedingH g) (w2Cell j true)) ≤
        actualAnchorDefect g F :=
      max_le hd (hu.2 j).1
    have h1 : max 0 (F (originalW2At j).phi1 -
        floorValue (precedingH g) (w2Cell j false)) ≤
        actualAnchorDefect g F :=
      max_le hd (hu.2 j).2
    change
      (4 * max 0 (F (originalW2At j).s0 -
          floorValue (precedingH g) (w2Cell j true)) +
        max 0 (F (originalW2At j).phi1 -
          floorValue (precedingH g) (w2Cell j false))) / 5 ≤
      actualAnchorDefect g F
    linarith only [h0, h1]

/-- Actual selected bank action/Fin-occurrence payment, preserving
the full original positive occurrenceScale, NOT summing all 106
potential actions at each position. -/
def bankSelectedPositiveAnchorPayment
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      occurrenceScale N n root tau p g l *
        actionPositiveAnchorAllowance g F a

theorem bankSelectedPositiveAnchorPayment_nonneg
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    0 ≤ bankSelectedPositiveAnchorPayment N n root tau p g F := by
  unfold bankSelectedPositiveAnchorPayment
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro l _
  exact mul_nonneg
    (occurrenceScale_nonneg N n root tau p g l
      hN ht ht' hn hp hband)
    (actionPositiveAnchorAllowance_nonneg g a F)

/-- The original exact fixed slack is paid actionwise by positive
endpoint deficits, with no global anchor-bound hypothesis. -/
theorem bankFixedSlackMass_le_selectedPositiveAnchorPayment
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    bankFixedSlackMass N n root tau p g F ≤
      bankSelectedPositiveAnchorPayment N n root tau p g F := by
  unfold bankFixedSlackMass bankSelectedPositiveAnchorPayment
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro l _
  have hs := occurrenceScale_nonneg N n root tau p g l
    hN ht ht' hn hp hband
  have hpnt := mul_le_mul_of_nonneg_left
    (fixedReadSlack_le_actionPositiveAnchorAllowance g a F) hs
  calc
    levelMark l * (occurrenceTheta N n root tau p g l *
        fixedReadSlack g a F) =
      occurrenceScale N n root tau p g l *
        fixedReadSlack g a F := by
          simp only [occurrenceScale, mul_assoc]
    _ ≤ occurrenceScale N n root tau p g l *
          actionPositiveAnchorAllowance g F a := hpnt

/-- Finer than the previous 82-anchor maximum times all selected
Theta; no endpoint absent from the winning action is charged. -/
theorem bankSelectedPositiveAnchorPayment_le_uniformDefect
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    bankSelectedPositiveAnchorPayment N n root tau p g F ≤
      actualAnchorDefect g F *
        bankSelectedTheta N n root tau p g := by
  unfold bankSelectedPositiveAnchorPayment bankSelectedTheta levelTheta
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l _
  have hs := occurrenceScale_nonneg N n root tau p g l
    hN ht ht' hn hp hband
  have hpnt := mul_le_mul_of_nonneg_left
    (actionPositiveAnchorAllowance_le_actualAnchorDefect g a F) hs
  calc
    occurrenceScale N n root tau p g l *
        actionPositiveAnchorAllowance g F a ≤
      occurrenceScale N n root tau p g l *
        actualAnchorDefect g F := hpnt
    _ = actualAnchorDefect g F *
        (levelMark l *
          thetaAtom N (rootQ N n root tau p)
            (parentProduct (levelOccurrence l).current.old)) := by
          dsimp [occurrenceScale, occurrenceTheta]
          ring

/-- One true frozen 430-root consumer with the new selected-action
finite payment. CLOSED-CELL is not discharged here, and no bound on
the computed Q80 anchor discrepancies is assumed. -/
theorem frozen_root_le_selectedPositiveAnchorPayment
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hclosed : ∀ g : Fin 430, ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s) :
    weightedRequest N (rootQ N n root tau p) 430
        (rootRequest N n root tau p) +
      (∑ g : Fin 430, bankFeedbackFloorCredit N n root tau p g) ≤
      (∑ l : LevelIndex N n root tau p 0,
        levelMark l *
          max 0 (weightedRequest N (rootQ N n root tau p) 0
            (levelOccurrence l).current)) +
      ∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          (bankBaseIdealPositive N n root tau p g +
            bankSelectedPositiveAnchorPayment N n root tau p g F) +
          bankPhysicalAppliedAbs N n root tau p g) := by
  have hroot := frozen_root_le_ideal_balance_plus_fixed_slack
    N n root tau p F hN ht ht' hn hp hband hclosed
  have hlevels :
      (∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          (bankBaseIdealPositive N n root tau p g +
            bankFixedSlackMass N n root tau p g F) +
          bankPhysicalAppliedAbs N n root tau p g)) ≤
      ∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          (bankBaseIdealPositive N n root tau p g +
            bankSelectedPositiveAnchorPayment N n root tau p g F) +
          bankPhysicalAppliedAbs N n root tau p g) := by
    apply Finset.sum_le_sum
    intro g _
    have hpnt := bankFixedSlackMass_le_selectedPositiveAnchorPayment
      N n root tau p g F hN ht ht' hn hp hband
    linarith only [hpnt]
  exact hroot.trans (add_le_add_left hlevels _)

end
end ImbalancedChen.Part5OriginalH430SelectedPositiveAnchorPayment
