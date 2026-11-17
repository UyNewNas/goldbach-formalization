import ImbalancedChen.Part5OriginalH430ClosedCellPositivePrefloor
import ImbalancedChen.Part5OriginalH430FixedReadRows

/-!
P5.6 → h34. Split the ACTUAL positive CLOSED-CELL selected-bank
pre-floor gap into the fixed-cell predecessor slack and the unrounded
same-Q analytic base/feedback/dynamic-ideal balance.

The preceding CLOSED-CELL bound controls the old fixed read from ABOVE
but does not itself pay the positive gap caused by replacing that read
with F. In fact it makes the fixed-reference slack NONNEGATIVE and
therefore a genuine additional positive-debt channel. This packet
proves both directions of the exact positive-part sandwich and
transfers the upper direction to actual winning Fin positions and
the existing frozen 430-root consumer. The lower direction prevents
treating closed-cell substitution as a free cancellation.

Only the ORIGINAL 70 W1 anchors and 36 W2 4:1 fixed mixtures are used
via fixedReference/fixedValue. The dynamic ideal is the old literal
cellReadIdeal integral component with NO modified weights or same-Q.

No base/seed/PP/owner/numeric payment is assumed. The predecessor
CLOSED-CELL hypothesis stays explicit and unproved. Source-only,
UNCOMPILED / UNEVALUATED. Full manuscript-internal h34 remains OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ClosedCellIdealSplit

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430FixedReadDictionary
open Part5OriginalH430FixedReadRows
open Part5OriginalH430SelectedFixedReadSupply
open Part5OriginalH430ImmutableBankProfiles
open Part5OriginalH430ActualFixedClosedCell
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger
open Part5OriginalH430TrueBankFeedbackFloorCredit
open Part5OriginalH430ClosedCellPositivePrefloor

/-- The original ideal row's genuine non-fixed (prime-integral) part.
Its coefficients are the pinned dynamicIdeal, not a new analytic
profile, and both original upper/lower old arrays remain visible. -/
def dynamicIdealProfile (H h : Fin 200 → ℤ) (a : Original106Action) : ℝ :=
  ∑ b : RowAtom, dynamicIdeal a b * oldAtomValue H h b

/-- Coefficientwise decomposition of the EXISTING specified-cell ideal
row. This identity is valid for signed old arrays and all 106 actions;
it never identifies a specified-cell read with a scalar lookup. -/
theorem idealCellProfile_fixed_dynamic (H h : Fin 200 → ℤ)
    (a : Original106Action) :
    idealCellProfile H h a =
      fixedValue H a + dynamicIdealProfile H h a := by
  calc
    idealCellProfile H h a =
        ∑ b : RowAtom,
          (readFixed 1 a b + dynamicIdeal a b) * oldAtomValue H h b := by
          simp only [idealCellProfile, cellReadIdeal_split]
    _ = (∑ b : RowAtom, readFixed 1 a b * oldAtomValue H h b) +
        ∑ b : RowAtom, dynamicIdeal a b * oldAtomValue H h b := by
          simp only [add_mul, Finset.sum_add_distrib]
    _ = fixedValue H a + dynamicIdealProfile H h a := by
          rw [readFixed_value]
          simp only [one_mul, dynamicIdealProfile]

/-- The only part not involving the predecessor fixed table read:
literal base, original unrounded feedback, and true dynamic same-Q
ideal applied to the actual preceding arrays. -/
def unroundedIdealBalance (g : Fin 430) (a : Original106Action) : ℝ :=
  baseValue a + idealFeedbackValue (iterate g.val) a -
    dynamicIdealProfile (precedingH g) (precedingh g) a

/-- The exact difference between the W1/W2 fixed reference of F and
the ORIGINAL old upper specified-cell producer. -/
def fixedReadSlack (g : Fin 430) (a : Original106Action)
    (F : ℝ → ℝ) : ℝ :=
  fixedReference F a - fixedValue (precedingH g) a

/-- The predecessor CLOSED-CELL premise implies a nonnegative *slack*,
not its disappearance. This remains a manuscript-internal induction
premise, not an assumed counting target. -/
theorem fixedReadSlack_nonneg (g : Fin 430) (a : Original106Action)
    (F : ℝ → ℝ)
    (hcells : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s) :
    0 ≤ fixedReadSlack g a F := by
  unfold fixedReadSlack
  exact sub_nonneg.mpr (selected_fixed_reference_upper g F hcells a)

/-- A literal signed identity, BEFORE positive-part clipping, at every
true selected bank position. No analytic small-error claim is used. -/
theorem closedCellPreFloorAtom_exact_split
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (a : Original106Action)
    (l : Index N n root tau p g) (F : ℝ → ℝ) :
    closedCellPreFloorAtom N n root tau p g a l F =
      occurrenceTheta N n root tau p g l *
        (unroundedIdealBalance g a + fixedReadSlack g a F) := by
  simp only [closedCellPreFloorAtom, unroundedIdealBalance,
    fixedReadSlack, idealCellProfile_fixed_dynamic, precedingH]
  ring

/-- Genuine positive-part sandwich. The LOWER inequality is important:
given the predecessor cells and true nonnegative theta, replacing the
fixed read with F cannot lower the positive ideal-balance debt. The
UPPER inequality retains exactly the separately unpaid fixed slack. -/
theorem closedCellPreFloorAtom_positive_sandwich
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (a : Original106Action)
    (l : Index N n root tau p g) (F : ℝ → ℝ)
    (htheta : 0 ≤ occurrenceTheta N n root tau p g l)
    (hcells : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s) :
    max 0 (occurrenceTheta N n root tau p g l *
      unroundedIdealBalance g a) ≤
      max 0 (closedCellPreFloorAtom N n root tau p g a l F) ∧
    max 0 (closedCellPreFloorAtom N n root tau p g a l F) ≤
      max 0 (occurrenceTheta N n root tau p g l *
        unroundedIdealBalance g a) +
      occurrenceTheta N n root tau p g l * fixedReadSlack g a F := by
  let x : ℝ := occurrenceTheta N n root tau p g l *
    unroundedIdealBalance g a
  let y : ℝ := occurrenceTheta N n root tau p g l * fixedReadSlack g a F
  have hy : 0 ≤ y :=
    mul_nonneg htheta (fixedReadSlack_nonneg g a F hcells)
  have hgap : closedCellPreFloorAtom N n root tau p g a l F = x + y := by
    rw [closedCellPreFloorAtom_exact_split]
    dsimp [x, y]
    ring
  rw [hgap]
  constructor
  · apply max_le
    · exact le_max_left _ _
    · exact (le_add_of_nonneg_right hy).trans (le_max_right _ _)
  · apply max_le
    · exact (le_max_left _ _).trans (le_add_of_nonneg_right hy)
    · have hx : x ≤ max 0 x := le_max_right _ _
      linarith only [hx]

/-- Positive old dynamic/base/feedback imbalance at all genuinely
winning 106-bank Fin positions, keeping original occurrence marks. -/
def bankBaseIdealPositive
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      levelMark l *
        max 0 (occurrenceTheta N n root tau p g l *
          unroundedIdealBalance g a)

/-- All fixed-reference slack, counted ONCE per true selected action
occurrence with the actual same-Q theta and original history mark.
This is a cost, not an available discount or a signed cancellation. -/
def bankFixedSlackMass
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      levelMark l *
        (occurrenceTheta N n root tau p g l * fixedReadSlack g a F)

/-- Reuse the existing admission/window chain on an actual Fin index.
The root-specific physical Q and theta normalization are unchanged. -/
private theorem true_occurrenceTheta_nonneg
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (l : Index N n root tau p g)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    0 ≤ occurrenceTheta N n root tau p g l := by
  have hw := (rootHistory_support (by omega : 1 < N)
    ht ht' hn hp hband (levelOccurrence_source l).1).1
  exact thetaAtom_nonneg hN hw.2.1 (parentWindow_logs hw).2.1

/-- TRUE Fin-position selected-bank positive debt is sandwiched
between the genuine dynamic ideal-balance positive debt and that
positive debt PLUS the exact original fixed-cell slack. No cell
renaming, absent bank action or repeated path is discarded. -/
theorem bank_closed_cell_positive_sandwich
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hcells : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s) :
    bankBaseIdealPositive N n root tau p g ≤
      bankClosedCellPreFloorExcess N n root tau p g F ∧
    bankClosedCellPreFloorExcess N n root tau p g F ≤
      bankBaseIdealPositive N n root tau p g +
        bankFixedSlackMass N n root tau p g F := by
  constructor
  · unfold bankBaseIdealPositive bankClosedCellPreFloorExcess
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro l _
    have htheta := true_occurrenceTheta_nonneg N n root tau p g l
      hN ht ht' hn hp hband
    have hpnt := closedCellPreFloorAtom_positive_sandwich
      N n root tau p g a l F htheta hcells
    exact mul_le_mul_of_nonneg_left hpnt.1 (mark_pos _).le
  · unfold bankBaseIdealPositive bankClosedCellPreFloorExcess bankFixedSlackMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro l _
    have htheta := true_occurrenceTheta_nonneg N n root tau p g l
      hN ht ht' hn hp hband
    have hpnt := closedCellPreFloorAtom_positive_sandwich
      N n root tau p g a l F htheta hcells
    have hweighted := mul_le_mul_of_nonneg_left hpnt.2 (mark_pos _).le
    simpa only [mul_add] using hweighted

/-- Fixed-read slack is genuinely nonnegative at every true weighted
selected-bank occurrence when the predecessor cells are closed. -/
theorem bank_fixed_slack_nonneg
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hcells : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s) :
    0 ≤ bankFixedSlackMass N n root tau p g F := by
  unfold bankFixedSlackMass
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro l _
  exact mul_nonneg (mark_pos _).le
    (mul_nonneg (true_occurrenceTheta_nonneg N n root tau p g l
      hN ht ht' hn hp hband) (fixedReadSlack_nonneg g a F hcells))

/-- A true 430-generation root consumer, with positive feedback-floor
credit STILL on the left. The selected-bank CLOSED-CELL term is now
bounded by two separate manuscript-internal debts: same-Q dynamic
ideal/base/feedback positive imbalance and the original fixed slack.
Neither is asserted small or paid. -/
theorem frozen_root_le_ideal_balance_plus_fixed_slack
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
            bankFixedSlackMass N n root tau p g F) +
          bankPhysicalAppliedAbs N n root tau p g) := by
  have hroot := frozen_root_le_closed_cell_positive_with_credit
    N n root tau p F hN ht ht' hn hp hband hclosed
  have hlevels :
      (∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          bankClosedCellPreFloorExcess N n root tau p g F +
          bankPhysicalAppliedAbs N n root tau p g)) ≤
      ∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          (bankBaseIdealPositive N n root tau p g +
            bankFixedSlackMass N n root tau p g F) +
          bankPhysicalAppliedAbs N n root tau p g) := by
    apply Finset.sum_le_sum
    intro g _
    have hsplit := (bank_closed_cell_positive_sandwich
      N n root tau p g F hN ht ht' hn hp hband (hclosed g)).2
    linarith only [hsplit]
  exact hroot.trans (add_le_add_left hlevels _)

end
end ImbalancedChen.Part5OriginalH430ClosedCellIdealSplit
