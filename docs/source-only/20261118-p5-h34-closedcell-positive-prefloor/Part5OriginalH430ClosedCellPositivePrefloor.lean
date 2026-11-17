import ImbalancedChen.Part5OriginalH430TrueBankFeedbackFloorCredit
import ImbalancedChen.Part5OriginalH430ActualFixedClosedCell

/-!
P5.6 → h34. TRUE selected 106-bank positive pre-floor debt, transferred
to the ORIGINAL closed-cell predecessor reference, not a scalar owner.

The last packet identified a capped, exact Euclidean feedback-floor credit
but left its pre-floor positive surplus unpaid. This packet transfers that
POSITIVE surplus pointwise through the original W1 anchor / W2 4:1 fixed
read bound. It does not assume that a signed total controls positive parts.

The only additional hypothesis is the explicit preceding-generation
CLOSED-CELL bound at the original query cells. That predecessor induction
is still MANUSCRIPT-INTERNAL and NOT proved here. In particular, no h34
count-source, PP/same-rho, arithmetic owner, or numeric budget is assumed.

The clipped feedback-floor credit is also bounded ABOVE by the older
actual per-product quotient/remainder envelope (not by a one-floor-per-
action simplification). All summands keep actual Fin occurrence positions.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ClosedCellPositivePrefloor
noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ActualFixedClosedCell
open Part5OriginalH430ActualFeedbackQuotientRemainders
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger
open Part5OriginalH430LiteralBankQ80PhysicalExcess
open Part5OriginalH430TrueBankFeedbackFloorCredit

/-- Actual selected position's pre-floor candidate, replacing ONLY
the old table's fixed read by its original W1/W2 evaluation of F.
The ideal feedback, true same-Q Theta and ideal profile remain literal. -/
def closedCellPreFloorAtom (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (a : Original106Action)
    (l : Index N n root tau p g) (F : ℝ → ℝ) : ℝ :=
  occurrenceTheta N n root tau p g l *
      (baseValue a + fixedReference F a +
        idealFeedbackValue (iterate g.val) a) -
    occurrenceTheta N n root tau p g l *
      idealCellProfile (precedingH g) (precedingh g) a

/-- One occurrence for each *winning* bank action and genuine historical
Fin position. No quotient by product, q/tag or common catalog labels. -/
def bankClosedCellPreFloorExcess (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (F : ℝ → ℝ) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      levelMark l * max 0
        (closedCellPreFloorAtom N n root tau p g a l F)

/-- The exact original fixed-read closed-cell estimate transfers to
the PHYSICAL pre-floor gap before positive parts are taken. No
signed cancellation or scalar-owner replacement is used. -/
theorem preFloorAtom_le_closedCellPreFloorAtom
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (a : Original106Action)
    (l : Index N n root tau p g) (F : ℝ → ℝ)
    (htheta : 0 ≤ occurrenceTheta N n root tau p g l)
    (hcells : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s) :
    preFloorAtom N n root tau p g a l ≤
      closedCellPreFloorAtom N n root tau p g a l F := by
  have hfixed := selected_fixed_reference_upper g F hcells a
  have hcandidate :
      baseValue a + fixedValue (iterate g.val true) a +
          idealFeedbackValue (iterate g.val) a ≤
        baseValue a + fixedReference F a +
          idealFeedbackValue (iterate g.val) a := by
    linarith only [hfixed]
  have hscale := mul_le_mul_of_nonneg_left hcandidate htheta
  simpa only [preFloorAtom, closedCellPreFloorAtom] using
    (sub_le_sub_right hscale
      (occurrenceTheta N n root tau p g l *
        idealCellProfile (precedingH g) (precedingh g) a))

/-- This is a pointwise-positive bound at ORIGINAL selected Fin positions,
not the older signed closed-cell sum. The predecessor bound is explicit,
so it cannot be mistaken for a completed CLOSED-CELL induction. -/
theorem bank_prefloor_le_closed_cell_positive
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hcells : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s) :
    bankPreFloorIdealExcess N n root tau p g ≤
      bankClosedCellPreFloorExcess N n root tau p g F := by
  unfold bankPreFloorIdealExcess bankClosedCellPreFloorExcess
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro l _
  have hw := (rootHistory_support (by omega : 1 < N)
    ht ht' hn hp hband (levelOccurrence_source l).1).1
  have htheta : 0 ≤ occurrenceTheta N n root tau p g l := by
    exact thetaAtom_nonneg hN hw.2.1 (parentWindow_logs hw).2.1
  have hpoint := preFloorAtom_le_closedCellPreFloorAtom
    N n root tau p g a l F htheta hcells
  have hpositive :
      max 0 (preFloorAtom N n root tau p g a l) ≤
        max 0 (closedCellPreFloorAtom N n root tau p g a l F) := by
    apply max_le
    · exact le_max_left _ _
    · exact hpoint.trans (le_max_right _ _)
  exact mul_le_mul_of_nonneg_left hpositive (mark_pos _).le

/-- The genuine Q80 bank excess and its clipped feedback credit are
bounded by the ACTUAL preceding closed-cell pre-floor envelope. Neither
the old fixed reference nor the ideal feedback is declared paid. -/
theorem bank_literal_plus_credit_le_closed_cell
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hcells : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s) :
    bankLiteralQ80IdealExcess N n root tau p g +
        bankFeedbackFloorCredit N n root tau p g ≤
      bankClosedCellPreFloorExcess N n root tau p g F := by
  have hfloor := bank_literal_excess_plus_floor_credit_le_prefloor
    N n root tau p g hN ht ht' hn hp hband
  have hfixed := bank_prefloor_le_closed_cell_positive
    N n root tau p g F hN ht ht' hn hp hband hcells
  exact le_trans hfloor hfixed

/-- A clipped floor credit cannot exceed the REAL per-product
feedback rounding loss on the same selected 106-bank positions.
This is the needed anti-over-credit direction. -/
theorem bank_credit_le_original_rounding
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    bankFeedbackFloorCredit N n root tau p g ≤
      selectedBankRoundingLoss N n root tau p g := by
  unfold bankFeedbackFloorCredit selectedBankRoundingLoss
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro l _
  have hmin :
      min (max 0 (preFloorAtom N n root tau p g a l))
          (floorAtom N n root tau p g a l) ≤
        floorAtom N n root tau p g a l :=
    min_le_right _ _
  have hmark :=
    mul_le_mul_of_nonneg_left hmin (mark_pos _).le
  simpa only [floorAtom, occurrenceScale, mul_assoc] using hmark

/-- The cap also respects the ORIGINAL integer-product count, row
divisor and 2^80 scale via the previously constructed real remainder
envelope. It never assumes only one floor per winning action. -/
theorem bank_credit_le_original_product_envelope
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    bankFeedbackFloorCredit N n root tau p g ≤
      selectedBankRoundingEnvelope N n root tau p g := by
  exact (bank_credit_le_original_rounding N n root tau p g).trans
    (selected_bank_rounding_le_envelope N n root tau p g
      hN ht ht' hn hp hband)

/-- A TRUE 430-level upper bound on total eligible floor credit:
generation-zero seed is not a rounding generation, and repeated
positions are counted exactly as often as the actual producer paid. -/
theorem frozen_430_credit_le_product_envelopes
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    (∑ g : Fin 430, bankFeedbackFloorCredit N n root tau p g) ≤
      ∑ g : Fin 430, selectedBankRoundingEnvelope N n root tau p g := by
  apply Finset.sum_le_sum
  intro g _
  exact bank_credit_le_original_product_envelope
    N n root tau p g hN ht ht' hn hp hband

/-- Global source bound WITH the clipped credit still on the LEFT,
and the TRUE previous-generation closed-cell obligation made explicit.
This is not a proof of that induction nor of original U3/U4 counts.
No h34-equivalent hypothesis is introduced. -/
theorem frozen_root_le_closed_cell_positive_with_credit
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
          bankClosedCellPreFloorExcess N n root tau p g F +
            bankPhysicalAppliedAbs N n root tau p g) := by
  have hroot := frozen_root_le_prefloor_with_actual_feedback_credit
    N n root tau p hN ht ht' hn hp hband
  have hlevels :
      (∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          bankPreFloorIdealExcess N n root tau p g +
            bankPhysicalAppliedAbs N n root tau p g)) ≤
      ∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          bankClosedCellPreFloorExcess N n root tau p g F +
            bankPhysicalAppliedAbs N n root tau p g) := by
    apply Finset.sum_le_sum
    intro g _
    have hpositive := bank_prefloor_le_closed_cell_positive
      N n root tau p g F hN ht ht' hn hp hband (hclosed g)
    linarith only [hpositive]
  linarith only [hroot, hlevels]

end
end ImbalancedChen.Part5OriginalH430ClosedCellPositivePrefloor
