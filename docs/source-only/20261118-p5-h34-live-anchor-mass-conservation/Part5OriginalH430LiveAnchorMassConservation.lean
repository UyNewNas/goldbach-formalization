import ImbalancedChen.Part5OriginalH430LiveAnchorFloorCancellation

/-!
P5.6 / h34: under the ACTUAL predecessor CLOSED-CELL premise, the
previously clipped selected fixed-anchor liability is EXACTLY the
signed reference-minus-original-Q80-fixed-read amount.

The W1 endpoint and two W2 endpoints are each tested against their
own literal CLOSED query cell, not a scalar closed-min owner.
The old W2 fixed channel retains 4:1/5. Summation is over the
genuine selected Fin LIST occurrences with occurrenceScale.

We derive a finite conservation law (reference mass = current fixed
table mass + remaining positive anchor liability) and apply it to
the existing 430-root consumer with both integer rounding credits.
No quantitative smallness, complete CLOSED-CELL induction, seed
payment, U3/U4 count owner, PP/same-rho or h34 claim is assumed.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430LiveAnchorMassConservation

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open P2Selected430CausalOccurrenceExporter
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430FixedReadDictionary
open Part5OriginalH430ActualFixedClosedCell
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ClosedCellIdealSplit
open Part5OriginalH430SelectedPositiveAnchorPayment
open Part5OriginalH430LiveAnchorFloorCancellation

/-- At each original W1 or W2 endpoint, CLOSED-CELL removes the max(0,_)
without losing the raw previous-table value. This is stronger than merely
bounding the original fixed slack by positive-part allowances. -/
theorem action_positive_anchor_eq_actual_fixed_slack
    (g : Fin 430) (a : Original106Action) (F : ℝ → ℝ)
    (hcells : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i →
        floorValue (iterate g.val true) i ≤ F s) :
    actionPositiveAnchorAllowance g F a = fixedReadSlack g a F := by
  rcases a with ⟨i, j⟩ | j
  · have hp : 0 ≤ F (W1Anchor j) -
        floorValue (precedingH g) (w1Cell j) := by
      apply sub_nonneg.mpr
      simpa only [precedingH] using
        (hcells (w1Cell j) (W1Anchor j) (w1Cell_contains j))
    change max 0 (F (W1Anchor j) -
      floorValue (precedingH g) (w1Cell j)) =
        F (W1Anchor j) - floorValue (precedingH g) (w1Cell j)
    exact max_eq_right hp
  · have hm0 : (originalW2At j).s0 ∈ queryCell (w2Cell j true) := by
      simpa only [ite_true] using (w2Cell_contains j true)
    have hm1 : (originalW2At j).phi1 ∈ queryCell (w2Cell j false) := by
      simpa only [ite_false] using (w2Cell_contains j false)
    have hp0 : 0 ≤ F (originalW2At j).s0 -
        floorValue (precedingH g) (w2Cell j true) := by
      apply sub_nonneg.mpr
      simpa only [precedingH] using
        (hcells (w2Cell j true) (originalW2At j).s0 hm0)
    have hp1 : 0 ≤ F (originalW2At j).phi1 -
        floorValue (precedingH g) (w2Cell j false) := by
      apply sub_nonneg.mpr
      simpa only [precedingH] using
        (hcells (w2Cell j false) (originalW2At j).phi1 hm1)
    change (4 * max 0 (F (originalW2At j).s0 -
            floorValue (precedingH g) (w2Cell j true)) +
          max 0 (F (originalW2At j).phi1 -
            floorValue (precedingH g) (w2Cell j false))) / 5 =
        (4 * F (originalW2At j).s0 +
          F (originalW2At j).phi1) / 5 -
        (4 * floorValue (precedingH g) (w2Cell j true) +
          floorValue (precedingH g) (w2Cell j false)) / 5
    rw [max_eq_right hp0, max_eq_right hp1]
    ring

/-- No overpayment remains from taking positive parts on EACH actual
selected endpoint under CLOSED-CELL. This is equality of the full
marked, same-Q selected list, not just a global bound. -/
theorem selected_positive_anchor_eq_fixed_slack_mass
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ)
    (hcells : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i →
        floorValue (iterate g.val true) i ≤ F s) :
    bankSelectedPositiveAnchorPayment N n root tau p g F =
      bankFixedSlackMass N n root tau p g F := by
  unfold bankSelectedPositiveAnchorPayment bankFixedSlackMass
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro l _
  rw [action_positive_anchor_eq_actual_fixed_slack g a F hcells]
  simp only [occurrenceScale, mul_assoc]

/-- The TRUE original selected positive occurrence-weighted fixed read.
Do not identify a specified-cell read with a scalar-owner lookup. -/
def selectedLiteralFixedMass
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      occurrenceScale N n root tau p g l *
        fixedValue (precedingH g) a

/-- The same selected occurrences with the exact analytic W1/W2
fixed reference, retaining the original W2 four-to-one weighting. -/
def selectedLiteralReferenceMass
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      occurrenceScale N n root tau p g l * fixedReference F a

/-- Conservation at EVERY selected bank Fin-list occurrence:
actual-Q80 fixed mass + outstanding positive deficit equals reference
mass. This uses the predecessor CLOSED-CELL premise; without it
the positive-part deficit need not equal the signed fixed slack. -/
theorem selected_literal_fixed_mass_conservation
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ)
    (hcells : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i →
        floorValue (iterate g.val true) i ≤ F s) :
    bankSelectedPositiveAnchorPayment N n root tau p g F +
      selectedLiteralFixedMass N n root tau p g =
      selectedLiteralReferenceMass N n root tau p g F := by
  rw [selected_positive_anchor_eq_fixed_slack_mass
    N n root tau p g F hcells]
  unfold bankFixedSlackMass selectedLiteralFixedMass
    selectedLiteralReferenceMass
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro l _
  simp only [fixedReadSlack, occurrenceScale]
  ring

/-- Conservation over precisely 430 earlier generations, with
no change of the original selected action or repeated Fin positions. -/
theorem all_generations_literal_fixed_mass_conservation
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (F : ℝ → ℝ)
    (hclosed : ∀ g : Fin 430, ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i →
        floorValue (iterate g.val true) i ≤ F s) :
    (∑ g : Fin 430,
      bankSelectedPositiveAnchorPayment N n root tau p g F) +
    (∑ g : Fin 430,
      selectedLiteralFixedMass N n root tau p g) =
    (∑ g : Fin 430,
      selectedLiteralReferenceMass N n root tau p g F) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  exact selected_literal_fixed_mass_conservation
    N n root tau p g F (hclosed g)

/-- Final original-root accounting form: retain the complete actual
Q80 floor credit AND place the genuine old fixed-read mass on the
LEFT. This exposes the exact bridge needed for later physical
fixed-source/owner matching; it does not claim that source is paid. -/
theorem frozen_root_le_reference_with_literal_fixed_mass
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hclosed : ∀ g : Fin 430, ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i →
        floorValue (iterate g.val true) i ≤ F s) :
    weightedRequest N (rootQ N n root tau p) 430
        (rootRequest N n root tau p) +
      (∑ g : Fin 430,
        bankCompleteFloorCredit N n root tau p g) +
      (∑ g : Fin 430,
        selectedLiteralFixedMass N n root tau p g) ≤
      (∑ l : LevelIndex N n root tau p 0,
        levelMark l *
          max 0 (weightedRequest N (rootQ N n root tau p) 0
            (levelOccurrence l).current)) +
      (∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          (bankBaseIdealPositive N n root tau p g +
            selectedLiteralReferenceMass N n root tau p g F) +
          bankPhysicalAppliedAbs N n root tau p g)) := by
  have hroot := frozen_root_le_live_anchors_with_complete_floor
    N n root tau p F hN ht ht' hn hp hband hclosed
  have hsource :
      (∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          (bankBaseIdealPositive N n root tau p g +
            bankSelectedPositiveAnchorPayment N n root tau p g F) +
          bankPhysicalAppliedAbs N n root tau p g)) +
      (∑ g : Fin 430,
        selectedLiteralFixedMass N n root tau p g) =
      (∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          (bankBaseIdealPositive N n root tau p g +
            selectedLiteralReferenceMass N n root tau p g F) +
          bankPhysicalAppliedAbs N n root tau p g)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro g _
    have hm := selected_literal_fixed_mass_conservation
      N n root tau p g F (hclosed g)
    linarith only [hm]
  linarith only [hroot, hsource]

end
end ImbalancedChen.Part5OriginalH430LiveAnchorMassConservation
