import ImbalancedChen.Part5OriginalH430SelectedAnchorBackwardVariation

/-!
P5.6 / h34: exact CLIPPED deterioration and recovery of the genuinely
selected W1/W2 fixed-anchor defects along the literal Q80 table iterations.

The earlier backward-variation packet charged every downward step at an
original fixed cell, even when the step lay entirely ABOVE the analytic
reference F and therefore did not increase its positive anchor deficit.
This source charges only the portion of a decrease that ACTUALLY crosses
the positive gap, and keeps an equally clipped credit for later upward
motion. Both are exact for the ORIGINAL iterate k -> k+1, not guessed
errors or a monotonicity assertion.

W1 pays its single original endpoint; W2 keeps its original 4:1 weights.
All finite selected action occurrences retain their original
occurrenceScale, marks, and same-Q Theta. The frozen 430-root statement
keeps the complete per-product and outer-integer floor credit and places
the genuine anchor RECOVERY on the left, with the clipped deterioration
on the right. The preceding CLOSED-CELL condition and quantitative
payment obligations remain explicit. SOURCE ONLY / UNCOMPILED.
-/

namespace ImbalancedChen.Part5OriginalH430ClippedAnchorRecovery

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430ActualFixedClosedCell
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430TrueBankFeedbackFloorCredit
open Part5OriginalH430ClosedCellPositivePrefloor
open Part5OriginalH430ClosedCellIdealSplit
open Part5OriginalH430SelectedPositiveAnchorPayment
open Part5OriginalH430ExactOuterQ80FloorCredit
open Part5OriginalH430SelectedAnchorBackwardVariation

/-- Only the part of a literal Q80 cell DECREASE that increases the
positive reference-versus-table gap is charged. -/
def effectiveAnchorRise (k : ℕ) (i : Fin 200) (z : ℝ) : ℝ :=
  min (max 0 (z - floorValue (iterate (k+1) true) i))
    (actualUpperCellDrop k i)

/-- Conversely, only an actual decrease in a previously present
positive gap is credited when the literal Q80 cell rises. -/
def effectiveAnchorRecovery (k : ℕ) (i : Fin 200) (z : ℝ) : ℝ :=
  min (max 0 (z - floorValue (iterate k true) i))
    (max 0 (floorValue (iterate (k+1) true) i -
      floorValue (iterate k true) i))

theorem effectiveAnchorRise_nonneg (k : ℕ) (i : Fin 200) (z : ℝ) :
    0 ≤ effectiveAnchorRise k i z := by
  unfold effectiveAnchorRise actualUpperCellDrop
  exact le_min (le_max_left _ _) (le_max_left _ _)

theorem effectiveAnchorRecovery_nonneg (k : ℕ) (i : Fin 200) (z : ℝ) :
    0 ≤ effectiveAnchorRecovery k i z := by
  unfold effectiveAnchorRecovery
  exact le_min (le_max_left _ _) (le_max_left _ _)

theorem effectiveAnchorRise_le_drop (k : ℕ) (i : Fin 200) (z : ℝ) :
    effectiveAnchorRise k i z ≤ actualUpperCellDrop k i := by
  exact min_le_right _ _

/-- One-step exact positive-gap balance; no monotonicity premise.
The two min terms cap deterioration and recovery at the gap actually
available for the corresponding direction of motion. -/
private theorem clipped_step_balance (x y z : ℝ) :
    max 0 (z-y) +
      min (max 0 (z-x)) (max 0 (y-x)) =
    max 0 (z-x) +
      min (max 0 (z-y)) (max 0 (x-y)) := by
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- Telescoping with both capped charges. Unlike a one-sided sum of
all downward steps, the recovered positive gap is not discarded. -/
private theorem clipped_range_balance (f : ℕ → ℝ) (z : ℝ) (m : ℕ) :
    max 0 (z-f m) +
      (∑ k ∈ Finset.range m,
        min (max 0 (z-f k)) (max 0 (f (k+1)-f k))) =
    max 0 (z-f 0) +
      (∑ k ∈ Finset.range m,
        min (max 0 (z-f (k+1))) (max 0 (f k-f (k+1)))) := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [Finset.sum_range_succ]
      have hs := clipped_step_balance (f m) (f (m+1)) z
      linarith only [ih, hs]

/-- Original W1 uses one endpoint; original W2 uses the SAME physical
two endpoints and 4:1 fixed-read weights, not duplicate full charges. -/
def actionEffectiveRise (k : ℕ) (F : ℝ → ℝ) :
    Original106Action → ℝ
  | .inl ij => effectiveAnchorRise k (w1Cell ij.2) (F (W1Anchor ij.2))
  | .inr j =>
      (4 * effectiveAnchorRise k (w2Cell j true) (F (originalW2At j).s0) +
        effectiveAnchorRise k (w2Cell j false) (F (originalW2At j).phi1)) / 5

def actionEffectiveRecovery (k : ℕ) (F : ℝ → ℝ) :
    Original106Action → ℝ
  | .inl ij => effectiveAnchorRecovery k (w1Cell ij.2) (F (W1Anchor ij.2))
  | .inr j =>
      (4 * effectiveAnchorRecovery k (w2Cell j true) (F (originalW2At j).s0) +
        effectiveAnchorRecovery k (w2Cell j false) (F (originalW2At j).phi1)) / 5

def actionCumulativeEffectiveRise (g : Fin 430) (F : ℝ → ℝ)
    (a : Original106Action) : ℝ :=
  ∑ k ∈ Finset.range g.val, actionEffectiveRise k F a

def actionCumulativeEffectiveRecovery (g : Fin 430) (F : ℝ → ℝ)
    (a : Original106Action) : ℝ :=
  ∑ k ∈ Finset.range g.val, actionEffectiveRecovery k F a

theorem action_effective_rise_le_backward_drop
    (k : ℕ) (a : Original106Action) (F : ℝ → ℝ) :
    actionEffectiveRise k F a ≤ actionBackwardDrop k a := by
  rcases a with ⟨i, j⟩ | j
  · simpa [actionEffectiveRise, actionBackwardDrop] using
      effectiveAnchorRise_le_drop k (w1Cell j) (F (W1Anchor j))
  · have h0 := effectiveAnchorRise_le_drop k
      (w2Cell j true) (F (originalW2At j).s0)
    have h1 := effectiveAnchorRise_le_drop k
      (w2Cell j false) (F (originalW2At j).phi1)
    dsimp [actionEffectiveRise, actionBackwardDrop]
    linarith only [h0, h1]

theorem action_effective_recovery_nonneg
    (k : ℕ) (a : Original106Action) (F : ℝ → ℝ) :
    0 ≤ actionEffectiveRecovery k F a := by
  rcases a with ⟨i, j⟩ | j
  · simpa [actionEffectiveRecovery] using
      effectiveAnchorRecovery_nonneg k (w1Cell j) (F (W1Anchor j))
  · have h0 := effectiveAnchorRecovery_nonneg k
      (w2Cell j true) (F (originalW2At j).s0)
    have h1 := effectiveAnchorRecovery_nonneg k
      (w2Cell j false) (F (originalW2At j).phi1)
    dsimp [actionEffectiveRecovery]
    linarith only [h0, h1]

/-- EXACT endpoint recurrence for the original action at generation g:
defect-now + recovered = defect-at-iterate-zero + effective rises.
The old gross downward-variation bound follows by dropping the
nonnegative recovered charge and enlarging effective rises. -/
theorem action_anchor_balance (g : Fin 430) (a : Original106Action)
    (F : ℝ → ℝ) :
    actionPositiveAnchorAllowance g F a +
      actionCumulativeEffectiveRecovery g F a =
    actionPositiveAnchorAllowance firstOriginalGeneration F a +
      actionCumulativeEffectiveRise g F a := by
  rcases a with ⟨i, j⟩ | j
  · have h := clipped_range_balance
      (fun k : ℕ => floorValue (iterate k true) (w1Cell j))
      (F (W1Anchor j)) g.val
    simpa [actionPositiveAnchorAllowance, firstOriginalGeneration,
      actionCumulativeEffectiveRecovery, actionCumulativeEffectiveRise,
      actionEffectiveRecovery, actionEffectiveRise,
      effectiveAnchorRecovery, effectiveAnchorRise,
      actualUpperCellDrop, precedingH] using h
  · have h0 := clipped_range_balance
      (fun k : ℕ => floorValue (iterate k true) (w2Cell j true))
      (F (originalW2At j).s0) g.val
    have h1 := clipped_range_balance
      (fun k : ℕ => floorValue (iterate k true) (w2Cell j false))
      (F (originalW2At j).phi1) g.val
    dsimp [actionPositiveAnchorAllowance, firstOriginalGeneration,
      actionCumulativeEffectiveRecovery, actionCumulativeEffectiveRise,
      actionEffectiveRecovery, actionEffectiveRise,
      effectiveAnchorRecovery, effectiveAnchorRise,
      actualUpperCellDrop, precedingH]
    simp only [Finset.sum_div, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    linear_combination (4 / 5 : ℝ) * h0 + (1 / 5 : ℝ) * h1

/-- Exact recovered amount at every real selected Fin occurrence.
No distinctness of arithmetic products or paths is assumed. -/
def bankSelectedAnchorRecovery (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (F : ℝ → ℝ) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      occurrenceScale N n root tau p g l *
        actionCumulativeEffectiveRecovery g F a

/-- The corresponding clipped, not gross, deterioration amount. -/
def bankSelectedEffectiveRise (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (F : ℝ → ℝ) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      occurrenceScale N n root tau p g l *
        actionCumulativeEffectiveRise g F a

/-- This is an exact balance on original selected LIST POSITIONS,
including multiplicity and original same-Q parent theta/mark. -/
theorem bank_selected_anchor_balance (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (F : ℝ → ℝ) :
    bankSelectedPositiveAnchorPayment N n root tau p g F +
      bankSelectedAnchorRecovery N n root tau p g F =
    bankSelectedSeedAnchorPayment N n root tau p g F +
      bankSelectedEffectiveRise N n root tau p g F := by
  unfold bankSelectedPositiveAnchorPayment bankSelectedAnchorRecovery
    bankSelectedSeedAnchorPayment bankSelectedEffectiveRise
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  linear_combination
    (occurrenceScale N n root tau p g l) * action_anchor_balance g a F

theorem bank_selected_anchor_recovery_nonneg
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    0 ≤ bankSelectedAnchorRecovery N n root tau p g F := by
  unfold bankSelectedAnchorRecovery
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro l _
  apply mul_nonneg
  · exact occurrenceScale_nonneg N n root tau p g l
      hN ht ht' hn hp hband
  · unfold actionCumulativeEffectiveRecovery
    apply Finset.sum_nonneg
    intro k _
    exact action_effective_recovery_nonneg k a F

theorem bank_selected_effective_rise_le_backward_variation
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    bankSelectedEffectiveRise N n root tau p g F ≤
      bankSelectedBackwardVariationPayment N n root tau p g := by
  unfold bankSelectedEffectiveRise bankSelectedBackwardVariationPayment
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro l _
  apply mul_le_mul_of_nonneg_left
  · unfold actionCumulativeEffectiveRise actionCumulativeBackwardDrop
    apply Finset.sum_le_sum
    intro k _
    exact action_effective_rise_le_backward_drop k a F
  · exact occurrenceScale_nonneg N n root tau p g l
      hN ht ht' hn hp hband

/-- Sharper original root consumer: FULL Q80 floor credit and ACTUAL
anchor recovery are on the LEFT; only effective clipped deterioration
is on the RIGHT. This does not pay either source nor discharge hclosed. -/
theorem frozen_root_le_clipped_rise_with_floor_and_recovery
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
      (∑ g : Fin 430, bankCompleteFloorCredit N n root tau p g) +
      (∑ g : Fin 430, bankSelectedAnchorRecovery N n root tau p g F) ≤
      (∑ l : LevelIndex N n root tau p 0,
        levelMark l *
          max 0 (weightedRequest N (rootQ N n root tau p) 0
            (levelOccurrence l).current)) +
      ∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          (bankBaseIdealPositive N n root tau p g +
            bankSelectedSeedAnchorPayment N n root tau p g F +
            bankSelectedEffectiveRise N n root tau p g F) +
          bankPhysicalAppliedAbs N n root tau p g) := by
  have hroot := frozen_root_le_prefloor_with_complete_credit
    N n root tau p hN ht ht' hn hp hband
  have hlevels :
      (∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          bankPreFloorIdealExcess N n root tau p g +
            bankPhysicalAppliedAbs N n root tau p g)) +
      (∑ g : Fin 430, bankSelectedAnchorRecovery N n root tau p g F) ≤
      ∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          (bankBaseIdealPositive N n root tau p g +
            bankSelectedSeedAnchorPayment N n root tau p g F +
            bankSelectedEffectiveRise N n root tau p g F) +
          bankPhysicalAppliedAbs N n root tau p g) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro g _
    have h0 := bank_prefloor_le_closed_cell_positive
      N n root tau p g F hN ht ht' hn hp hband (hclosed g)
    have h1 := (bank_closed_cell_positive_sandwich
      N n root tau p g F hN ht ht' hn hp hband (hclosed g)).2
    have h2 := bankFixedSlackMass_le_selectedPositiveAnchorPayment
      N n root tau p g F hN ht ht' hn hp hband
    have h3 := bank_selected_anchor_balance N n root tau p g F
    linarith only [h0, h1, h2, h3]
  linarith only [hroot, hlevels]

end
end ImbalancedChen.Part5OriginalH430ClippedAnchorRecovery
