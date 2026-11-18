import ImbalancedChen.Part5OriginalH430ClippedAnchorRecovery

/-!
P5.6 / h34 — literal Q80 retention eliminates ALL selected fixed-anchor
deterioration. The original old-table decision has a retained alternative,
and its maximum keeps every numerator nondecreasing at exactly the same
upper/lower bit and Fin 200 cell. Therefore every upper fixed-cell positive
defect relative to a fixed reference F is nonincreasing.

This is NOT a numerical test, an appeal to an unrelated P2 iteration,
or an extra bounded-error hypothesis. The proof invokes the existing
Part5OriginalH430DecisionProvenance.iterate_le_succ for the EXACT
P2Selected430CausalOccurrenceExporter.iterate used in the existing
selected W1/W2 requests. It preserves the original W2 4:1 mixture,
106 selected Fin occurrences and real positive marks.

The previous clipped deterioration sum is identically ZERO, while the
real clipped recovery remains on the left of the 430-root bound.
The zero-iterate anchor mismatch remains UNPAID. Likewise, CLOSED-CELL,
Buchstab/seed, count ownership and analytic PP/same-rho remain open.
SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430MonotoneQ80AnchorZeroRise

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430DecisionProvenance
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ClosedCellIdealSplit
open Part5OriginalH430SelectedAnchorBackwardVariation
open Part5OriginalH430ClippedAnchorRecovery
open Part5OriginalH430ExactOuterQ80FloorCredit

/-- Literal retention of the very SAME Q80 upper table used by
the actual fixed W1/W2 readings, rather than the unrelated P2 test
iteration. No switch of cell, bit or reference function occurs. -/
theorem actual_upper_floor_le_succ (k : ℕ) (i : Fin 200) :
    floorValue (iterate k true) i ≤
      floorValue (iterate (k+1) true) i := by
  have hi := iterate_le_succ k true i
  have hr : (iterate k true i : ℝ) ≤
      (iterate (k+1) true i : ℝ) := by
    exact_mod_cast hi
  unfold floorValue
  exact div_le_div_of_nonneg_right hr (by positivity)

/-- The previously charged Q80 downward move is identically zero
for the original MAX-with-retention update, not merely small. -/
theorem actual_upper_cell_drop_zero (k : ℕ) (i : Fin 200) :
    actualUpperCellDrop k i = 0 := by
  unfold actualUpperCellDrop
  exact max_eq_left (sub_nonpos.mpr (actual_upper_floor_le_succ k i))

/-- The clipped deterioration is zero at EACH real original fixed cell,
for ANY fixed analytic reference value z. -/
theorem effective_anchor_rise_zero (k : ℕ) (i : Fin 200) (z : ℝ) :
    effectiveAnchorRise k i z = 0 := by
  apply le_antisymm
  · simpa only [actual_upper_cell_drop_zero] using
      effectiveAnchorRise_le_drop k i z
  · exact effectiveAnchorRise_nonneg k i z

/-- The original W1 and W2 4:1 action has no positive anchor deterioration. -/
theorem action_effective_rise_zero
    (k : ℕ) (a : Original106Action) (F : ℝ → ℝ) :
    actionEffectiveRise k F a = 0 := by
  rcases a with ⟨i, j⟩ | j
  · simpa only [actionEffectiveRise] using
      effective_anchor_rise_zero k (w1Cell j) (F (W1Anchor j))
  · simp [actionEffectiveRise, effective_anchor_rise_zero]

theorem action_backward_drop_zero (k : ℕ) (a : Original106Action) :
    actionBackwardDrop k a = 0 := by
  rcases a with ⟨i, j⟩ | j
  · simpa only [actionBackwardDrop] using
      actual_upper_cell_drop_zero k (w1Cell j)
  · simp [actionBackwardDrop, actual_upper_cell_drop_zero]

/-- No hidden last 430-to-431 step is paid. This vanishes on the
existing [0,g) prefix of the literal iteration. -/
theorem action_cumulative_effective_rise_zero
    (g : Fin 430) (F : ℝ → ℝ) (a : Original106Action) :
    actionCumulativeEffectiveRise g F a = 0 := by
  simp [actionCumulativeEffectiveRise, action_effective_rise_zero]

theorem action_cumulative_backward_drop_zero
    (g : Fin 430) (a : Original106Action) :
    actionCumulativeBackwardDrop g a = 0 := by
  simp [actionCumulativeBackwardDrop, action_backward_drop_zero]

/-- Even if distinct selected occurrences share the same arithmetic
product, every individual original marked Fin occurrence has zero rise. -/
theorem bank_selected_effective_rise_zero
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ) :
    bankSelectedEffectiveRise N n root tau p g F = 0 := by
  simp [bankSelectedEffectiveRise, action_cumulative_effective_rise_zero]

theorem bank_selected_backward_variation_zero
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    bankSelectedBackwardVariationPayment N n root tau p g = 0 := by
  simp [bankSelectedBackwardVariationPayment,
    action_cumulative_backward_drop_zero]

/-- Existing exact clipped balance now becomes an unconditional
within-action identity: current positive fixed-anchor debt plus ACTUAL
Q80 recovery equals the initial table's positive anchor debt.
There is no growth or separate variation charge. -/
theorem action_anchor_eq_seed_sub_recovery
    (g : Fin 430) (a : Original106Action) (F : ℝ → ℝ) :
    actionPositiveAnchorAllowance g F a +
      actionCumulativeEffectiveRecovery g F a =
    actionPositiveAnchorAllowance firstOriginalGeneration F a := by
  have h := action_anchor_balance g a F
  simpa only [action_cumulative_effective_rise_zero, add_zero] using h

/-- This nonincreasing bound is about the actual Q80 fixed-anchor
reference defect, NOT yet about the full base/feedback ideal comparison. -/
theorem action_positive_anchor_le_seed
    (g : Fin 430) (a : Original106Action) (F : ℝ → ℝ) :
    actionPositiveAnchorAllowance g F a ≤
      actionPositiveAnchorAllowance firstOriginalGeneration F a := by
  have he := action_anchor_eq_seed_sub_recovery g a F
  have hr : 0 ≤ actionCumulativeEffectiveRecovery g F a := by
    unfold actionCumulativeEffectiveRecovery
    apply Finset.sum_nonneg
    intro k _
    exact action_effective_recovery_nonneg k a F
  linarith only [he, hr]

/-- Exact identity at selected Fin LIST positions, with real
occurrenceScale and same-Q Theta; no set-based deduplication. -/
theorem bank_selected_anchor_eq_seed_plus_recovery
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ) :
    bankSelectedPositiveAnchorPayment N n root tau p g F +
      bankSelectedAnchorRecovery N n root tau p g F =
    bankSelectedSeedAnchorPayment N n root tau p g F := by
  have h := bank_selected_anchor_balance N n root tau p g F
  simpa only [bank_selected_effective_rise_zero, add_zero] using h

theorem bank_selected_anchor_le_seed
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    bankSelectedPositiveAnchorPayment N n root tau p g F ≤
      bankSelectedSeedAnchorPayment N n root tau p g F := by
  have he := bank_selected_anchor_eq_seed_plus_recovery
    N n root tau p g F
  have hr := bank_selected_anchor_recovery_nonneg
    N n root tau p g F hN ht ht' hn hp hband
  linarith only [he, hr]

/-- Stronger frozen root consumer: ORIGINAL Q80 max retention removes
the entire clipped deterioration term, while keeping both the full
integer feedback/outer-floor credit and actual positive recovery on
the LEFT. No new h34-equivalent bound is assumed. The manuscript-local
predecessor CLOSED-CELL invariant is explicitly NOT discharged. -/
theorem frozen_root_le_seed_with_full_floor_and_recovery
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
            bankSelectedSeedAnchorPayment N n root tau p g F) +
          bankPhysicalAppliedAbs N n root tau p g) := by
  have h := frozen_root_le_clipped_rise_with_floor_and_recovery
    N n root tau p F hN ht ht' hn hp hband hclosed
  simpa only [bank_selected_effective_rise_zero, add_zero] using h

/-- Optional weaker statement obtained only by DROPPING genuine
nonnegative recovery, not by double counting it as a fixed saving. -/
theorem frozen_root_le_seed_with_complete_floor
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
      (∑ g : Fin 430, bankCompleteFloorCredit N n root tau p g) ≤
      (∑ l : LevelIndex N n root tau p 0,
        levelMark l *
          max 0 (weightedRequest N (rootQ N n root tau p) 0
            (levelOccurrence l).current)) +
      ∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          (bankBaseIdealPositive N n root tau p g +
            bankSelectedSeedAnchorPayment N n root tau p g F) +
          bankPhysicalAppliedAbs N n root tau p g) := by
  have h := frozen_root_le_seed_with_full_floor_and_recovery
    N n root tau p F hN ht ht' hn hp hband hclosed
  have hr : 0 ≤ ∑ g : Fin 430,
      bankSelectedAnchorRecovery N n root tau p g F := by
    apply Finset.sum_nonneg
    intro g _
    exact bank_selected_anchor_recovery_nonneg
      N n root tau p g F hN ht ht' hn hp hband
  linarith only [h, hr]

end
end ImbalancedChen.Part5OriginalH430MonotoneQ80AnchorZeroRise
