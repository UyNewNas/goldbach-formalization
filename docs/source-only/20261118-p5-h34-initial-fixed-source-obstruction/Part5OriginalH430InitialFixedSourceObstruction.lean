import ImbalancedChen.Part5OriginalH430ActualWinnerFixedRead
import ImbalancedChen.Part5OriginalH430LiteralZeroFixedSeed
import ImbalancedChen.Part5OriginalH430TaggedArithmeticReceivers

/-!
P5.6 / h34: a literal FIRST-GENERATION obstruction to treating the
genuine selected bank FIXED channel as an original U3/U4 q-count owner.

All 106 fixed reads at predecessor generation zero are identically
zero in the original Q80 seed. Consequently the actual winner-fixed
mass is zero at the first generated request level, EVEN IF bank actions
win and even if retention/Buchstab requests are also resolved.
This is stronger than the older empty-resolved-level obstruction.

At later generations, an empty bank winner set still has zero fixed
mass while nonbank resolved actions remain a separate physical source.
Original q is the genuine positive quotient receiver, not asserted prime.

No assumption that original U3/U4 receipts are funded by fixed reads
is introduced. These are necessary source-coverage obstructions, not
a substitute for U3/U4 count-owner, CLOSED-CELL or h34 closure.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430InitialFixedSourceObstruction

noncomputable section
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430FixedReadDictionary
open Part5OriginalH430SelectedAnchorBackwardVariation
open Part5OriginalH430LiteralZeroFixedSeed
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430LiveAnchorMassConservation
open Part5OriginalH430ActualWinnerFixedRead
open Part5OriginalH430TaggedArithmeticReceivers

/-- The actual original 106-action fixed term, NOT the whole selected
candidate, is zero on the unmodified upper Q80 seed. W2 remains 4:1. -/
theorem first_original_bank_fixed_value_zero (a : Original106Action) :
    fixedValue (precedingH firstOriginalGeneration) a = 0 := by
  rcases a with ⟨i, j⟩ | j
  · change floorValue (iterate 0 true) (w1Cell j) = 0
    exact w1_initial_fixed_floor_zero j
  · change (4 * floorValue (iterate 0 true) (w2Cell j true) +
       floorValue (iterate 0 true) (w2Cell j false)) / 5 = 0
    rw [w2_initial_fixed_floor_zero j true,
      w2_initial_fixed_floor_zero j false]
    norm_num

/-- The genuine g+1 resolver has zero selected-bank fixed channel at
g=0, for EVERY list position and every action choice. This does not
assert the retained or Buchstab physical value is zero. -/
theorem first_actual_winner_fixed_read_zero
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (l : Index N n root tau p firstOriginalGeneration) :
    actualWinnerFixedRead N n root tau p firstOriginalGeneration l = 0 := by
  cases hc : actualChoice N n root tau p firstOriginalGeneration l with
  | none => simp [actualWinnerFixedRead, hc]
  | some c =>
      cases c with
      | retained => simp [actualWinnerFixedRead, hc]
      | buchstab => simp [actualWinnerFixedRead, hc]
      | bank k =>
          simpa [actualWinnerFixedRead, hc] using
            (first_original_bank_fixed_value_zero (actionOfSlot k))

/-- Even a NONEMPTY actual bank or resolved list carries zero
original fixed-channel mass at generation one; occurrenceScale and
all repeated Fin positions are kept, not replaced by unit weights. -/
theorem first_resolved_winner_fixed_mass_zero
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) :
    resolvedWinnerFixedMass N n root tau p firstOriginalGeneration = 0 := by
  unfold resolvedWinnerFixedMass
  apply Finset.sum_eq_zero
  intro l hl
  rw [first_actual_winner_fixed_read_zero N n root tau p l]
  ring

theorem first_selected_literal_fixed_mass_zero
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) :
    selectedLiteralFixedMass N n root tau p firstOriginalGeneration = 0 := by
  rw [← resolved_winner_fixed_mass_eq_literal_selected]
  exact first_resolved_winner_fixed_mass_zero N n root tau p

/-- A later level with no actual selected 106-bank winner also has
no bank fixed read. This DOES NOT imply the resolved level is empty:
retention/Buchstab winners are still present in the original partition. -/
theorem bank_empty_resolved_fixed_mass_zero
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430)
    (hbank : bankLevel N n root tau p g = ∅) :
    resolvedWinnerFixedMass N n root tau p g = 0 := by
  rw [resolved_winner_fixed_mass_eq_literal_selected,
    selected_literal_fixed_mass_eq_bank_winner_positions]
  simp [hbank]

/-- When no bank wins, the genuine resolved action ledger still
contains its retained and Buchstab terms. No arithmetic q/tag source
has been silently discarded and no bank owner is invented. -/
theorem bank_empty_resolved_sum_is_nonbank
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430)
    (hbank : bankLevel N n root tau p g = ∅)
    (f : Index N n root tau p g → ℝ) :
    (∑ l ∈ resolvedLevel N n root tau p g, f l) =
      (∑ l ∈ retainedLevel N n root tau p g, f l) +
      (∑ l ∈ buchstabLevel N n root tau p g, f l) := by
  have h := resolved_level_sum_all_actions N n root tau p g f
  have hb :
      (∑ a : Original106Action,
        ∑ l ∈ selectedLevel N n root tau p g a, f l) = 0 := by
    rw [← bank_level_sum_eq_original_106]
    simp [hbank]
  rw [hb] at h
  simpa only [add_zero] using h

/-- A real original quotient receiver q (not necessarily prime) is
strictly positive count mass. No scalar multiple of the ACTUAL
first-stage bank-fixed read can alone dominate that count, because
this precise channel is identically zero. This is a NEGATIVE
necessary-condition result, not an assumed h34 count inequality. -/
theorem first_fixed_channel_cannot_pay_original_q
    (N n : ℕ) (root : Root) (tau : ℝ) (p q : ℕ)
    (hq : q ∈ originalReceiver N p) (C : ℝ) :
    ¬ (((originalReceiver N p).card : ℝ) ≤
      C * resolvedWinnerFixedMass N n root tau p firstOriginalGeneration) := by
  have hpos : (0 : ℝ) < ((originalReceiver N p).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr ⟨q, hq⟩)
  intro h
  rw [first_resolved_winner_fixed_mass_zero, mul_zero] at h
  exact (not_le_of_gt hpos) h

/-- This failure remains possible beyond the first stage if the
actual selector picks retention/Buchstab but no bank at that level.
It does NOT say the whole positive physical source is zero. -/
theorem empty_bank_channel_cannot_pay_original_q
    (N n : ℕ) (root : Root) (tau : ℝ) (p q : ℕ)
    (g : Fin 430)
    (hbank : bankLevel N n root tau p g = ∅)
    (hq : q ∈ originalReceiver N p) (C : ℝ) :
    ¬ (((originalReceiver N p).card : ℝ) ≤
      C * resolvedWinnerFixedMass N n root tau p g) := by
  have hpos : (0 : ℝ) < ((originalReceiver N p).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr ⟨q, hq⟩)
  intro h
  rw [bank_empty_resolved_fixed_mass_zero N n root tau p g hbank,
    mul_zero] at h
  exact (not_le_of_gt hpos) h

end
end ImbalancedChen.Part5OriginalH430InitialFixedSourceObstruction
