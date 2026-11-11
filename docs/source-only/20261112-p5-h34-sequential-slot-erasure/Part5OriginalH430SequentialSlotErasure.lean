import ImbalancedChen.Part5OriginalH430OccupiedSlotSlack

/-!
P5.6 / h34 — sequential TRUE fixed-Q slot-erasure accounting.

The previous exact occupied-position slack ledger accepted one Q-dependent
post-frontier filter.  Here TWO consecutive genuine position tests are
accounted for without pretending either equals the manuscript's missing
full/selected/inherited count owner.

Every source slot erased by the second test is charged ONLY if its actual
fixed-Q Fin position survived the first test.  Earlier erased slots are
not charged again. The six original q/tag rejection lanes remain intact.
The same two-stage debt then enters the exact ORIGINAL signed -1/4 term.

All claims below are internal finite accounting. Neither gate is assumed
causal or paid; actual full/selected/inherited identification remains open.
SOURCE_ONLY / CANDIDATE_UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430SequentialSlotErasure

noncomputable section
open scoped Classical BigOperators

open Part5OriginalH430FixedQPositionFilterLedger
open Part5OriginalH430TruePositionReceiptLedger
open Part5OriginalH430FilteredQPositionCapacityDebt
open Part5OriginalH430OccupiedSlotSlack
open Part5OriginalH430ActualPositionMassGap
open Part5OriginalH430NegativeQuarterActualPositionDirection

/-- Applying a second actual Q-dependent test after the first.
The predicate is a conjunction evaluated on the SAME physical-Q state,
not a new owner or a permission to move between different Q fibres. -/
def sequentialQGate
    (first second : ℝ → FirstExitDepthState ℕ → Bool) :
    ℝ → FirstExitDepthState ℕ → Bool :=
  fun Q s => first Q s && second Q s

/-- At a single TRUE Q, a slot fails the combined gate exactly when
it failed the first gate, or passed the first but failed the second.
The latter is the NEW incremental original-arithmetic erasure debt. -/
theorem erased_slots_sequential_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (first second : FirstExitDepthState ℕ → Bool) :
    erasedSlots N cap precision tau z0 lower Q
        (fun s => first s && second s) =
      erasedSlots N cap precision tau z0 lower Q first ∪
        (keptSlots N cap precision tau z0 lower Q first ∩
          erasedSlots N cap precision tau z0 lower Q second) := by
  classical
  ext s
  simp only [Finset.mem_union, Finset.mem_inter,
    erasedSlots, keptSlots, Finset.mem_filter, Finset.mem_univ, true_and]
  cases hf : first ((actualPhysicalRankTwoList N cap z0 Q lower)[
      fixedQSlotPositionMap N cap precision tau z0 lower Q s]) <;>
    cases hs : second ((actualPhysicalRankTwoList N cap z0 Q lower)[
      fixedQSlotPositionMap N cap precision tau z0 lower Q s]) <;>
    simp [hf, hs]

/-- Newly erased source slots cannot belong to the earlier erased lane.
This disjointness is a statement about actual SlotAtQ occurrences. -/
theorem first_erased_disjoint_second_increment
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (first second : FirstExitDepthState ℕ → Bool) :
    Disjoint
      (erasedSlots N cap precision tau z0 lower Q first)
      (keptSlots N cap precision tau z0 lower Q first ∩
        erasedSlots N cap precision tau z0 lower Q second) := by
  apply Finset.disjoint_left.mpr
  intro s hbad hnew
  have hno := (Finset.mem_filter.mp hbad).2
  have hyes := (Finset.mem_filter.mp (Finset.mem_inter.mp hnew).1).2
  rw [hyes] at hno
  cases hno

/-- Exact Nat cardinal payment at one genuine physical Q. Nothing is
counted once per q/tag receipt; these remain distinct arithmetic lanes. -/
theorem erased_slots_sequential_card
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (first second : FirstExitDepthState ℕ → Bool) :
    (erasedSlots N cap precision tau z0 lower Q
      (fun s => first s && second s)).card =
    (erasedSlots N cap precision tau z0 lower Q first).card +
      (keptSlots N cap precision tau z0 lower Q first ∩
        erasedSlots N cap precision tau z0 lower Q second).card := by
  rw [erased_slots_sequential_exact]
  exact Finset.card_union_of_disjoint
    (first_erased_disjoint_second_increment
      N cap precision tau z0 lower Q first second)

/-- Surviving actual source slots pass BOTH tests at the SAME Q. -/
theorem kept_slots_sequential_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (first second : FirstExitDepthState ℕ → Bool) :
    keptSlots N cap precision tau z0 lower Q
        (fun s => first s && second s) =
      keptSlots N cap precision tau z0 lower Q first ∩
        keptSlots N cap precision tau z0 lower Q second := by
  classical
  ext s
  simp only [Finset.mem_inter, keptSlots,
    Finset.mem_filter, Finset.mem_univ, true_and]
  cases hf : first ((actualPhysicalRankTwoList N cap z0 Q lower)[
      fixedQSlotPositionMap N cap precision tau z0 lower Q s]) <;>
    cases hs : second ((actualPhysicalRankTwoList N cap z0 Q lower)[
      fixedQSlotPositionMap N cap precision tau z0 lower Q s]) <;>
    simp [hf, hs]

/-- Source slots admitted by stage one but rejected by stage two.
Every Q is an ORIGINAL observed Q; the tests may differ across Q.
This is an unpaid cardinal charge, not a root-weight or Euler bound. -/
def actualSecondStageSlotDebt
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (first second : ℝ → FirstExitDepthState ℕ → Bool) : ℝ :=
  ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
    (((keptSlots N cap precision tau z0 lower Q (first Q) ∩
      erasedSlots N cap precision tau z0 lower Q (second Q)).card : ℕ) : ℝ)

/-- The new second-stage debt has a sign without a manufactured
small-error estimate: it is a genuine finite cardinal sum. -/
theorem second_stage_slot_debt_nonneg
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (first second : ℝ → FirstExitDepthState ℕ → Bool) :
    0 ≤ actualSecondStageSlotDebt
      N cap precision tau z0 lower first second := by
  unfold actualSecondStageSlotDebt
  apply Finset.sum_nonneg
  intro Q hQ
  exact Nat.cast_nonneg _

/-- On the COMPLETE original physical-Q source, sequential erasure
is exactly the original first-stage debt plus the newly rejected
stage-two source slots.  There is no repeated payment. -/
theorem actual_sequential_erasure_debt_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (first second : ℝ → FirstExitDepthState ℕ → Bool) :
    actualErasedQSlotDebt N cap precision tau z0 lower
      (sequentialQGate first second) =
    actualErasedQSlotDebt N cap precision tau z0 lower first +
      actualSecondStageSlotDebt
        N cap precision tau z0 lower first second := by
  unfold actualErasedQSlotDebt actualSecondStageSlotDebt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Q hQ
  exact_mod_cast erased_slots_sequential_card
    N cap precision tau z0 lower Q (first Q) (second Q)

/-- EXACT ORIGINAL signed Chen contribution after two sequential
Q-dependent position tests: first erasures, incremental second
erasures, and all six original q/tag lanes remain SEPARATELY charged.
The positive unused-Fin slack is not declared a paid saving.
No full/selected/inherited identification is asserted by this proof. -/
theorem original_signed_quarter_sequential_debt_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    (first second : ℝ → FirstExitDepthState ℕ → Bool) :
    originalU34SignedQuarter N =
      -(1 / 4 : ℝ) *
        ((actualFilteredQPositionCapacity N cap precision tau z0 lower
              (sequentialQGate first second) +
            (actualErasedQSlotDebt N cap precision tau z0 lower first +
              actualSecondStageSlotDebt N cap precision tau z0 lower
                first second)) +
          originalSixUnpaidReceiptLanes N cap precision tau z0 lower
            (fun _ => (1 : ℝ))) +
        (1 / 4 : ℝ) *
          actualUnusedKeptQPositionSlack N cap precision tau z0 lower
            (sequentialQGate first second) := by
  have h := original_signed_quarter_with_unused_exact
    N cap precision tau z0 lower hzcap (sequentialQGate first second)
  rw [actual_sequential_erasure_debt_exact
    N cap precision tau z0 lower first second] at h
  exact h

end
end ImbalancedChen.Part5OriginalH430SequentialSlotErasure
