import ImbalancedChen.Part5OriginalH430SequentialTaggedReceiptDebt

/-!
P5.6 / h34 — push ALL retained original q/tag arithmetic receipts to
the REAL bounded rank-two Fin list occurrence at each TRUE physical Q.

The previous positional source carried only one representative receipt per
observed physical slot; the previous sequential ledger carried the whole
q/tag fibre but summed over SLOTS rather than history list positions.
Here each true Fin position receives the entire fibre of any physical slot
that maps to it. The actual fixed-Q slot injection is reused unchanged.

This is an exact arithmetic pushforward, not a proof that these Fin
positions are the manuscript's full/selected/inherited owner. It does
not identify q with the selected history prime ell, merge physical Q
fibres, erase U4's second label or pay any Euler/six-lane cost.

SOURCE_ONLY / CANDIDATE_UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430FullTaggedActualFinPushforward

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430PhysicalSlotListPositions
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430FixedQSlotInjection
open Part5OriginalH430FixedQPositionFilterLedger
open Part5OriginalH430TruePositionReceiptLedger
open Part5OriginalH430SequentialSlotErasure
open Part5OriginalH430SequentialTaggedReceiptDebt

/-- ALL original tagged q receipts at an actual bounded rank-two
history LIST position, not merely one chosen arithmetic representative
and not the historical state mass. For each physical Q the sum is
formed on its own genuine Fin index set. -/
def actualAllTaggedAtFin
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) (Q : ℝ)
    (i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) : ℝ :=
  ∑ s : SlotAtQ N cap precision tau z0 lower Q,
    if fixedQSlotPositionMap N cap precision tau z0 lower Q s = i
    then actualSlotTaggedWeight N cap precision tau z0 lower w Q s
    else 0

/-- All original q/tag occurrences over a true Q are transported
exactly to the real Fin LIST positions. Multiple receipts in the same
slot stay as multiple summands inside the single position weight. -/
theorem actual_all_tagged_fin_total_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) (Q : ℝ) :
    (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      actualAllTaggedAtFin N cap precision tau z0 lower w Q i) =
    ∑ s : SlotAtQ N cap precision tau z0 lower Q,
      actualSlotTaggedWeight N cap precision tau z0 lower w Q s := by
  classical
  unfold actualAllTaggedAtFin
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  simp

/-- An actual historical list occurrence that is not the image of
ANY observed original physical slot carries zero source weight,
even if the history state itself has positive native mass. -/
theorem actual_all_tagged_fin_zero_outside_slots
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) (Q : ℝ)
    (i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length)
    (hnone : ¬ ∃ s : SlotAtQ N cap precision tau z0 lower Q,
      fixedQSlotPositionMap N cap precision tau z0 lower Q s = i) :
    actualAllTaggedAtFin N cap precision tau z0 lower w Q i = 0 := by
  classical
  unfold actualAllTaggedAtFin
  apply Finset.sum_eq_zero
  intro s hs
  have hne : fixedQSlotPositionMap
      N cap precision tau z0 lower Q s ≠ i := by
    intro h
    exact hnone ⟨s, h⟩
  simp [hne]

/-- Filtering the ACTUAL Fin indices by a Q-dependent state test
exactly filters all original tagged q receipts by their physical
slot's unique actual position. No cardinality-one assumption is made
about the q/tag receipt fibre at an occupied position. -/
theorem actual_all_tagged_fin_kept_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) (Q : ℝ)
    (keep : FirstExitDepthState ℕ → Bool) :
    (∑ i ∈ keptPositions N cap z0 Q lower keep,
      actualAllTaggedAtFin N cap precision tau z0 lower w Q i) =
    ∑ s ∈ keptSlots N cap precision tau z0 lower Q keep,
      actualSlotTaggedWeight N cap precision tau z0 lower w Q s := by
  classical
  unfold actualAllTaggedAtFin
  rw [Finset.sum_comm]
  simp [keptSlots, keptPositions]

/-- The existing TRUE ordinary Rosser full-prefix gate preserves
all source receipt weight at its actual rank-two positions. This
does NOT identify the missing selected/inherited owner. -/
theorem actual_all_tagged_fin_full_prefix_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) (Q : ℝ) :
    (∑ i ∈ keptPositions N cap z0 Q lower
        (actualFullPrefixGate lower Q),
      actualAllTaggedAtFin N cap precision tau z0 lower w Q i) =
    ∑ s : SlotAtQ N cap precision tau z0 lower Q,
      actualSlotTaggedWeight N cap precision tau z0 lower w Q s := by
  rw [actual_full_prefix_keeps_positions N cap z0 Q lower]
  exact actual_all_tagged_fin_total_exact
    N cap precision tau z0 lower w Q

/-- After TWO state tests at the same true physical Q, the
full arithmetic receipt mass on actual Fin indices is exactly the
remaining FIN mass plus stage-one q/tag deletions and stage-two
incremental q/tag deletions. Every signed receipt is preserved.
No erased slot is charged twice, but no deleted receipt is paid. -/
theorem actual_all_tagged_fin_two_stage_conservation
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) (Q : ℝ)
    (first second : FirstExitDepthState ℕ → Bool) :
    (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      actualAllTaggedAtFin N cap precision tau z0 lower w Q i) =
    (∑ i ∈ keptPositions N cap z0 Q lower
        (fun t => first t && second t),
      actualAllTaggedAtFin N cap precision tau z0 lower w Q i) +
    (∑ s ∈ erasedSlots N cap precision tau z0 lower Q first,
      actualSlotTaggedWeight N cap precision tau z0 lower w Q s) +
    (∑ s ∈ keptSlots N cap precision tau z0 lower Q first ∩
        erasedSlots N cap precision tau z0 lower Q second,
      actualSlotTaggedWeight N cap precision tau z0 lower w Q s) := by
  have h := fixed_q_sequential_tagged_conservation
    N cap precision tau z0 lower Q first second w
  rw [← actual_all_tagged_fin_total_exact
      N cap precision tau z0 lower w Q,
    ← actual_all_tagged_fin_kept_exact
      N cap precision tau z0 lower w Q
        (fun t => first t && second t)] at h
  exact h

end
end ImbalancedChen.Part5OriginalH430FullTaggedActualFinPushforward
