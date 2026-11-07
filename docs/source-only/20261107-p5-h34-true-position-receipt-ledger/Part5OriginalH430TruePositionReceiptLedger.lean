import ImbalancedChen.Part5OriginalH430FixedQPositionFilterLedger
import ImbalancedChen.Part5OriginalH430PhysicalSlotCollisionLedger

/-!
P5.6/h34 — ORIGINAL q/tag-dependent arithmetic receipt weights transported
onto actual fixed-Q rank-two LIST POSITIONS.

Earlier packets assigned distinct observed physical slots (Q,p,ell)
to distinct bounded Fin positions, but did not place even one original
q/tag receipt weight on those positions. This packet transports the
ONE representative receipt per physical slot to the genuine position;
the within-slot tagged collisions and q-fibre surplus stay separate
and UNPAID. The position weight is arithmetic, not the historical
state mass or signed Euler exit.

The only instantiated position filter is the original ordinary Rosser
complete-prefix gate already used by the recursion. It is NOT the
manuscript's full/selected/inherited count predicate. No ownership,
payment inequality, simultaneous-Q mass budget or final h34 closure.
SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430TruePositionReceiptLedger

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedRankTwoFibreCapacity
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430PhysicalSlotListPositions
open Part5OriginalH430FixedQSlotInjection
open Part5OriginalH430FixedQPositionFilterLedger

/-- The actual finite set of physical Q values represented by the
original retained U3/U4 quotient receipts. This is not a universal Q. -/
def observedReceiptQs (N cap precision : ℕ) (tau z0 : ℝ)
    (lower : Bool) : Finset ℝ :=
  (observedPhysicalSlots N cap precision tau z0 lower).image Prod.fst

/-- Exactly ONE original tagged (p,q) receipt per physical (Q,p,ell)
slot, chosen through the already-proved source fibres. This keeps the
original q-dependent weight w rather than substituting history mass. -/
def slotRepresentativeArithmeticWeight
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) (slot : ℝ × ℕ × ℕ) : ℝ :=
  w (keyRepresentative N cap precision tau z0 lower
      (physicalSlotRepresentative N cap precision tau z0 lower slot))

/-- Original representative arithmetic source weight at the LITERAL
Fin index of the true rank-two history LIST for one fixed physical Q.
No deduplication of the history list; the source position map is the
one constructed in the preceding fixed-Q injection packet. -/
def originalWeightAtActualPosition
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) (Q : ℝ)
    (i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) : ℝ :=
  ∑ s : SlotAtQ N cap precision tau z0 lower Q,
    if fixedQSlotPositionMap N cap precision tau z0 lower Q s = i
    then slotRepresentativeArithmeticWeight
      N cap precision tau z0 lower w s.1 else 0

/-- Summing over actual bounded list indices gives the exact source
representative weight of every observed fixed-Q physical slot. This
is a reindexing identity, NOT a history-mass payment. -/
theorem actual_position_rep_weight_sum
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) (Q : ℝ) :
    (∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      originalWeightAtActualPosition
        N cap precision tau z0 lower w Q i) =
      ∑ s : SlotAtQ N cap precision tau z0 lower Q,
        slotRepresentativeArithmeticWeight
          N cap precision tau z0 lower w s.1 := by
  classical
  simp only [originalWeightAtActualPosition]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  simp

/-- One actual list position at fixed Q cannot acquire two distinct
observed source slots. It may still represent several original q/tag
receipts: those reside in the explicit collision/surplus sums. -/
theorem actual_position_preimage_subsingleton
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (Q : ℝ)
    (s t : SlotAtQ N cap precision tau z0 lower Q)
    (h : fixedQSlotPositionMap N cap precision tau z0 lower Q s =
         fixedQSlotPositionMap N cap precision tau z0 lower Q t) :
    s = t :=
  fixed_q_slot_position_injective N cap precision tau z0 lower Q h

/-- A position never selected by an observed physical slot receives
ZERO representative arithmetic weight. This says nothing about other
historical events at that position. -/
theorem actual_position_weight_zero_outside_slots
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) (Q : ℝ)
    (i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length)
    (hnone : ¬ ∃ s : SlotAtQ N cap precision tau z0 lower Q,
      fixedQSlotPositionMap N cap precision tau z0 lower Q s = i) :
    originalWeightAtActualPosition
      N cap precision tau z0 lower w Q i = 0 := by
  classical
  unfold originalWeightAtActualPosition
  apply Finset.sum_eq_zero
  intro s hs
  have hsi : fixedQSlotPositionMap
      N cap precision tau z0 lower Q s ≠ i := by
    intro h
    exact hnone ⟨s, h⟩
  simp [hsi]

/-- At this one REAL complete-prefix Rosser gate, the sum of actual
position weights is unchanged. The complete arithmetic
full/selected/inherited predicates are NOT identified with it. -/
theorem actual_prefix_keeps_position_rep_weights
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) (Q : ℝ) :
    (∑ i ∈ keptPositions N cap z0 Q lower
        (actualFullPrefixGate lower Q),
      originalWeightAtActualPosition
        N cap precision tau z0 lower w Q i) =
      ∑ s : SlotAtQ N cap precision tau z0 lower Q,
        slotRepresentativeArithmeticWeight
          N cap precision tau z0 lower w s.1 := by
  rw [actual_full_prefix_keeps_positions N cap z0 Q lower]
  exact actual_position_rep_weight_sum N cap precision tau z0 lower w Q

/-- Every observed slot has exactly one Q coordinate in the
original finite Q set. Different physical Q values are never pooled
into one frontier list. -/
theorem observed_slot_rep_weight_by_Q
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
      slotRepresentativeArithmeticWeight
        N cap precision tau z0 lower w slot) =
      ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
        ∑ slot ∈ observedPhysicalSlotsAtQ
          N cap precision tau z0 lower Q,
          slotRepresentativeArithmeticWeight
            N cap precision tau z0 lower w slot := by
  classical
  calc
    _ = ∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
          ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
            if slot.1 = Q then
              slotRepresentativeArithmeticWeight
                N cap precision tau z0 lower w slot else 0 := by
          apply Finset.sum_congr rfl
          intro slot hs
          have hq : slot.1 ∈
              observedReceiptQs N cap precision tau z0 lower :=
            Finset.mem_image.mpr ⟨slot, hs, rfl⟩
          simp [hq]
    _ = ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
          ∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
            if slot.1 = Q then
              slotRepresentativeArithmeticWeight
                N cap precision tau z0 lower w slot else 0 := by
          rw [Finset.sum_comm]
    _ = _ := by
          apply Finset.sum_congr rfl
          intro Q hQ
          simp only [observedPhysicalSlotsAtQ, Finset.sum_filter]

/-- The ORIGINAL q/tag representatives, still weighted by their
actual arithmetic source weights, now lie at TRUE finite rank-two
positions, separately for each physical Q. No q-dependent
weight is silently replaced by 1/((p-1)(ell-1)). -/
theorem observed_slot_rep_weight_at_actual_positions
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
      slotRepresentativeArithmeticWeight
        N cap precision tau z0 lower w slot) =
      ∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
        ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
          originalWeightAtActualPosition
            N cap precision tau z0 lower w Q i := by
  rw [observed_slot_rep_weight_by_Q]
  apply Finset.sum_congr rfl
  intro Q hQ
  have hsum := actual_position_rep_weight_sum
    N cap precision tau z0 lower w Q
  simpa [SlotAtQ] using hsum.symm

/-- Full retained ORIGINAL U3/U4 q/tag source, not root-mark-one
mass, decomposes into (a) original representative weights on real
rank-two Fin positions for each separate Q; (b) ALL extra tagged
keys at each collided physical slot; (c) ALL extra q receipts for each
tagged key. The last two are explicitly UNPAID. The first is still
only positional arithmetic weight, not a full/selected/inherited owner
or a signed historical Euler payment. -/
theorem retained_receipts_actual_position_signed_ledger
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ retainedReceipts N cap precision tau z0 lower, w z) =
      ((∑ Q ∈ observedReceiptQs N cap precision tau z0 lower,
          ∑ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
            originalWeightAtActualPosition
              N cap precision tau z0 lower w Q i) +
        (∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
          ∑ key ∈
            (physicalSlotTaggedFibre N cap precision tau z0 lower slot).erase
              (physicalSlotRepresentative N cap precision tau z0 lower slot),
            w (keyRepresentative N cap precision tau z0 lower key))) +
        (∑ key ∈ observedRankTwoKeys N cap precision tau z0 lower,
          ∑ z ∈
            (keyReceiptFibre N cap precision tau z0 lower key).erase
              (keyRepresentative N cap precision tau z0 lower key),
            w z) := by
  calc
    _ = ((∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
           slotRepresentativeArithmeticWeight
             N cap precision tau z0 lower w slot) +
          (∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
            ∑ key ∈
              (physicalSlotTaggedFibre N cap precision tau z0 lower slot).erase
                (physicalSlotRepresentative N cap precision tau z0 lower slot),
              w (keyRepresentative N cap precision tau z0 lower key))) +
          (∑ key ∈ observedRankTwoKeys N cap precision tau z0 lower,
            ∑ z ∈
              (keyReceiptFibre N cap precision tau z0 lower key).erase
                (keyRepresentative N cap precision tau z0 lower key),
              w z) :=
        retained_physical_slot_signed_ledger
          N cap precision tau z0 lower w
    _ = _ := by
      rw [observed_slot_rep_weight_at_actual_positions
        N cap precision tau z0 lower w]

end
end ImbalancedChen.Part5OriginalH430TruePositionReceiptLedger
