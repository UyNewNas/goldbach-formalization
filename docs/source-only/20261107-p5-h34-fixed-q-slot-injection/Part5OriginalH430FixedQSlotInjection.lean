import ImbalancedChen.Part5OriginalH430PhysicalSlotListPositions

/-!
P5.6 / h34: an actual rank-two LIST-POSITION capacity INJECTION
for observed physical slots sharing ONE fixed physical Q.

The previous packet obtained one Fin-bounded occurrence for each
observed (Q,p,ell) slot. Here the observed source is filtered to one
literal Q. Each observed slot in that fibre receives a concrete
position in the existing firstExitDepthFrontier 2 LIST. If two such
positions are equal, their selected prefixes agree. Their ordered
prime pairs therefore agree; the Q coordinates are already equal.
This proves injection on the finite PHYSICAL-SLOT fibre.

The resulting cardinal bound is per-Q only. We do not sum frontier
capacities across Q, infer that a slot survives full/selected/inherited
filtering, count q/tag receipts as distinct slots, or assign any owner
mass. In particular, the prior explicit cross-tag and multi-q
surplus lanes remain unpaid. We do not assume Nodup for any frontier
LIST or identify a historical state value with a list occurrence.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430FixedQSlotInjection

noncomputable section
open scoped Classical
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430PhysicalSlotListPositions

/-- Restrict REAL observed historical slots to ONE physical Q.
The finite filter retains every distinct (p,ell) pair in that Q fibre;
it does not count an original q or a U3/U4 tag as a fresh slot. -/
def observedPhysicalSlotsAtQ
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ) :
    Finset (ℝ × ℕ × ℕ) :=
  (observedPhysicalSlots N cap precision tau z0 lower).filter
    (fun slot => slot.1 = Q)

/-- An observed Q-fibre slot has a bounded position in the actual
rank-two recursive LIST for this very Q. There is no simultaneous-Q
selection or division by a possibly-zero history mark. -/
theorem observed_fixed_q_slot_has_position
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (slot : ℝ × ℕ × ℕ)
    (hs : slot ∈ observedPhysicalSlotsAtQ
      N cap precision tau z0 lower Q) :
    ∃ i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length,
      (actualPhysicalRankTwoList N cap z0 Q lower)[i].selectedPrefix =
        [slot.2.2, slot.2.1] := by
  have hsource : slot ∈ observedPhysicalSlots
      N cap precision tau z0 lower :=
    (Finset.mem_filter.mp hs).1
  have hQ : slot.1 = Q := (Finset.mem_filter.mp hs).2
  obtain ⟨i, hi⟩ :=
    observed_slot_has_actual_rank_two_position
      N cap precision tau z0 lower slot hsource
  subst Q
  exact ⟨i, hi⟩

/-- A canonical position selection over the observed fixed-Q fibre.
This is only a finite position witness, NOT a filtered history owner
or a per-receipt payment. -/
def fixedQSlotPosition
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (slot : ℝ × ℕ × ℕ)
    (hs : slot ∈ observedPhysicalSlotsAtQ
      N cap precision tau z0 lower Q) :
    Fin (actualPhysicalRankTwoList N cap z0 Q lower).length :=
  Classical.choose
    (observed_fixed_q_slot_has_position
      N cap precision tau z0 lower Q slot hs)

/-- The selected actual LIST position retains the precise ordered
prime prefix [ell,p] of its source physical slot. -/
theorem fixed_q_slot_position_prefix
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ)
    (slot : ℝ × ℕ × ℕ)
    (hs : slot ∈ observedPhysicalSlotsAtQ
      N cap precision tau z0 lower Q) :
    (actualPhysicalRankTwoList N cap z0 Q lower)[
      fixedQSlotPosition
        N cap precision tau z0 lower Q slot hs].selectedPrefix =
          [slot.2.2, slot.2.1] := by
  exact Classical.choose_spec
    (observed_fixed_q_slot_has_position
      N cap precision tau z0 lower Q slot hs)

/-- A function from exactly the finite observed Q-fibre to actual
Fin-bounded LIST positions; the subtype carries the source proof. -/
def fixedQSlotPositionMap
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ) :
    {slot // slot ∈ observedPhysicalSlotsAtQ
      N cap precision tau z0 lower Q} →
      Fin (actualPhysicalRankTwoList N cap z0 Q lower).length :=
  fun s => fixedQSlotPosition
    N cap precision tau z0 lower Q s.1 s.2

/-- For one physical Q, DIFFERENT observed (Q,p,ell) slots
cannot choose the same actual rank-two LIST position.
This result does NOT claim uniqueness of positions for one slot;
a frontier might still contain repeated occurrences of a state. -/
theorem fixed_q_slot_position_injective
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ) :
    Function.Injective
      (fixedQSlotPositionMap N cap precision tau z0 lower Q) := by
  intro s t heq
  have hs := fixed_q_slot_position_prefix
    N cap precision tau z0 lower Q s.1 s.2
  have ht := fixed_q_slot_position_prefix
    N cap precision tau z0 lower Q t.1 t.2
  have hprefix :
      ([s.1.2.2, s.1.2.1] : List ℕ) =
        [t.1.2.2, t.1.2.1] := by
    calc
      [s.1.2.2, s.1.2.1] =
        (actualPhysicalRankTwoList N cap z0 Q lower)[
          fixedQSlotPositionMap N cap precision tau z0 lower Q s
          ].selectedPrefix := hs.symm
      _ =
        (actualPhysicalRankTwoList N cap z0 Q lower)[
          fixedQSlotPositionMap N cap precision tau z0 lower Q t
          ].selectedPrefix := by rw [heq]
      _ = [t.1.2.2, t.1.2.1] := ht
  have hell : s.1.2.2 = t.1.2.2 :=
    (List.cons.inj hprefix).1
  have hp : s.1.2.1 = t.1.2.1 :=
    (List.cons.inj (List.cons.inj hprefix).2).1
  have hq : s.1.1 = t.1.1 := by
    calc
      s.1.1 = Q := (Finset.mem_filter.mp s.2).2
      _ = t.1.1 := (Finset.mem_filter.mp t.2).2.symm
  apply Subtype.ext
  exact Prod.ext hq (Prod.ext hp hell)

/-- Exact per-Q CAPACITY UPPER BOUND in the true recursive rank-two
LIST, without supposing Nodup or pretending that tagged q receipts
inject into this LIST. The output is still before all historical
full/selected/inherited filters and is not a payment estimate. -/
theorem observed_fixed_q_slots_card_le_frontier_length
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) (Q : ℝ) :
    (observedPhysicalSlotsAtQ N cap precision tau z0 lower Q).card ≤
      (actualPhysicalRankTwoList N cap z0 Q lower).length := by
  classical
  have hbound :
      Fintype.card
        {slot // slot ∈ observedPhysicalSlotsAtQ
          N cap precision tau z0 lower Q} ≤
        Fintype.card
          (Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) :=
    Fintype.card_le_of_injective
      (fixedQSlotPositionMap N cap precision tau z0 lower Q)
      (fixed_q_slot_position_injective
        N cap precision tau z0 lower Q)
  simpa using hbound

end
end ImbalancedChen.Part5OriginalH430FixedQSlotInjection
