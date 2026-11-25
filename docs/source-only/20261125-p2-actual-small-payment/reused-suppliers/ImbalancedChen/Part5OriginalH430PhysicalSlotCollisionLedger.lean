import ImbalancedChen.Part5OriginalH430TaggedRankTwoFibreCapacity

/-!
P5.6 / h34: real physical-Q rank-two SLOT collisions in the original
U3/U4 selected quotient ledger.

The previous (tag,p,ell) grouping counts one ledger representative
per tagged key. This does NOT even guarantee that different tagged
keys name different historical states: an overlapping U3/U4 root can
share the physical Q and ordered [ell,p] prefix.

Here the second finite quotient uses the literal physical
(Q,p,ell) tuple. The exact ledger has THREE levels:
  (1) one proposed representative per distinct physical slot;
  (2) all extra tagged keys mapping to the same physical slot;
  (3) all extra original q receipts mapping to one tagged key.
None is silently removed or called paid. An actual frontier witness
is supplied for every observed slot, and equal slots determine the
same rank-two STATE VALUE by the preceding genuine recursion theorem.

The physical slot is NOT a full/selected/inherited list position.
No Nodup, distinct occurrence position, capacity injection, positive
Euler payment or final manuscript count-to-history theorem is claimed.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430PhysicalSlotCollisionLedger

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430ActualSecondRosserRetention
open Part5OriginalH430RankTwoFrontierConverse
open Part5OriginalH430TaggedRankTwoFibreCapacity

/-- The ACTUAL historical physical-Q and ordered two-prime prefix,
recorded without inventing a separate state for U3/U4 tags.
The second coordinate of a tagged rank-two key is ell, not q. -/
def physicalRankTwoSlot (N precision : ℕ) (tau : ℝ)
    (key : TaggedReceiver) : ℝ × ℕ × ℕ :=
  (originalPhysicalQ N precision tau key,
    arithmeticPrime key, arithmeticQuotientPrime key)

/-- Equality of physical keys requires the SAME actual Q, root p,
and second selected prime ell. No common-Q assumption is imposed. -/
theorem physical_slot_eq_iff
    (N precision : ℕ) (tau : ℝ) (k j : TaggedReceiver) :
    physicalRankTwoSlot N precision tau k =
        physicalRankTwoSlot N precision tau j ↔
      originalPhysicalQ N precision tau k =
        originalPhysicalQ N precision tau j ∧
      arithmeticPrime k = arithmeticPrime j ∧
      arithmeticQuotientPrime k = arithmeticQuotientPrime j := by
  simp only [physicalRankTwoSlot, Prod.mk.injEq, and_assoc]

/-- Replacing an original quotient q by one of its genuine retained
factors does not change the root-dependent physical Q or root p. -/
theorem chosen_key_physical_source
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver) :
    physicalRankTwoSlot N precision tau
      (chosenRankTwoKey N cap precision tau z0 lower z) =
      (originalPhysicalQ N precision tau z, arithmeticPrime z,
        chosenSecondFactor N cap precision tau z0 lower z) := by
  cases z with
  | inl v =>
      rcases v with ⟨p, q⟩
      rfl
  | inr v =>
      rcases v with ⟨p, q⟩
      rfl

/-- Two rank-two frontier members under the SAME physical slot
have the same state VALUE: prefix, sign, product mass and suffix.
This still says nothing about their multiplicity as LIST POSITIONS. -/
theorem equal_physical_slot_same_frontier_state
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (k j : TaggedReceiver) (d e : FirstExitDepthState ℕ)
    (hs : physicalRankTwoSlot N precision tau k =
      physicalRankTwoSlot N precision tau j)
    (hd : d ∈ firstExitDepthFrontier 2
      (ordinaryRosserRetainedPolicy lower
        (originalPhysicalQ N precision tau k))
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    (he : e ∈ firstExitDepthFrontier 2
      (ordinaryRosserRetainedPolicy lower
        (originalPhysicalQ N precision tau j))
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    (hdpre : d.selectedPrefix =
      [arithmeticQuotientPrime k, arithmeticPrime k])
    (hepre : e.selectedPrefix =
      [arithmeticQuotientPrime j, arithmeticPrime j]) : d = e := by
  obtain ⟨hQ, hp, hell⟩ :=
    (physical_slot_eq_iff N precision tau k j).mp hs
  have he' : e ∈ firstExitDepthFrontier 2
      (ordinaryRosserRetainedPolicy lower
        (originalPhysicalQ N precision tau k))
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0) := by
    simpa only [hQ] using he
  have hpre : d.selectedPrefix = e.selectedPrefix := by
    calc
      d.selectedPrefix =
          [arithmeticQuotientPrime k, arithmeticPrime k] := hdpre
      _ = [arithmeticQuotientPrime j, arithmeticPrime j] := by
        rw [hell, hp]
      _ = e.selectedPrefix := hepre.symm
  exact actual_frontier_state_determined_by_prefix
    2 (by decide) N cap z0
    (originalPhysicalQ N precision tau k) lower d e hd he' hpre

/-- Distinct physical slots actually observed among the retained
original U3/U4 source; no off-source key is added. -/
def observedPhysicalSlots
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    Finset (ℝ × ℕ × ℕ) :=
  (observedRankTwoKeys N cap precision tau z0 lower).image
    (physicalRankTwoSlot N precision tau)

/-- Every tagged (p,ell) key in the same TRUE physical-Q/p/ell slot.
Tag distinctions remain in this finite fibre, not in the slot value. -/
def physicalSlotTaggedFibre
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (slot : ℝ × ℕ × ℕ) : Finset TaggedReceiver :=
  (observedRankTwoKeys N cap precision tau z0 lower).filter
    (fun key => physicalRankTwoSlot N precision tau key = slot)

/-- A single TAGGED key chosen from an actually nonempty physical slot
fibre. This is a ledger representative, NOT a paid history position. -/
def physicalSlotRepresentative
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (slot : ℝ × ℕ × ℕ) : TaggedReceiver :=
  if h : slot ∈ observedPhysicalSlots N cap precision tau z0 lower then
    Classical.choose (Finset.mem_image.mp h)
  else Sum.inl (⟨0, 0⟩ : TaggedPair)

theorem physical_slot_representative_spec
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (slot : ℝ × ℕ × ℕ)
    (hs : slot ∈ observedPhysicalSlots N cap precision tau z0 lower) :
    physicalSlotRepresentative N cap precision tau z0 lower slot ∈
      observedRankTwoKeys N cap precision tau z0 lower ∧
    physicalRankTwoSlot N precision tau
      (physicalSlotRepresentative N cap precision tau z0 lower slot) =
        slot := by
  unfold physicalSlotRepresentative
  rw [dif_pos hs]
  exact Classical.choose_spec (Finset.mem_image.mp hs)

theorem physical_slot_representative_mem_fibre
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (slot : ℝ × ℕ × ℕ)
    (hs : slot ∈ observedPhysicalSlots N cap precision tau z0 lower) :
    physicalSlotRepresentative N cap precision tau z0 lower slot ∈
      physicalSlotTaggedFibre N cap precision tau z0 lower slot := by
  exact Finset.mem_filter.mpr
    (physical_slot_representative_spec
      N cap precision tau z0 lower slot hs)

/-- An observed physical slot is backed by a REAL original q receipt,
its actual retained quotient prime factor and one actual rank-two
frontier state. It is not a free slot manufactured by the quotient. -/
theorem physical_slot_has_actual_source_and_frontier
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (slot : ℝ × ℕ × ℕ)
    (hs : slot ∈ observedPhysicalSlots N cap precision tau z0 lower) :
    ∃ key z ell, ∃ d : FirstExitDepthState ℕ,
      key ∈ observedRankTwoKeys N cap precision tau z0 lower ∧
      z ∈ retainedReceipts N cap precision tau z0 lower ∧
      chosenRankTwoKey N cap precision tau z0 lower z = key ∧
      physicalRankTwoSlot N precision tau key = slot ∧
      ell.Prime ∧ ell ∣ arithmeticQuotientPrime z ∧
      d ∈ firstExitDepthFrontier 2
        (ordinaryRosserRetainedPolicy lower
          (originalPhysicalQ N precision tau z))
        (fun r : ℕ => 1 / ((r : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z0) ∧
      d.selectedPrefix = [ell, arithmeticPrime z] ∧
      d.positive = true ∧
      d.mass = historicalFirstRootMass (arithmeticPrime z) *
        (1 / ((ell : ℝ) - 1)) := by
  obtain ⟨key, hk, hslot⟩ := Finset.mem_image.mp hs
  obtain ⟨z, hz, hzkey⟩ := Finset.mem_image.mp hk
  have hzFibre : z ∈ keyReceiptFibre
      N cap precision tau z0 lower key :=
    Finset.mem_filter.mpr ⟨hz, hzkey⟩
  obtain ⟨ell, d, hell, hdiv, _hlo, _hhi,
      hd, hpre, hsign, hmass, _hkey⟩ :=
    key_receipt_has_actual_rank_two_frontier
      N cap precision tau z0 lower key z hzFibre
  exact ⟨key, z, ell, d, hk, hz, hzkey, hslot,
    hell, hdiv, hd, hpre, hsign, hmass⟩

/-- Reindex all TAGGED rank-two keys by physical historical slots.
Weights can depend on tags: collisions are not lost. -/
theorem physical_slot_weighted_partition
    {M : Type*} [AddCommMonoid M]
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → M) :
    (∑ key ∈ observedRankTwoKeys N cap precision tau z0 lower, w key) =
    ∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
      ∑ key ∈ physicalSlotTaggedFibre
        N cap precision tau z0 lower slot, w key := by
  classical
  calc
    (∑ key ∈ observedRankTwoKeys N cap precision tau z0 lower,
        w key) =
      ∑ key ∈ observedRankTwoKeys N cap precision tau z0 lower,
        ∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
          if physicalRankTwoSlot N precision tau key = slot
            then w key else 0 := by
              apply Finset.sum_congr rfl
              intro key hk
              have hs : physicalRankTwoSlot N precision tau key ∈
                  observedPhysicalSlots N cap precision tau z0 lower :=
                Finset.mem_image.mpr ⟨key, hk, rfl⟩
              rw [Finset.sum_ite_eq]
              simp [hs]
    _ = ∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
          ∑ key ∈ observedRankTwoKeys N cap precision tau z0 lower,
            if physicalRankTwoSlot N precision tau key = slot
              then w key else 0 := by
                rw [Finset.sum_comm]
    _ = ∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
          ∑ key ∈ physicalSlotTaggedFibre
            N cap precision tau z0 lower slot, w key := by
              apply Finset.sum_congr rfl
              intro slot hs
              simp only [physicalSlotTaggedFibre, Finset.sum_filter]

/-- One tagged key per physical slot; EVERY extra U3/U4 key
colliding at that Q/p/ell is retained as a signed residual. -/
theorem physical_slot_representatives_and_collisions
    {M : Type*} [AddCommMonoid M]
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → M) :
    (∑ key ∈ observedRankTwoKeys N cap precision tau z0 lower, w key) =
      (∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
        w (physicalSlotRepresentative N cap precision tau z0 lower slot)) +
      (∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
        ∑ key ∈
          (physicalSlotTaggedFibre N cap precision tau z0 lower slot).erase
            (physicalSlotRepresentative N cap precision tau z0 lower slot),
          w key) := by
  rw [physical_slot_weighted_partition N cap precision tau z0 lower w]
  calc
    (∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
        ∑ key ∈ physicalSlotTaggedFibre
          N cap precision tau z0 lower slot, w key) =
      ∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
        (w (physicalSlotRepresentative N cap precision tau z0 lower slot) +
          ∑ key ∈
            (physicalSlotTaggedFibre N cap precision tau z0 lower slot).erase
              (physicalSlotRepresentative N cap precision tau z0 lower slot),
            w key) := by
              apply Finset.sum_congr rfl
              intro slot hs
              exact (Finset.add_sum_erase
                (physicalSlotTaggedFibre N cap precision tau z0 lower slot)
                w (physical_slot_representative_mem_fibre
                  N cap precision tau z0 lower slot hs)).symm
    _ = _ := Finset.sum_add_distrib

/-- Exact number of tagged keys = unique physical slots PLUS
all tagged collisions. No unit historical payment is implied. -/
theorem physical_slot_capacity_card
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    (observedRankTwoKeys N cap precision tau z0 lower).card =
      (observedPhysicalSlots N cap precision tau z0 lower).card +
      ∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
        ((physicalSlotTaggedFibre
          N cap precision tau z0 lower slot).erase
          (physicalSlotRepresentative N cap precision tau z0 lower slot)).card := by
  simpa using
    (physical_slot_representatives_and_collisions
      (M := ℕ) N cap precision tau z0 lower (fun _ => (1 : ℕ)))

/-- Three-stage exact natural-number accounting:
source q occurrences = distinct physical historical slots +
tag collisions + all additional q occurrences at one tagged key.
Slots are NOT yet proven full/selected/inherited positions. -/
theorem retained_physical_slot_capacity_card
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    (retainedReceipts N cap precision tau z0 lower).card =
      ((observedPhysicalSlots N cap precision tau z0 lower).card +
        ∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
          ((physicalSlotTaggedFibre
            N cap precision tau z0 lower slot).erase
            (physicalSlotRepresentative N cap precision tau z0 lower slot)).card) +
      ∑ key ∈ observedRankTwoKeys N cap precision tau z0 lower,
        ((keyReceiptFibre N cap precision tau z0 lower key).erase
          (keyRepresentative N cap precision tau z0 lower key)).card := by
  rw [retained_source_capacity_card,
    physical_slot_capacity_card]

/-- The same three levels, with arbitrary signed q/tag weights.
No cancellation is used to grant a mass bound or to pay Euler exits. -/
theorem retained_physical_slot_signed_ledger
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ retainedReceipts N cap precision tau z0 lower, w z) =
      ((∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
          w (keyRepresentative N cap precision tau z0 lower
            (physicalSlotRepresentative N cap precision tau z0 lower slot))) +
        (∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
          ∑ key ∈
            (physicalSlotTaggedFibre N cap precision tau z0 lower slot).erase
              (physicalSlotRepresentative N cap precision tau z0 lower slot),
            w (keyRepresentative N cap precision tau z0 lower key))) +
      (∑ key ∈ observedRankTwoKeys N cap precision tau z0 lower,
        ∑ z ∈ (keyReceiptFibre N cap precision tau z0 lower key).erase
          (keyRepresentative N cap precision tau z0 lower key), w z) := by
  rw [retained_source_representative_and_surplus
    N cap precision tau z0 lower w]
  rw [physical_slot_representatives_and_collisions
    N cap precision tau z0 lower
      (fun key => w (keyRepresentative N cap precision tau z0 lower key))]

end
end ImbalancedChen.Part5OriginalH430PhysicalSlotCollisionLedger
