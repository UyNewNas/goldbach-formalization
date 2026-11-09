import ImbalancedChen.Part5OriginalH430ActualPositionMassGap
import ImbalancedChen.Part5OriginalH430UpperRetainedTagPairing
import ImbalancedChen.Part5OriginalH430UpperOverlapCommonQ

/-!
P5.6 / h34 — a GLOBAL, filter-independent original U4 receipt
capacity obstruction at ACTUAL rank-two physical slots.

Unlike the local two-tag collision, this source proves that the whole
observed physical-slot set has a witness among ORIGINAL U3 (p,q)
receipts. This uses the actual frozen U3/U4 Q and the actual chosen
second factor, not a shared-Q assumption. Consequently the original
SIX unpaid arithmetic source lanes for unit weights contain at least
the complete original U4 receiver cardinality, regardless of the
presieve and ordinary retention gates.

This is only a global SOURCE-TO-ONE-SLOT cardinal shortfall. Historical
weights and signed Euler payments can cover more than one receipt; this
lower bound is NOT an impossibility theorem for H430 or an upper bound
on its analytic cost. It does not supply full/selected/inherited owner.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430GlobalU4SourceShortfall

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OriginalUpperOverlapCount
open Part5OriginalH430TaggedRankTwoFibreCapacity
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430TruePositionReceiptLedger
open Part5OriginalH430ActualPositionMassGap
open Part5OriginalH430UpperOverlapCommonQ

/-- Candidate physical slots generated using ONLY original U3 arithmetic
receipts, before filtering which ones actually survive. The slot map
still uses the true root-specific physical Q and second-prime selector. -/
def allU3CandidateSlots
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    Finset (ℝ × ℕ × ℕ) :=
  (originalPairs N .U3).image (fun x =>
    physicalRankTwoSlot N precision tau
      (chosenRankTwoKey N cap precision tau z0 lower
        (Sum.inl x : TaggedReceiver)))

/-- Every ACTUAL observed slot has an original U3 (p,q) witness.
For an original U4 receipt, the witness is its literal U3 twin:
the existing frozen-level and chosen-second-factor equalities prove
its physical (Q,p,ell) slot is unchanged. -/
theorem observed_slots_subset_original_u3_candidates
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) :
    observedPhysicalSlots N cap precision tau z0 lower ⊆
      allU3CandidateSlots N cap precision tau z0 lower := by
  classical
  intro slot hslot
  obtain ⟨key, hkey, hslotEq⟩ := Finset.mem_image.mp hslot
  obtain ⟨z, hz, hkeyEq⟩ := Finset.mem_image.mp hkey
  have horig : z ∈ originalTagged N :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
  cases z with
  | inl x =>
      have hx : x ∈ originalPairs N .U3 := by
        simpa [originalTagged] using horig
      apply Finset.mem_image.mpr
      refine ⟨x, hx, ?_⟩
      change physicalRankTwoSlot N precision tau
          (chosenRankTwoKey N cap precision tau z0 lower
            (Sum.inl x : TaggedReceiver)) = slot
      rw [hkeyEq]
      exact hslotEq
  | inr x =>
      have hx : x ∈ originalPairs N .U4 := by
        simpa [originalTagged] using horig
      have hu3 : x ∈ originalPairs N .U3 := by
        have htags := original_u4_pair_has_two_tags N (by omega) x hx
        simpa [originalTagged] using htags.1
      have hsame := original_u4_overlap_actual_slot_equal
        N cap precision tau z0 lower hN x hx
      apply Finset.mem_image.mpr
      refine ⟨x, hu3, ?_⟩
      change physicalRankTwoSlot N precision tau
          (chosenRankTwoKey N cap precision tau z0 lower
            (Sum.inl x : TaggedReceiver)) = slot
      rw [hsame, hkeyEq]
      exact hslotEq

/-- A different original U4 label cannot add a SECOND global
physical slot to the image of the actual U3 arithmetic receivers.
No injectivity or quotient-to-history owner is inferred. -/
theorem observed_slots_card_le_original_u3
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) :
    (observedPhysicalSlots N cap precision tau z0 lower).card ≤
      (originalPairs N .U3).card := by
  have hsub := observed_slots_subset_original_u3_candidates
    N cap precision tau z0 lower hN
  exact (Finset.card_le_card hsub).trans
    (Finset.card_image_le)

/-- At UNIT source weight, the existing six literal unpaid lanes are
EXACTLY the number of original tagged receipts minus the number of
physically distinct actual rank-two slots. This is a cardinal ledger,
not the original-history mass or a signed Euler correction. -/
theorem original_six_unpaid_unit_card_exact
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) :
    originalSixUnpaidReceiptLanes
        N cap precision tau z0 lower (fun _ => (1 : ℝ)) =
      ((originalTagged N).card : ℝ) -
      ((observedPhysicalSlots N cap precision tau z0 lower).card : ℝ) := by
  have hsrc := complete_original_source_at_actual_positions
    N cap precision tau z0 lower hzcap (fun _ => (1 : ℝ))
  have hpositions := observed_slot_rep_weight_at_actual_positions
    N cap precision tau z0 lower (fun _ => (1 : ℝ))
  have hslotUnit :
      (∑ slot ∈ observedPhysicalSlots N cap precision tau z0 lower,
        slotRepresentativeArithmeticWeight
          N cap precision tau z0 lower (fun _ => (1 : ℝ)) slot) =
        ((observedPhysicalSlots N cap precision tau z0 lower).card : ℝ) := by
    simp [slotRepresentativeArithmeticWeight]
  have hsourceUnit :
      (∑ z ∈ originalTagged N, (1 : ℝ)) =
        ((originalTagged N).card : ℝ) := by simp
  rw [← hpositions, hslotUnit, hsourceUnit] at hsrc
  linarith

/-- The FULL original U4 receiver source must remain visible as a
capacity shortfall in the literal six unpaid ARITHMETIC lanes, even if
all surviving original U3/U4 receivers are assigned a physical slot.
Root and quotient multiplicities are not converted into historical
weight payments. The bound survives every legal z0 and root policy. -/
theorem original_u4_global_six_lane_unit_floor
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (hzcap : z0 ≤ (cap : ℝ)) :
    ((originalPairs N .U4).card : ℝ) ≤
      originalSixUnpaidReceiptLanes
        N cap precision tau z0 lower (fun _ => (1 : ℝ)) := by
  have hnat := observed_slots_card_le_original_u3
    N cap precision tau z0 lower hN
  have hslots :
      ((observedPhysicalSlots N cap precision tau z0 lower).card : ℝ) ≤
        ((originalPairs N .U3).card : ℝ) := by
    exact_mod_cast hnat
  have htag : ((originalTagged N).card : ℝ) =
      ((originalPairs N .U3).card : ℝ) +
      ((originalPairs N .U4).card : ℝ) := by
    simp [originalTagged, Finset.card_disjSum]
  rw [original_six_unpaid_unit_card_exact
    N cap precision tau z0 lower hzcap, htag]
  linarith

end
end ImbalancedChen.Part5OriginalH430GlobalU4SourceShortfall
