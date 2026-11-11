import ImbalancedChen.Part5OriginalH430OriginalQFibreActualPositionBridge

/-!
P5.6 / h34 — a genuine directional fact for the ORIGINAL UNIT
U3/U4 (tag,p,q) count at observed physical rank-two positions.

The previous exact position ledger left arithmetic-minus-historical
mass with UNKNOWN sign for arbitrary signed receipt weights.
For UNIT arithmetic weight, the real observed p and chosen ell
are both primes, hence the actual historical rank-two mass
1/((ell-1)*(p-1)) is at most one.  This proves a NONNEGATIVE
position mismatch, before or after any actual post-frontier filter.

This is NOT a payment of the manuscript's signed Chen quarter
(U3 versus U4), nor an owner for deeper full/selected/inherited
history.  In fact the obtained inequality controls positive
rank-two history FROM ABOVE by arithmetic receipt count; it
must NOT be reversed to claim an upper bound on the original count.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430UnitPositionMassDirection

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedRankTwoFibreCapacity
open Part5OriginalH430PhysicalSlotCollisionLedger
open Part5OriginalH430FixedQSlotInjection
open Part5OriginalH430FixedQPositionFilterLedger
open Part5OriginalH430TruePositionReceiptLedger
open Part5OriginalH430ActualPositionMassGap
open Part5OriginalH430QDependentPositionErasure
open Part5OriginalH430OriginalQFibreActualPositionBridge

/-- The p and ell coordinates of every genuinely observed ORIGINAL
physical slot are primes. The second is the CHOSEN divisor ell of q,
not the quotient prime q itself. No arbitrary slot is admitted. -/
theorem observed_original_physical_slot_primes
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (slot : ℝ × ℕ × ℕ)
    (hs : slot ∈ observedPhysicalSlots N cap precision tau z0 lower) :
    slot.2.1.Prime ∧ slot.2.2.Prime := by
  obtain ⟨key, hk, hslot⟩ := Finset.mem_image.mp hs
  obtain ⟨z, hz, hkey⟩ := Finset.mem_image.mp hk
  have hroot : z ∈
      (originalTagged N).filter
        (selectedOriginalRootStage N cap precision tau z0 lower) :=
    (Finset.mem_filter.mp hz).1
  have horig : z ∈ originalTagged N :=
    (Finset.mem_filter.mp hroot).1
  have hprime : (arithmeticPrime z).Prime := by
    cases z with
    | inl v =>
        have hv : v ∈ originalPairs N .U3 := by
          simpa [originalTagged] using horig
        exact (original_band_prime (Finset.mem_sigma.mp hv).1).1
    | inr v =>
        have hv : v ∈ originalPairs N .U4 := by
          simpa [originalTagged] using horig
        exact (original_band_prime (Finset.mem_sigma.mp hv).1).1
  have hret : hasRetainedOriginalSecond
      N cap precision tau z0 lower z :=
    (Finset.mem_filter.mp hz).2
  have hsecond : (chosenSecondFactor
      N cap precision tau z0 lower z).Prime :=
    (chosen_second_factor_spec
      N cap precision tau z0 lower z hret).1
  have hphysical :
      (originalPhysicalQ N precision tau z, arithmeticPrime z,
        chosenSecondFactor N cap precision tau z0 lower z) = slot := by
    calc
      _ = physicalRankTwoSlot N precision tau
          (chosenRankTwoKey N cap precision tau z0 lower z) :=
            (chosen_key_physical_source
              N cap precision tau z0 lower z).symm
      _ = physicalRankTwoSlot N precision tau key := by rw [hkey]
      _ = slot := hslot
  have hp : arithmeticPrime z = slot.2.1 :=
    congrArg (fun t : ℝ × ℕ × ℕ => t.2.1) hphysical
  have hell : chosenSecondFactor N cap precision tau z0 lower z =
      slot.2.2 :=
    congrArg (fun t : ℝ × ℕ × ℕ => t.2.2) hphysical
  exact ⟨hp ▸ hprime, hell ▸ hsecond⟩

/-- The actual positive rank-two state attached to a genuine
observed slot has mass at most ONE. This proves the inequality
from the original two PRIME letters; it is not a new row norm. -/
theorem observed_original_rank_two_mass_le_one
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (Q : ℝ) (s : SlotAtQ N cap precision tau z0 lower Q) :
    (actualPhysicalRankTwoList N cap z0 Q lower)[
      fixedQSlotPositionMap N cap precision tau z0 lower Q s].mass ≤ 1 := by
  have hs : s.1 ∈ observedPhysicalSlots N cap precision tau z0 lower :=
    (Finset.mem_filter.mp s.2).1
  have hpr := observed_original_physical_slot_primes
    N cap precision tau z0 lower s.1 hs
  have hp : (2 : ℝ) ≤ (s.1.2.1 : ℝ) := by
    exact_mod_cast hpr.1.two_le
  have he : (2 : ℝ) ≤ (s.1.2.2 : ℝ) := by
    exact_mod_cast hpr.2.two_le
  have hpp : 0 < (s.1.2.1 : ℝ) - 1 := by linarith
  have hep : 0 < (s.1.2.2 : ℝ) - 1 := by linarith
  have hpb : (1 : ℝ) / ((s.1.2.1 : ℝ) - 1) ≤ 1 := by
    apply (div_le_iff₀ hpp).2
    linarith
  have heb : (1 : ℝ) / ((s.1.2.2 : ℝ) - 1) ≤ 1 := by
    apply (div_le_iff₀ hep).2
    linarith
  have hpnonneg : 0 ≤ (1 : ℝ) / ((s.1.2.1 : ℝ) - 1) :=
    le_of_lt (div_pos (by norm_num) hpp)
  have hmul := mul_le_mul heb hpb hpnonneg (by norm_num : (0 : ℝ) ≤ 1)
  have hmass := (observed_fixed_q_position_true_sign_mass
    N cap precision tau z0 lower Q s).2
  rw [hmass]
  simpa only [one_mul] using hmul

/-- At EVERY actual rank-two Fin index, one original UNIT
representative per physical slot pays at least its literal
historical mass. Unobserved positions contribute zero to BOTH
terms. Distinct slots cannot share this actual index. -/
theorem unit_original_position_mass_gap_nonneg
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (Q : ℝ)
    (i : Fin (actualPhysicalRankTwoList N cap z0 Q lower).length) :
    0 ≤ originalRankTwoPositionMassGap
      N cap precision tau z0 lower (fun _ => (1 : ℝ)) Q i := by
  classical
  unfold originalRankTwoPositionMassGap
    originalWeightAtActualPosition observedRankTwoMassAtPosition
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro s hs
  by_cases h : fixedQSlotPositionMap
      N cap precision tau z0 lower Q s = i
  · have hb :
        (actualPhysicalRankTwoList N cap z0 Q lower)[i].mass ≤ 1 := by
      simpa only [h] using
        (observed_original_rank_two_mass_le_one
          N cap precision tau z0 lower Q s)
    simp only [if_pos h, slotRepresentativeArithmeticWeight]
    linarith
  · simp [h]

/-- The REAL arithmetic-minus-history mismatch for unit
q/tag representative weights is nonnegative under ANY actual
Q-dependent position filter, including the real complete-prefix
test. No false equivalence to full/selected/inherited is used. -/
theorem unit_kept_original_position_gap_nonneg
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    0 ≤ keptOriginalRankTwoGap N cap precision tau z0 lower
      (fun _ => (1 : ℝ)) keep := by
  unfold keptOriginalRankTwoGap
  apply Finset.sum_nonneg
  intro Q hQ
  apply Finset.sum_nonneg
  intro i hi
  exact unit_original_position_mass_gap_nonneg
    N cap precision tau z0 lower Q i

/-- Unit arithmetic weights deleted by a post-frontier mask are
nonnegative but NOT zero unless the actual gate is proved. -/
theorem unit_erased_original_arithmetic_nonneg
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    0 ≤ erasedOriginalPositionArithmetic N cap precision tau z0 lower
      (fun _ => (1 : ℝ)) keep := by
  classical
  unfold erasedOriginalPositionArithmetic
  apply Finset.sum_nonneg
  intro Q hQ
  apply Finset.sum_nonneg
  intro i hi
  unfold originalWeightAtActualPosition
  apply Finset.sum_nonneg
  intro s hs
  split_ifs <;> simp [slotRepresentativeArithmeticWeight]

/-- A DIRECTIONAL count-to-rank-two history consequence for UNIT
U3+U4 receipts, preserving all SIX literal q/tag rejection lanes.
The inequality is count >= positive history+six-lane weight;
it is NOT the desired upper selected-count bound, and cannot
be used in the reverse direction for the signed Chen objective. -/
theorem original_unit_count_bounds_kept_rank_two_and_six_lanes
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    (keep : ℝ → FirstExitDepthState ℕ → Bool) :
    keptOriginalRankTwoMass N cap precision tau z0 lower keep +
      originalSixUnpaidReceiptLanes N cap precision tau z0 lower
        (fun _ => (1 : ℝ)) ≤
      currentChenUpsilon3 N + currentChenUpsilon4 N := by
  have hsource := complete_original_source_with_q_dependent_erasure
    N cap precision tau z0 lower hzcap (fun _ => (1 : ℝ)) keep
  have hunit :
      (∑ z ∈ originalTagged N, (1 : ℝ)) =
        ((originalTagged N).card : ℝ) := by simp
  rw [hunit] at hsource
  have hgap := unit_kept_original_position_gap_nonneg
    N cap precision tau z0 lower keep
  have herased := unit_erased_original_arithmetic_nonneg
    N cap precision tau z0 lower keep
  rw [original_U34_eq_tagged_card]
  linarith only [hsource, hgap, herased]

end
end ImbalancedChen.Part5OriginalH430UnitPositionMassDirection
