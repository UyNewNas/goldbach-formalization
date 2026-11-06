import ImbalancedChen.Part5OriginalH430OriginalRootCutoffObstruction

/-!
P5.6 / h34 -- exponent-level separation of the ORIGINAL U3/U4
arithmetic selected primes from a small initial first-exit presieve.

The pinned manuscript says the ordinary lower tree starts at w=a or w=h,
but its projection presieve is written z0=N^omega without assigning a
numerical omega there. Those two stages MUST NOT be identified.

This packet proves a precise obstruction FOR EVERY omega <= a and N>=2,
including the signed source ledger: no original U3/U4 arithmetic selected
prime can be the FIRST prime of that literal small-presieve tree. The
unpaid arithmetic source, including every original q occurrence, survives.
It does NOT infer omega<=a for the actual consumer, eliminate an original
receiver, or claim that later-history owners do not exist.

SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430PresieveExponentSeparation

noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430ReceiverRootGateAccounting
open Part5OriginalH430OriginalRootCutoffObstruction

/-- Real-power monotonicity is used at the ACTUAL N, rather than
introducing an invented presieve exponent or an asymptotic exception. -/
theorem presieve_power_le_original_band_start
    (N : ℕ) (omega : ℝ) (hN : 2 ≤ N) (homega : omega ≤ a) :
    (N : ℝ) ^ omega ≤ (N : ℝ) ^ a := by
  have hNat : (1 : ℕ) ≤ N := by omega
  have hbase : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hNat
  exact Real.rpow_le_rpow_of_exponent_le hbase homega

/-- Every genuine original raw U3/U4 receipt requires the presieve
exponent to be STRICTLY greater than a for rank-one root admission. -/
theorem raw_rank_one_licence_forces_exponent_gt_a
    (N : ℕ) (omega Q : ℝ) (lower : Bool)
    (hN : 2 ≤ N) {z : TaggedReceiver} (hz : z ∈ rawTagged N)
    (hlicense : rootLicensed N ((N : ℝ) ^ omega) Q lower z) :
    a < omega := by
  by_contra hle
  have homega : omega ≤ a := le_of_not_gt hle
  have hsmall := presieve_power_le_original_band_start N omega hN homega
  exact (raw_root_not_licensed N ((N : ℝ) ^ omega) Q lower
    hsmall hz) hlicense

/-- The original arithmetic selected root is not an initial historical
candidate when the presieve exponent is at or below the actual band start.
No conclusion is made about any later root stage. -/
theorem raw_rank_one_carrier_excluded
    (N cap : ℕ) (omega : ℝ) (hN : 2 ≤ N)
    (homega : omega ≤ a)
    (hcap : (N : ℝ) ^ omega ≤ (cap : ℝ))
    {z : TaggedReceiver} (hz : z ∈ rawTagged N) :
    arithmeticPrime z ∉
      roughPrimeUniverse N cap 0 ((N : ℝ) ^ omega) := by
  exact raw_root_not_initial_carrier N cap ((N : ℝ) ^ omega)
    hcap (presieve_power_le_original_band_start N omega hN homega) hz

/-- There are no root-licensed original raw receivers in ANY genuine
subfamily; retaining the full finite source is essential for counting. -/
theorem raw_rank_one_licensed_filter_empty
    (N : ℕ) (omega Q : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (homega : omega ≤ a)
    (S : Finset TaggedReceiver) (hS : S ⊆ rawTagged N) :
    S.filter (fun z =>
      rootLicensed N ((N : ℝ) ^ omega) Q lower z) = ∅ := by
  classical
  ext z
  simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false]
  rintro ⟨hz, hlicensed⟩
  exact (raw_root_not_licensed N ((N : ℝ) ^ omega) Q lower
    (presieve_power_le_original_band_start N omega hN homega)
    (hS hz)) hlicensed

/-- All original receipts in a genuine subfamily are still accounted
for as blocked, not silently removed from the count source. -/
theorem raw_presieve_blocked_exact
    (N : ℕ) (omega Q : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (homega : omega ≤ a)
    (S : Finset TaggedReceiver) (hS : S ⊆ rawTagged N) :
    gateBlocked S N ((N : ℝ) ^ omega) Q lower = S :=
  all_raw_gate_blocked N ((N : ℝ) ^ omega) Q lower
    (presieve_power_le_original_band_start N omega hN homega) S hS

/-- No member of a genuinely unlicensed source can enter the
carrier-outside sublane: that sublane starts WITH a licensed root. -/
theorem raw_presieve_own_outside_empty
    (N : ℕ) (omega Q : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (homega : omega ≤ a)
    (S : Finset TaggedReceiver) (hS : S ⊆ rawTagged N)
    (bad : TaggedReceiver → ℕ) :
    ownCarrierOutside S bad N ((N : ℝ) ^ omega) Q lower = ∅ := by
  classical
  ext z
  simp only [ownCarrierOutside, Finset.mem_filter,
    Finset.not_mem_empty, iff_false]
  rintro ⟨hz, hlicensed, _⟩
  exact (raw_root_not_licensed N ((N : ℝ) ^ omega) Q lower
    (presieve_power_le_original_band_start N omega hN homega)
    (hS hz)) hlicensed

/-- A small-presieve rank-one owner cannot classify an original
receipt as policy-pass; the licence already fails before this test. -/
theorem raw_presieve_own_pass_empty
    (N : ℕ) (omega Q : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (homega : omega ≤ a)
    (S : Finset TaggedReceiver) (hS : S ⊆ rawTagged N)
    (bad : TaggedReceiver → ℕ) :
    ownPolicyPass S bad N ((N : ℝ) ^ omega) Q lower = ∅ := by
  classical
  ext z
  simp only [ownPolicyPass, Finset.mem_filter,
    Finset.not_mem_empty, iff_false]
  rintro ⟨hz, hlicensed, _, _⟩
  exact (raw_root_not_licensed N ((N : ℝ) ^ omega) Q lower
    (presieve_power_le_original_band_start N omega hN homega)
    (hS hz)) hlicensed

/-- Even a potentially bad quotient prime creates NO rank-one
first-excluded event at the original arithmetic selected root in
this exponent regime. The full original count stays unpaid. -/
theorem raw_presieve_own_fail_empty
    (N : ℕ) (omega Q : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (homega : omega ≤ a)
    (S : Finset TaggedReceiver) (hS : S ⊆ rawTagged N)
    (bad : TaggedReceiver → ℕ) :
    ownPolicyFail S bad N ((N : ℝ) ^ omega) Q lower = ∅ := by
  classical
  ext z
  simp only [ownPolicyFail, Finset.mem_filter,
    Finset.not_mem_empty, iff_false]
  rintro ⟨hz, hlicensed, _, _⟩
  exact (raw_root_not_licensed N ((N : ℝ) ^ omega) Q lower
    (presieve_power_le_original_band_start N omega hN homega)
    (hS hz)) hlicensed

/-- Original frozenOnly rejection: all three purported post-root
lanes vanish at this presieve. Its receipts have NOT vanished. -/
theorem frozen_presieve_no_own_root_event_lanes
    (N n : ℕ) (tau omega Q : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (homega : omega ≤ a) :
    ownCarrierOutside (frozenOnly N n tau) (frozenOnlyBad N)
        N ((N : ℝ) ^ omega) Q lower = ∅ ∧
    ownPolicyPass (frozenOnly N n tau) (frozenOnlyBad N)
        N ((N : ℝ) ^ omega) Q lower = ∅ ∧
    ownPolicyFail (frozenOnly N n tau) (frozenOnlyBad N)
        N ((N : ℝ) ^ omega) Q lower = ∅ := by
  have hS : frozenOnly N n tau ⊆ rawTagged N := by
    intro z hz
    exact frozen_tagged_subset_raw N n tau (Finset.mem_sdiff.mp hz).1
  exact ⟨raw_presieve_own_outside_empty N omega Q lower hN homega
      (frozenOnly N n tau) hS (frozenOnlyBad N),
    raw_presieve_own_pass_empty N omega Q lower hN homega
      (frozenOnly N n tau) hS (frozenOnlyBad N),
    raw_presieve_own_fail_empty N omega Q lower hN homega
      (frozenOnly N n tau) hS (frozenOnlyBad N)⟩

/-- Distinct rejectedFrozen cutoff: do not merge its first-bad choice
with frozenOnly's bad-prime function or collapse repeated q receipts. -/
theorem rejected_frozen_presieve_no_own_root_event_lanes
    (N n : ℕ) (tau omega Q : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (homega : omega ≤ a) :
    ownCarrierOutside (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau)
        N ((N : ℝ) ^ omega) Q lower = ∅ ∧
    ownPolicyPass (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau)
        N ((N : ℝ) ^ omega) Q lower = ∅ ∧
    ownPolicyFail (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau)
        N ((N : ℝ) ^ omega) Q lower = ∅ := by
  have hS : rejectedFrozen N n tau ⊆ rawTagged N := by
    intro z hz
    exact (Finset.mem_sdiff.mp hz).1
  exact ⟨raw_presieve_own_outside_empty N omega Q lower hN homega
      (rejectedFrozen N n tau) hS (rejectedFrozenBad N n tau),
    raw_presieve_own_pass_empty N omega Q lower hN homega
      (rejectedFrozen N n tau) hS (rejectedFrozenBad N n tau),
    raw_presieve_own_fail_empty N omega Q lower hN homega
      (rejectedFrozen N n tau) hS (rejectedFrozenBad N n tau)⟩

/-- Exact original tagged rejection cardinality stays in the TWO
blocked sources, with all U3/U4 tags, p,q occurrences and overlap. -/
theorem rejected_presieve_original_count_unpaid
    (N n : ℕ) (tau omega Q : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384)
    (homega : omega ≤ a) :
    (rejectedOriginal N).card =
      (gateBlocked (frozenOnly N n tau) N ((N : ℝ) ^ omega)
        Q lower).card +
      (gateBlocked (rejectedFrozen N n tau) N ((N : ℝ) ^ omega)
        Q lower).card := by
  exact rejected_original_count_all_blocked N n tau
    ((N : ℝ) ^ omega) Q lower hN htau htauhi hn
    (presieve_power_le_original_band_start N omega hN homega)

/-- This is the SIGNED original receipt ledger, not a historical
root-mass sum. Arbitrary signed weights are preserved occurrence by
occurrence, and none are paid by an impossible rank-one event. -/
theorem rejected_presieve_signed_source_unpaid
    (N n : ℕ) (tau omega Q : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384)
    (homega : omega ≤ a) (w : TaggedReceiver → ℝ) :
    (∑ z ∈ rejectedOriginal N, w z) =
      (∑ z ∈ gateBlocked (frozenOnly N n tau)
        N ((N : ℝ) ^ omega) Q lower, w z) +
      (∑ z ∈ gateBlocked (rejectedFrozen N n tau)
        N ((N : ℝ) ^ omega) Q lower, w z) := by
  rw [frozen_all_gate_blocked N n tau ((N : ℝ) ^ omega) Q lower
      (presieve_power_le_original_band_start N omega hN homega),
    rejected_frozen_all_gate_blocked N n tau ((N : ℝ) ^ omega)
      Q lower (presieve_power_le_original_band_start N omega hN homega)]
  rw [rejected_original_partition N n tau hN htau htauhi hn]
  exact Finset.sum_union (frozen_only_disjoint_rejected N n tau)

end
end ImbalancedChen.Part5OriginalH430PresieveExponentSeparation
