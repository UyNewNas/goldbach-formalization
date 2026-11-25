import ImbalancedChen.Part5OriginalH430RootDiagonalElimination

/-!
P5.6 / h34: conditional physical presieve obstruction.
The genuine ORIGINAL U3/U4 selected prime p begins at N^a.
If a history presieve z0 does not exceed N^a, then NONE of the
original raw (band,p,q) receivers has a licensed rank-one historical
root. No original q occurrence is discarded. The source count remains
unpaid, instead of being relabeled as a first-excluded event.

Crucial scope: this packet does NOT prove the fixed manuscript chooses
z0 <= N^a, nor assert that other historical reorganizations cannot
work. The inequality is an explicit condition to check against the
pinned manuscript. SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430OriginalRootCutoffObstruction

noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430ReceiverRootGateAccounting
open Part5OriginalH430RootDiagonalElimination

/-- Exact half-open selected-prime bands BOTH include N^a. -/
theorem original_band_lower_power {N p : ℕ} {k : Root}
    (hp : p ∈ originalBand N k) :
    (N : ℝ) ^ a ≤ (p : ℝ) := by
  cases k with
  | U3 =>
      change p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a)
        ((N : ℝ) ^ (1 / 3 : ℝ)) at hp
      exact (Finset.mem_filter.mp hp).2.1
  | U4 =>
      change p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ a)
        ((N : ℝ) ^ (59 / 250 : ℝ)) at hp
      exact (Finset.mem_filter.mp hp).2.1

/-- The lower bound belongs to the ACTUAL arithmetic receiver's p. -/
theorem raw_root_lower_power {N : ℕ} {z : TaggedReceiver}
    (hz : z ∈ rawTagged N) :
    (N : ℝ) ^ a ≤ (arithmeticPrime z : ℝ) :=
  original_band_lower_power (raw_root_in_original_band hz)

/-- Any actual licensed strict root would REQUIRE N^a < z0. -/
theorem raw_strict_root_requires_large_presieve
    (N : ℕ) (z0 : ℝ) {z : TaggedReceiver}
    (hz : z ∈ rawTagged N)
    (hcut : (arithmeticPrime z : ℝ) < z0) :
    (N : ℝ) ^ a < z0 :=
  lt_of_le_of_lt (raw_root_lower_power hz) hcut

/-- A small presieve excludes all genuine U3/U4 selected primes. -/
theorem raw_root_no_strict_cutoff
    (N : ℕ) (z0 : ℝ)
    (hsmall : z0 ≤ (N : ℝ) ^ a)
    {z : TaggedReceiver} (hz : z ∈ rawTagged N) :
    ¬ (arithmeticPrime z : ℝ) < z0 := by
  exact not_lt_of_ge (hsmall.trans (raw_root_lower_power hz))

/-- A source receiver's actual root cannot satisfy the literal
Rosser-root licence if the required PHYSICAL cutoff is impossible. -/
theorem raw_root_not_licensed
    (N : ℕ) (z0 Q : ℝ) (lower : Bool)
    (hsmall : z0 ≤ (N : ℝ) ^ a)
    {z : TaggedReceiver} (hz : z ∈ rawTagged N) :
    ¬rootLicensed N z0 Q lower z := by
  intro h
  exact raw_root_no_strict_cutoff N z0 hsmall hz h.2.1

/-- The entire selected arithmetic subfamily is a ROOT-GATE exception,
not an event that can be paid using a fictitious root weight. -/
theorem all_raw_gate_blocked
    (N : ℕ) (z0 Q : ℝ) (lower : Bool)
    (hsmall : z0 ≤ (N : ℝ) ^ a)
    (S : Finset TaggedReceiver) (hS : S ⊆ rawTagged N) :
    gateBlocked S N z0 Q lower = S := by
  classical
  ext z
  simp only [gateBlocked, Finset.mem_filter]
  constructor
  · intro h
    exact h.1
  · intro hz
    exact ⟨hz, raw_root_not_licensed N z0 Q lower hsmall (hS hz)⟩

/-- True frozenOnly rejection cutoff, with all original U3/U4 labels. -/
theorem frozen_all_gate_blocked
    (N n : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (hsmall : z0 ≤ (N : ℝ) ^ a) :
    gateBlocked (frozenOnly N n tau) N z0 Q lower =
      frozenOnly N n tau := by
  apply all_raw_gate_blocked N z0 Q lower hsmall
  intro z hz
  exact frozen_tagged_subset_raw N n tau (Finset.mem_sdiff.mp hz).1

/-- Distinct rejectedFrozen cutoff; it is NOT merged with frozenOnly. -/
theorem rejected_frozen_all_gate_blocked
    (N n : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (hsmall : z0 ≤ (N : ℝ) ^ a) :
    gateBlocked (rejectedFrozen N n tau) N z0 Q lower =
      rejectedFrozen N n tau := by
  apply all_raw_gate_blocked N z0 Q lower hsmall
  intro z hz
  exact (Finset.mem_sdiff.mp hz).1

/-- Exact original rejected receiver count remains in the two blocked
channels, preserving each repeated q occurrence and overlap band. -/
theorem rejected_original_count_all_blocked
    (N n : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384)
    (hsmall : z0 ≤ (N : ℝ) ^ a) :
    (rejectedOriginal N).card =
      (gateBlocked (frozenOnly N n tau) N z0 Q lower).card +
      (gateBlocked (rejectedFrozen N n tau) N z0 Q lower).card := by
  rw [frozen_all_gate_blocked N n tau z0 Q lower hsmall,
    rejected_frozen_all_gate_blocked N n tau z0 Q lower hsmall]
  exact rejected_original_card_split N n tau hN htau htauhi hn

/-- The ORIGINAL selected prime is not even in the initial physical
first-exit universe at a low presieve. This does not claim anything
about a different or later-stage causal-history construction. -/
theorem raw_root_not_initial_carrier
    (N cap : ℕ) (z0 : ℝ)
    (hzcap : z0 ≤ (cap : ℝ))
    (hsmall : z0 ≤ (N : ℝ) ^ a)
    {z : TaggedReceiver} (hz : z ∈ rawTagged N) :
    arithmeticPrime z ∉ roughPrimeUniverse N cap 0 z0 := by
  intro hcarrier
  have hcut : (arithmeticPrime z : ℝ) < z0 :=
    ((mem_roughPrimeUniverse_iff_of_cutoff_le_cap hzcap).1 hcarrier).2.2.2
  exact raw_root_no_strict_cutoff N z0 hsmall hz hcut

end
end ImbalancedChen.Part5OriginalH430OriginalRootCutoffObstruction
