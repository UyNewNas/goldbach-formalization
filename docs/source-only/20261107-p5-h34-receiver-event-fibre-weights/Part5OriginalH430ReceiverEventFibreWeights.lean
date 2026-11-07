import ImbalancedChen.Part5OriginalH430ReceiverRootGateAccounting

/-!
P5.6 / h34 — original rejected-receiver event FIBRE multiplicities.

The literal first-excluded event is labelled by its selected prime p
and next rejected prime ell.  Several genuine (U3/U4,p,q) receipts can
have the SAME (p,ell), including distinct q and overlapping U3/U4 bands.
The earlier receipt-specific fourth-lane witnesses therefore cannot
be summed once per distinct event without retaining the fibre count.

This file proves exact finite occurrence reindexing with ARBITRARY
signed weights, then the literal rank-two 1/(p-1) * 1/(ell-1) kernel.
It also lifts the genuine history event witness to every distinct
event key in EACH of the two original rejection cutoff lanes.
The witness is not a unique owner: no selected/full/inherited history
matching, signed rejection payment, count bound, or source-to-feedback
equality follows from event existence.

Manuscript-internal SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430ReceiverEventFibreWeights

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430ReceiverRootGateAccounting

/-- The ORIGINAL historical rank-two event is labelled by (p,ell).
The omitted q remains in each actual receiver fibre, never a quotient
of the original tagged source. -/
abbrev EventKey := ℕ × ℕ

def receiverEventKey (bad : TaggedReceiver → ℕ)
    (z : TaggedReceiver) : EventKey :=
  (arithmeticPrime z, bad z)

/-- Every original receipt with the SAME event key; distinct q and
U3/U4 tags retain distinct positions and therefore full multiplicity. -/
def eventFibre (S : Finset TaggedReceiver)
    (bad : TaggedReceiver → ℕ) (key : EventKey) :
    Finset TaggedReceiver :=
  S.filter (fun z => receiverEventKey bad z = key)

def eventKeys (S : Finset TaggedReceiver)
    (bad : TaggedReceiver → ℕ) : Finset EventKey :=
  S.image (receiverEventKey bad)

theorem mem_eventFibre_iff (S : Finset TaggedReceiver)
    (bad : TaggedReceiver → ℕ) (key : EventKey)
    (z : TaggedReceiver) :
    z ∈ eventFibre S bad key ↔
      z ∈ S ∧ receiverEventKey bad z = key := by
  simp [eventFibre]

/-- Genuine total receipt sum by event keys. The weight is arbitrary
and may DEPEND on the tag and on q; this identity needs neither
nonnegativity nor an injective receiver-to-event map. -/
theorem sum_by_event_fibres (S : Finset TaggedReceiver)
    (bad : TaggedReceiver → ℕ) (w : TaggedReceiver → ℝ) :
    (∑ key ∈ eventKeys S bad,
        ∑ z ∈ eventFibre S bad key, w z) =
      ∑ z ∈ S, w z := by
  classical
  unfold eventKeys eventFibre
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  have hm : receiverEventKey bad z ∈
      S.image (receiverEventKey bad) :=
    Finset.mem_image.mpr ⟨z, hz, rfl⟩
  simp [hm]

/-- The original first-excluded sign and mass kernel for the TRUE
selected prime and the TRUE first bad prime, not a unit root mark. -/
def originalEventMass (key : EventKey) : ℝ :=
  (1 / ((key.1 : ℝ) - 1)) * (1 / ((key.2 : ℝ) - 1))

/-- Any signed kernel constant on each (p,ell) fibre is multiplied by
the ACTUAL number of original (tag,p,q) receipts in that fibre.
No uniqueness or max-fibre bound is assumed. -/
theorem key_weighted_fibre_sum (S : Finset TaggedReceiver)
    (bad : TaggedReceiver → ℕ) (w : EventKey → ℝ) :
    (∑ z ∈ S, w (receiverEventKey bad z)) =
      ∑ key ∈ eventKeys S bad,
        ((eventFibre S bad key).card : ℝ) * w key := by
  classical
  rw [← sum_by_event_fibres S bad
    (fun z => w (receiverEventKey bad z))]
  apply Finset.sum_congr rfl
  intro key _
  calc
    (∑ z ∈ eventFibre S bad key,
        w (receiverEventKey bad z)) =
      ∑ _z ∈ eventFibre S bad key, w key := by
        apply Finset.sum_congr rfl
        intro z hz
        have hk := (mem_eventFibre_iff S bad key z).mp hz
        rw [hk.2]
    _ = ((eventFibre S bad key).card : ℝ) * w key := by
      simp [nsmul_eq_mul]

/-- Precisely the original frozenOnly fourth lane, with its actual
N^a bad-factor rule. The same key may occur multiple times. -/
theorem frozen_fail_event_mass_by_fibres (N n : ℕ) (tau z0 Q : ℝ)
    (lower : Bool) :
    (∑ z ∈ ownPolicyFail (frozenOnly N n tau)
        (frozenOnlyBad N) N z0 Q lower,
      originalEventMass (receiverEventKey (frozenOnlyBad N) z)) =
    ∑ key ∈ eventKeys
        (ownPolicyFail (frozenOnly N n tau)
          (frozenOnlyBad N) N z0 Q lower) (frozenOnlyBad N),
      ((eventFibre
        (ownPolicyFail (frozenOnly N n tau)
          (frozenOnlyBad N) N z0 Q lower)
        (frozenOnlyBad N) key).card : ℝ) *
      originalEventMass key :=
  key_weighted_fibre_sum _ _ originalEventMass

/-- The separate frozen-root cutoff does not inherit the old N^a
bad-factor function. Each occurrence is preserved independently. -/
theorem rejected_frozen_fail_event_mass_by_fibres
    (N n : ℕ) (tau z0 Q : ℝ) (lower : Bool) :
    (∑ z ∈ ownPolicyFail (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) N z0 Q lower,
      originalEventMass
        (receiverEventKey (rejectedFrozenBad N n tau) z)) =
    ∑ key ∈ eventKeys
        (ownPolicyFail (rejectedFrozen N n tau)
          (rejectedFrozenBad N n tau) N z0 Q lower)
        (rejectedFrozenBad N n tau),
      ((eventFibre
        (ownPolicyFail (rejectedFrozen N n tau)
          (rejectedFrozenBad N n tau) N z0 Q lower)
        (rejectedFrozenBad N n tau) key).card : ℝ) *
      originalEventMass key :=
  key_weighted_fibre_sum _ _ originalEventMass

/-- One historical event EXISTS for each distinct eligible event key
in the original-cutoff fourth lane. Repeated q remain a fibre MULTIPLIER,
not extra assumed independent event occurrences. -/
theorem frozen_fail_key_has_historical_event
    (N n cap : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    (key : EventKey)
    (hk : key ∈ eventKeys
      (ownPolicyFail (frozenOnly N n tau)
        (frozenOnlyBad N) N z0 Q lower) (frozenOnlyBad N)) :
    ∃ event : FirstExitDepthState ℕ,
      event ∈ historicalRejectedEvents
        (ordinaryRosserRetainedPolicy lower Q)
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        [key.1] false (1 / ((key.1 : ℝ) - 1))
        (roughPrimeUniverse N cap 0 (key.1 : ℝ)) ∧
      event.selectedPrefix = [key.2, key.1] ∧
      event.positive = true ∧
      event.mass = originalEventMass key := by
  change key ∈
    (ownPolicyFail (frozenOnly N n tau) (frozenOnlyBad N)
      N z0 Q lower).image (receiverEventKey (frozenOnlyBad N)) at hk
  rcases Finset.mem_image.mp hk with ⟨z, hz, rfl⟩
  obtain ⟨event, hmem, hprefix, hsign, hmass⟩ :=
    frozen_own_root_fail_has_event N n cap tau z0 Q lower hzcap hz
  refine ⟨event, ?_, ?_, hsign, ?_⟩
  · simpa [receiverEventKey] using hmem
  · simpa [receiverEventKey] using hprefix
  · simpa [receiverEventKey, originalEventMass] using hmass

/-- Separate key-event witness for the true frozen-cutoff rejection.
This has the correct q-dependent first bad factor and root p. -/
theorem rejected_frozen_fail_key_has_historical_event
    (N n cap : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    (key : EventKey)
    (hk : key ∈ eventKeys
      (ownPolicyFail (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) N z0 Q lower)
      (rejectedFrozenBad N n tau)) :
    ∃ event : FirstExitDepthState ℕ,
      event ∈ historicalRejectedEvents
        (ordinaryRosserRetainedPolicy lower Q)
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        [key.1] false (1 / ((key.1 : ℝ) - 1))
        (roughPrimeUniverse N cap 0 (key.1 : ℝ)) ∧
      event.selectedPrefix = [key.2, key.1] ∧
      event.positive = true ∧
      event.mass = originalEventMass key := by
  change key ∈
    (ownPolicyFail (rejectedFrozen N n tau)
      (rejectedFrozenBad N n tau) N z0 Q lower).image
      (receiverEventKey (rejectedFrozenBad N n tau)) at hk
  rcases Finset.mem_image.mp hk with ⟨z, hz, rfl⟩
  obtain ⟨event, hmem, hprefix, hsign, hmass⟩ :=
    rejected_own_root_fail_has_event N n cap tau z0 Q lower hzcap hz
  refine ⟨event, ?_, ?_, hsign, ?_⟩
  · simpa [receiverEventKey] using hmem
  · simpa [receiverEventKey] using hprefix
  · simpa [receiverEventKey, originalEventMass] using hmass

/-- Original U3/U4 receipt overlap, distinct q and two cutoff sources
are NOT quotiented away. This is an exact signed fibre ledger over the
two real event-bearing lanes, not a paid historical-owner equality. -/
theorem original_two_fail_lanes_signed_fibre_sum
    (N n : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (wf wr : TaggedReceiver → ℝ) :
    (∑ z ∈ ownPolicyFail (frozenOnly N n tau)
      (frozenOnlyBad N) N z0 Q lower, wf z) +
    (∑ z ∈ ownPolicyFail (rejectedFrozen N n tau)
      (rejectedFrozenBad N n tau) N z0 Q lower, wr z) =
    (∑ key ∈ eventKeys
      (ownPolicyFail (frozenOnly N n tau) (frozenOnlyBad N)
        N z0 Q lower) (frozenOnlyBad N),
      ∑ z ∈ eventFibre
        (ownPolicyFail (frozenOnly N n tau) (frozenOnlyBad N)
          N z0 Q lower) (frozenOnlyBad N) key, wf z) +
    (∑ key ∈ eventKeys
      (ownPolicyFail (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) N z0 Q lower)
      (rejectedFrozenBad N n tau),
      ∑ z ∈ eventFibre
        (ownPolicyFail (rejectedFrozen N n tau)
          (rejectedFrozenBad N n tau) N z0 Q lower)
        (rejectedFrozenBad N n tau) key, wr z) := by
  rw [sum_by_event_fibres, sum_by_event_fibres]

end
end ImbalancedChen.Part5OriginalH430ReceiverEventFibreWeights
