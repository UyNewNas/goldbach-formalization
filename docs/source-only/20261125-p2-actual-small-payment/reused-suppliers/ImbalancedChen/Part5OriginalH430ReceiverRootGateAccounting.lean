import ImbalancedChen.Part5OriginalH430ReceiverRootFrontier

/-!
P5.6 / h34: exact U3/U4 receiver-indexed root-gate and post-root
first-exit accounting.

Prior six lanes use a single historical frontier and the next packet
constructs a receiver's own rank-one frontier only conditionally.
This packet accounts for *every* original rejected tagged receiver:
a failed root gate; or, after the genuine root gates, a quotient first
bad factor outside the receiver's own suffix, retained at its own
Rosser prefix, or rejected at that exact prefix.  No source term is
silently deleted. The two source tags and their different bad-factor
cutoffs remain separate.

The gate-failure and post-root retained/outside lanes are EXPLICIT
UNPAID exceptions. Only the fourth lane has a conditional event
certificate, and different original receipts may share an event.
Neither a root-count-weight equality nor a signed payment is inferred.
All statements are manuscript-internal candidate Lean source.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430ReceiverRootGateAccounting

noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430HistoricalReceiverSixLanes
open Part5OriginalH430ReceiverRootFrontier

/-- Exact receiver-specific prerequisites for the ordinary rank-one
root. The global physical comparison z0 <= cap is required separately
when an actual frontier certificate is constructed. -/
def rootLicensed (N : ℕ) (z0 Q : ℝ) (lower : Bool)
    (z : TaggedReceiver) : Prop :=
  (¬ arithmeticPrime z ∣ N) ∧
  (arithmeticPrime z : ℝ) < z0 ∧
  ordinaryRosserPrefixAdmissible lower Q [arithmeticPrime z]

/-- Original receipts for which at least one real root gate is not
proved. No such receipt is assigned an invented historical event. -/
def gateBlocked (S : Finset TaggedReceiver)
    (N : ℕ) (z0 Q : ℝ) (lower : Bool) : Finset TaggedReceiver :=
  S.filter (fun z => ¬ rootLicensed N z0 Q lower z)

/-- Physically licensed original roots whose *own* bad factor is not
strictly below that root prime. -/
def ownCarrierOutside (S : Finset TaggedReceiver)
    (bad : TaggedReceiver → ℕ)
    (N : ℕ) (z0 Q : ℝ) (lower : Bool) : Finset TaggedReceiver :=
  S.filter (fun z =>
    rootLicensed N z0 Q lower z ∧
    ¬ (bad z : ℝ) < (arithmeticPrime z : ℝ))

/-- Actual bad factor is in the receiver root's strict suffix but its
literal length-two Rosser prefix is still retained. -/
def ownPolicyPass (S : Finset TaggedReceiver)
    (bad : TaggedReceiver → ℕ)
    (N : ℕ) (z0 Q : ℝ) (lower : Bool) : Finset TaggedReceiver :=
  S.filter (fun z =>
    rootLicensed N z0 Q lower z ∧
    (bad z : ℝ) < (arithmeticPrime z : ℝ) ∧
    ordinaryRosserPrefixAdmissible lower Q [bad z, arithmeticPrime z])

/-- The sole event-bearing lane: the receiver's own admitted root is
followed by its own actual first-bad factor which fails the next
ordinary Rosser test. No event-fibre injection is asserted. -/
def ownPolicyFail (S : Finset TaggedReceiver)
    (bad : TaggedReceiver → ℕ)
    (N : ℕ) (z0 Q : ℝ) (lower : Bool) : Finset TaggedReceiver :=
  S.filter (fun z =>
    rootLicensed N z0 Q lower z ∧
    (bad z : ℝ) < (arithmeticPrime z : ℝ) ∧
    ¬ordinaryRosserPrefixAdmissible lower Q [bad z, arithmeticPrime z])

/-- Exhaustive partition of one original tagged source by its OWN
root gate and its OWN root/quotient Rosser decision. -/
theorem receiver_four_lane_union
    (S : Finset TaggedReceiver) (bad : TaggedReceiver → ℕ)
    (N : ℕ) (z0 Q : ℝ) (lower : Bool) :
    S =
      gateBlocked S N z0 Q lower ∪
      (ownCarrierOutside S bad N z0 Q lower ∪
        (ownPolicyPass S bad N z0 Q lower ∪
          ownPolicyFail S bad N z0 Q lower)) := by
  classical
  ext z
  simp [gateBlocked, ownCarrierOutside, ownPolicyPass, ownPolicyFail]
  tauto

private theorem blocked_disjoint_others
    (S : Finset TaggedReceiver) (bad : TaggedReceiver → ℕ)
    (N : ℕ) (z0 Q : ℝ) (lower : Bool) :
    Disjoint (gateBlocked S N z0 Q lower)
      (ownCarrierOutside S bad N z0 Q lower ∪
        (ownPolicyPass S bad N z0 Q lower ∪
          ownPolicyFail S bad N z0 Q lower)) := by
  apply Finset.disjoint_left.mpr
  intro z hb hrest
  have hno : ¬rootLicensed N z0 Q lower z :=
    (Finset.mem_filter.mp hb).2
  rcases Finset.mem_union.mp hrest with ho | htail
  · exact hno (Finset.mem_filter.mp ho).2.1
  · rcases Finset.mem_union.mp htail with hp | hf
    · exact hno (Finset.mem_filter.mp hp).2.1
    · exact hno (Finset.mem_filter.mp hf).2.1

private theorem outside_disjoint_others
    (S : Finset TaggedReceiver) (bad : TaggedReceiver → ℕ)
    (N : ℕ) (z0 Q : ℝ) (lower : Bool) :
    Disjoint (ownCarrierOutside S bad N z0 Q lower)
      (ownPolicyPass S bad N z0 Q lower ∪
        ownPolicyFail S bad N z0 Q lower) := by
  apply Finset.disjoint_left.mpr
  intro z ho hrest
  have hno := (Finset.mem_filter.mp ho).2.2
  rcases Finset.mem_union.mp hrest with hp | hf
  · exact hno (Finset.mem_filter.mp hp).2.2.1
  · exact hno (Finset.mem_filter.mp hf).2.2.1

private theorem pass_disjoint_fail
    (S : Finset TaggedReceiver) (bad : TaggedReceiver → ℕ)
    (N : ℕ) (z0 Q : ℝ) (lower : Bool) :
    Disjoint (ownPolicyPass S bad N z0 Q lower)
      (ownPolicyFail S bad N z0 Q lower) := by
  apply Finset.disjoint_left.mpr
  intro z hp hf
  exact (Finset.mem_filter.mp hf).2.2.2
    (Finset.mem_filter.mp hp).2.2.2

/-- The exact original receipt count; gate failures and both non-event
lanes appear with their FULL multiplicities, not with unit historical
mass or identified physical catalogue labels. -/
theorem receiver_four_lane_card
    (S : Finset TaggedReceiver) (bad : TaggedReceiver → ℕ)
    (N : ℕ) (z0 Q : ℝ) (lower : Bool) :
    S.card =
      (gateBlocked S N z0 Q lower).card +
      (ownCarrierOutside S bad N z0 Q lower).card +
      (ownPolicyPass S bad N z0 Q lower).card +
      (ownPolicyFail S bad N z0 Q lower).card := by
  rw [receiver_four_lane_union S bad N z0 Q lower]
  rw [Finset.card_union_of_disjoint
    (blocked_disjoint_others S bad N z0 Q lower)]
  rw [Finset.card_union_of_disjoint
    (outside_disjoint_others S bad N z0 Q lower)]
  rw [Finset.card_union_of_disjoint
    (pass_disjoint_fail S bad N z0 Q lower)]
  omega

/-- Signed conservation for *arbitrary* original receipt weights.
No cancellation, absolute-value estimate or historical payment is
claimed by this equality. -/
theorem receiver_four_lane_signed
    (S : Finset TaggedReceiver) (bad : TaggedReceiver → ℕ)
    (N : ℕ) (z0 Q : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ S, w z) =
      (∑ z ∈ gateBlocked S N z0 Q lower, w z) +
      (∑ z ∈ ownCarrierOutside S bad N z0 Q lower, w z) +
      (∑ z ∈ ownPolicyPass S bad N z0 Q lower, w z) +
      (∑ z ∈ ownPolicyFail S bad N z0 Q lower, w z) := by
  rw [receiver_four_lane_union S bad N z0 Q lower]
  rw [Finset.sum_union
    (blocked_disjoint_others S bad N z0 Q lower)]
  rw [Finset.sum_union
    (outside_disjoint_others S bad N z0 Q lower)]
  rw [Finset.sum_union
    (pass_disjoint_fail S bad N z0 Q lower)]
  ring

/-- Original U3/U4 source, not a generated mark-one root: its two
different bad-prime choices have EIGHT distinct root-gate/own-root
lanes. This is the arithmetic count before any feedback payment. -/
theorem original_U34_receiver_root_eight_lane_count
    (N n : ℕ) (tau z0 Q : ℝ)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) (lower : Bool) :
    (rejectedOriginal N).card =
      (gateBlocked (frozenOnly N n tau) N z0 Q lower).card +
      (ownCarrierOutside (frozenOnly N n tau) (frozenOnlyBad N)
        N z0 Q lower).card +
      (ownPolicyPass (frozenOnly N n tau) (frozenOnlyBad N)
        N z0 Q lower).card +
      (ownPolicyFail (frozenOnly N n tau) (frozenOnlyBad N)
        N z0 Q lower).card +
      (gateBlocked (rejectedFrozen N n tau) N z0 Q lower).card +
      (ownCarrierOutside (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) N z0 Q lower).card +
      (ownPolicyPass (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) N z0 Q lower).card +
      (ownPolicyFail (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) N z0 Q lower).card := by
  have hbase := rejected_original_card_split N n tau hN htau htauhi hn
  have hf := receiver_four_lane_card (frozenOnly N n tau)
    (frozenOnlyBad N) N z0 Q lower
  have hr := receiver_four_lane_card (rejectedFrozen N n tau)
    (rejectedFrozenBad N n tau) N z0 Q lower
  omega

/-- The original raw U3/U4 integer count still has both sets of
receiver-specific root exceptions. The 1-to-1 Upsilon source identity
is not replaced by weighted historical events. -/
theorem original_U34_raw_with_eight_exceptions
    (N n : ℕ) (tau z0 Q : ℝ)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) (lower : Bool) :
    ((rawTagged N).card : ℝ) =
      currentChenUpsilon3 N + currentChenUpsilon4 N +
      ((gateBlocked (frozenOnly N n tau) N z0 Q lower).card : ℝ) +
      ((ownCarrierOutside (frozenOnly N n tau) (frozenOnlyBad N)
        N z0 Q lower).card : ℝ) +
      ((ownPolicyPass (frozenOnly N n tau) (frozenOnlyBad N)
        N z0 Q lower).card : ℝ) +
      ((ownPolicyFail (frozenOnly N n tau) (frozenOnlyBad N)
        N z0 Q lower).card : ℝ) +
      ((gateBlocked (rejectedFrozen N n tau) N z0 Q lower).card : ℝ) +
      ((ownCarrierOutside (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) N z0 Q lower).card : ℝ) +
      ((ownPolicyPass (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) N z0 Q lower).card : ℝ) +
      ((ownPolicyFail (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) N z0 Q lower).card : ℝ) := by
  have hraw := raw_U34_plus_two_rejections N n tau hN htau htauhi hn
  have hf := receiver_four_lane_card (frozenOnly N n tau)
    (frozenOnlyBad N) N z0 Q lower
  have hr := receiver_four_lane_card (rejectedFrozen N n tau)
    (rejectedFrozenBad N n tau) N z0 Q lower
  have hfc : ((frozenOnly N n tau).card : ℝ) =
      ((gateBlocked (frozenOnly N n tau) N z0 Q lower).card : ℝ) +
      ((ownCarrierOutside (frozenOnly N n tau) (frozenOnlyBad N)
        N z0 Q lower).card : ℝ) +
      ((ownPolicyPass (frozenOnly N n tau) (frozenOnlyBad N)
        N z0 Q lower).card : ℝ) +
      ((ownPolicyFail (frozenOnly N n tau) (frozenOnlyBad N)
        N z0 Q lower).card : ℝ) := by
    exact_mod_cast hf
  have hrc : ((rejectedFrozen N n tau).card : ℝ) =
      ((gateBlocked (rejectedFrozen N n tau) N z0 Q lower).card : ℝ) +
      ((ownCarrierOutside (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) N z0 Q lower).card : ℝ) +
      ((ownPolicyPass (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) N z0 Q lower).card : ℝ) +
      ((ownPolicyFail (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) N z0 Q lower).card : ℝ) := by
    exact_mod_cast hr
  rw [hfc, hrc] at hraw
  linarith

/-- All rejectedOriginal receipt weights, including negative weights,
split into the two REAL cutoff sources and four own-root lanes each.
This does not identify the finite source with any historical measure. -/
theorem original_rejected_eight_lane_signed
    (N n : ℕ) (tau z0 Q : ℝ)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384)
    (lower : Bool) (w : TaggedReceiver → ℝ) :
    (∑ z ∈ rejectedOriginal N, w z) =
      (∑ z ∈ gateBlocked (frozenOnly N n tau) N z0 Q lower, w z) +
      (∑ z ∈ ownCarrierOutside (frozenOnly N n tau)
        (frozenOnlyBad N) N z0 Q lower, w z) +
      (∑ z ∈ ownPolicyPass (frozenOnly N n tau)
        (frozenOnlyBad N) N z0 Q lower, w z) +
      (∑ z ∈ ownPolicyFail (frozenOnly N n tau)
        (frozenOnlyBad N) N z0 Q lower, w z) +
      (∑ z ∈ gateBlocked (rejectedFrozen N n tau) N z0 Q lower, w z) +
      (∑ z ∈ ownCarrierOutside (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) N z0 Q lower, w z) +
      (∑ z ∈ ownPolicyPass (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) N z0 Q lower, w z) +
      (∑ z ∈ ownPolicyFail (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) N z0 Q lower, w z) := by
  classical
  rw [rejected_original_partition N n tau hN htau htauhi hn]
  rw [Finset.sum_union (frozen_only_disjoint_rejected N n tau)]
  rw [receiver_four_lane_signed (frozenOnly N n tau)
    (frozenOnlyBad N) N z0 Q lower w]
  rw [receiver_four_lane_signed (rejectedFrozen N n tau)
    (rejectedFrozenBad N n tau) N z0 Q lower w]
  ring

/-- Each original frozenOnly receipt in the fourth *own-root* lane
gives a literal first-excluded event at its own rank-one frontier.
The cap comparison remains a real physical prerequisite; all other
receiver-specific root/policy tests are obtained from lane membership. -/
theorem frozen_own_root_fail_has_event
    (N n cap : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) {z : TaggedReceiver}
    (hz : z ∈ ownPolicyFail (frozenOnly N n tau)
      (frozenOnlyBad N) N z0 Q lower) :
    ∃ event : FirstExitDepthState ℕ,
      event ∈ historicalRejectedEvents
        (ordinaryRosserRetainedPolicy lower Q)
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        [arithmeticPrime z] false
        (1 / ((arithmeticPrime z : ℝ) - 1))
        (roughPrimeUniverse N cap 0 (arithmeticPrime z : ℝ)) ∧
      event.selectedPrefix = [frozenOnlyBad N z, arithmeticPrime z] ∧
      event.positive = true ∧
      event.mass =
        (1 / ((arithmeticPrime z : ℝ) - 1)) *
        (1 / ((frozenOnlyBad N z : ℝ) - 1)) := by
  have hmem := Finset.mem_filter.mp hz
  have hlicense : (¬ arithmeticPrime z ∣ N) ∧
      (arithmeticPrime z : ℝ) < z0 ∧
      ordinaryRosserPrefixAdmissible lower Q [arithmeticPrime z] := by
    simpa [rootLicensed] using hmem.2.1
  rcases hlicense with ⟨hnotN, hcut, hpolicy⟩
  exact frozen_receiver_own_root_first_exit
    N n cap tau z0 Q lower hzcap hmem.1
    hnotN hcut hpolicy hmem.2.2.1 hmem.2.2.2

/-- Separate frozen-cutoff failure event: original U3/U4 tags and
quotient occurrences are preserved and not identified with events. -/
theorem rejected_own_root_fail_has_event
    (N n cap : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) {z : TaggedReceiver}
    (hz : z ∈ ownPolicyFail (rejectedFrozen N n tau)
      (rejectedFrozenBad N n tau) N z0 Q lower) :
    ∃ event : FirstExitDepthState ℕ,
      event ∈ historicalRejectedEvents
        (ordinaryRosserRetainedPolicy lower Q)
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        [arithmeticPrime z] false
        (1 / ((arithmeticPrime z : ℝ) - 1))
        (roughPrimeUniverse N cap 0 (arithmeticPrime z : ℝ)) ∧
      event.selectedPrefix =
        [rejectedFrozenBad N n tau z, arithmeticPrime z] ∧
      event.positive = true ∧
      event.mass =
        (1 / ((arithmeticPrime z : ℝ) - 1)) *
        (1 / ((rejectedFrozenBad N n tau z : ℝ) - 1)) := by
  have hmem := Finset.mem_filter.mp hz
  have hlicense : (¬ arithmeticPrime z ∣ N) ∧
      (arithmeticPrime z : ℝ) < z0 ∧
      ordinaryRosserPrefixAdmissible lower Q [arithmeticPrime z] := by
    simpa [rootLicensed] using hmem.2.1
  rcases hlicense with ⟨hnotN, hcut, hpolicy⟩
  exact rejected_receiver_own_root_first_exit
    N n cap tau z0 Q lower hzcap hmem.1
    hnotN hcut hpolicy hmem.2.2.1 hmem.2.2.2

end
end ImbalancedChen.Part5OriginalH430ReceiverRootGateAccounting
