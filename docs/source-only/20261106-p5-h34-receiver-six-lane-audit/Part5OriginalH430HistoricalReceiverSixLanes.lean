import ImbalancedChen.Part5OriginalH430PostRootRemainingExact

/-!
P5.6 / h34: an EXACT six-lane audit of the ORIGINAL rejected U3/U4
receiver source against one genuine positive-rank ordinary-Rosser frontier.

This is not an arbitrary root mark-one replacement: the underlying
Finsets are the original tagged (band,p,q) receiver sets, and the
original strict/frozen cutoffs are different. Every receiver survives
in exactly one of the three post-root alternatives: outside the
remaining carrier, present but passing the Rosser prefix, or present
and failing that prefix. The same split is made separately for
frozenOnly and rejectedFrozen, then composed using the already proved
ORIGINAL arithmetic rejection partition.

For receivers in the final alternatives, the actual historical
rejected-event ledger gives a witness without a caller-provided
order or policy-failure certificate. These witnesses need NOT be
injective across tagged receivers, and this source does NOT identify
one global receiver-specific history or pay any signed rejection mass.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430HistoricalReceiverSixLanes

noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430TaggedFirstBadPrimeOwner
open Part5OriginalH430HistoricalRejectedExitLedger
open Part5OriginalH430PostRootRemainingExact

/-- The original (N^a)-cutoff first bad q factor, not the frozen one. -/
def frozenOnlyBad (N : ℕ) (z : TaggedReceiver) : ℕ :=
  firstBadPrime (arithmeticQuotientPrime z) ((N : ℝ)^a)

/-- The distinct actual root-dependent frozen-cutoff first bad q factor. -/
def rejectedFrozenBad (N n : ℕ) (tau : ℝ) (z : TaggedReceiver) : ℕ :=
  firstBadPrime (arithmeticQuotientPrime z)
    (frozenPrimeCutoff N n tau (arithmeticBand z) (arithmeticPrime z))

/-- Receipts failing the exact STRICT post-root prime-order carrier gate. -/
def outsideCarrier (S : Finset TaggedReceiver)
    (bad : TaggedReceiver → ℕ) (f : FirstExitDepthState ℕ) :
    Finset TaggedReceiver :=
  S.filter (fun z => ¬ (bad z : ℝ) < (f.selectedPrefix.headD 0 : ℝ))

/-- Receipts in the physical next-candidate carrier whose Rosser prefix
is retained at THIS frontier, not first-excluded at this transition. -/
def policyPass (S : Finset TaggedReceiver)
    (bad : TaggedReceiver → ℕ) (lower : Bool) (Q : ℝ)
    (f : FirstExitDepthState ℕ) : Finset TaggedReceiver :=
  S.filter (fun z =>
    (bad z : ℝ) < (f.selectedPrefix.headD 0 : ℝ) ∧
    ordinaryRosserPrefixAdmissible lower Q (bad z :: f.selectedPrefix))

/-- The third lane consists of ACTUAL post-root candidates whose
ordinary Rosser test fails at this precise selected prefix. -/
def policyFail (S : Finset TaggedReceiver)
    (bad : TaggedReceiver → ℕ) (lower : Bool) (Q : ℝ)
    (f : FirstExitDepthState ℕ) : Finset TaggedReceiver :=
  S.filter (fun z =>
    (bad z : ℝ) < (f.selectedPrefix.headD 0 : ℝ) ∧
    ¬ordinaryRosserPrefixAdmissible lower Q (bad z :: f.selectedPrefix))

/-- Every original tagged receipt belongs to exactly one physical /
Rosser gate lane. This is not a count-to-historical-weight identity. -/
theorem three_lane_union (S : Finset TaggedReceiver)
    (bad : TaggedReceiver → ℕ) (lower : Bool) (Q : ℝ)
    (f : FirstExitDepthState ℕ) :
    S = outsideCarrier S bad f ∪
      (policyPass S bad lower Q f ∪ policyFail S bad lower Q f) := by
  classical
  ext z
  simp [outsideCarrier, policyPass, policyFail] <;> tauto

private theorem outside_disjoint (S : Finset TaggedReceiver)
    (bad : TaggedReceiver → ℕ) (lower : Bool) (Q : ℝ)
    (f : FirstExitDepthState ℕ) :
    Disjoint (outsideCarrier S bad f)
      (policyPass S bad lower Q f ∪ policyFail S bad lower Q f) := by
  apply Finset.disjoint_left.mpr
  intro z hout hin
  have hn := (Finset.mem_filter.mp hout).2
  rcases Finset.mem_union.mp hin with hp | hf
  · exact hn (Finset.mem_filter.mp hp).2.1
  · exact hn (Finset.mem_filter.mp hf).2.1

private theorem policy_disjoint (S : Finset TaggedReceiver)
    (bad : TaggedReceiver → ℕ) (lower : Bool) (Q : ℝ)
    (f : FirstExitDepthState ℕ) :
    Disjoint (policyPass S bad lower Q f)
      (policyFail S bad lower Q f) := by
  apply Finset.disjoint_left.mpr
  intro z hp hf
  exact (Finset.mem_filter.mp hf).2.2 (Finset.mem_filter.mp hp).2.2

/-- Exact integer receipt counts: no q, overlapping band tag or
unmatched Rosser candidate is deleted. -/
theorem three_lane_card (S : Finset TaggedReceiver)
    (bad : TaggedReceiver → ℕ) (lower : Bool) (Q : ℝ)
    (f : FirstExitDepthState ℕ) :
    S.card =
      (outsideCarrier S bad f).card +
      (policyPass S bad lower Q f).card +
      (policyFail S bad lower Q f).card := by
  rw [three_lane_union S bad lower Q f]
  rw [Finset.card_union_of_disjoint (outside_disjoint S bad lower Q f)]
  rw [Finset.card_union_of_disjoint (policy_disjoint S bad lower Q f)] <;> omega

/-- Exact signed sum before ANY attempt to assign an historical
owner or replace the original root-count weight. The same weight
function is evaluated once at every original tagged receipt. -/
theorem three_lane_signed (S : Finset TaggedReceiver)
    (bad : TaggedReceiver → ℕ) (lower : Bool) (Q : ℝ)
    (f : FirstExitDepthState ℕ) (w : TaggedReceiver → ℝ) :
    (∑ z ∈ S, w z) =
      (∑ z ∈ outsideCarrier S bad f, w z) +
      (∑ z ∈ policyPass S bad lower Q f, w z) +
      (∑ z ∈ policyFail S bad lower Q f, w z) := by
  rw [three_lane_union S bad lower Q f]
  rw [Finset.sum_union (outside_disjoint S bad lower Q f)]
  rw [Finset.sum_union (policy_disjoint S bad lower Q f)] <;> ring

/-- ORIGINAL U3/U4 strict-sieve rejections, not arbitrary tagged inputs:
six distinct physical/policy lanes with all integer receipt
multiplicities intact. A frontier is fixed but NOT assumed to be
the selected-history owner of every receiver. -/
theorem original_rejected_six_lane_card
    (N n : ℕ) (tau : ℝ) (hN : 2 ≤ N)
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384)
    (lower : Bool) (Q : ℝ) (f : FirstExitDepthState ℕ) :
    (rejectedOriginal N).card =
      (outsideCarrier (frozenOnly N n tau) (frozenOnlyBad N) f).card +
      (policyPass (frozenOnly N n tau) (frozenOnlyBad N) lower Q f).card +
      (policyFail (frozenOnly N n tau) (frozenOnlyBad N) lower Q f).card +
      (outsideCarrier (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) f).card +
      (policyPass (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) lower Q f).card +
      (policyFail (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) lower Q f).card := by
  have hsource := rejected_original_card_split N n tau hN htau htauhi hn
  have h1 := three_lane_card (frozenOnly N n tau) (frozenOnlyBad N) lower Q f
  have h2 := three_lane_card (rejectedFrozen N n tau)
    (rejectedFrozenBad N n tau) lower Q f
  omega

/-- Complete ORIGINAL unsifted U3/U4 arithmetic count with six
explicit unpaid physical/Rosser exceptions. It reuses the literal
currentChenUpsilon3/U4 source identity; it does NOT turn those
exception cardinalities into feedback-history costs. -/
theorem raw_U34_six_exception_counts
    (N n : ℕ) (tau : ℝ) (hN : 2 ≤ N)
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384)
    (lower : Bool) (Q : ℝ) (f : FirstExitDepthState ℕ) :
    ((rawTagged N).card : ℝ) =
      currentChenUpsilon3 N + currentChenUpsilon4 N +
      ((outsideCarrier (frozenOnly N n tau) (frozenOnlyBad N) f).card : ℝ) +
      ((policyPass (frozenOnly N n tau) (frozenOnlyBad N) lower Q f).card : ℝ) +
      ((policyFail (frozenOnly N n tau) (frozenOnlyBad N) lower Q f).card : ℝ) +
      ((outsideCarrier (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) f).card : ℝ) +
      ((policyPass (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) lower Q f).card : ℝ) +
      ((policyFail (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) lower Q f).card : ℝ) := by
  have hraw := raw_U34_plus_two_rejections N n tau hN htau htauhi hn
  have hf := three_lane_card (frozenOnly N n tau) (frozenOnlyBad N) lower Q f
  have hr := three_lane_card (rejectedFrozen N n tau)
    (rejectedFrozenBad N n tau) lower Q f
  have hfc : ((frozenOnly N n tau).card : ℝ) =
      ((outsideCarrier (frozenOnly N n tau) (frozenOnlyBad N) f).card : ℝ) +
      ((policyPass (frozenOnly N n tau) (frozenOnlyBad N) lower Q f).card : ℝ) +
      ((policyFail (frozenOnly N n tau) (frozenOnlyBad N) lower Q f).card : ℝ) := by
    exact_mod_cast hf
  have hrc : ((rejectedFrozen N n tau).card : ℝ) =
      ((outsideCarrier (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) f).card : ℝ) +
      ((policyPass (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) lower Q f).card : ℝ) +
      ((policyFail (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) lower Q f).card : ℝ) := by
    exact_mod_cast hr
  rw [hfc, hrc] at hraw
  linarith

/-- Six-way signed conservation on the ACTUAL original rejection set.
This exposes both UNPAID out-of-carrier and policy-passing masses;
the event-bearing terms do not silently absorb them. -/
theorem original_rejected_six_lane_signed
    (N n : ℕ) (tau : ℝ) (hN : 2 ≤ N)
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384)
    (lower : Bool) (Q : ℝ) (f : FirstExitDepthState ℕ)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ rejectedOriginal N, w z) =
      (∑ z ∈ outsideCarrier (frozenOnly N n tau) (frozenOnlyBad N) f, w z) +
      (∑ z ∈ policyPass (frozenOnly N n tau) (frozenOnlyBad N) lower Q f, w z) +
      (∑ z ∈ policyFail (frozenOnly N n tau) (frozenOnlyBad N) lower Q f, w z) +
      (∑ z ∈ outsideCarrier (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) f, w z) +
      (∑ z ∈ policyPass (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) lower Q f, w z) +
      (∑ z ∈ policyFail (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau) lower Q f, w z) := by
  classical
  rw [rejected_original_partition N n tau hN htau htauhi hn]
  rw [Finset.sum_union (frozen_only_disjoint_rejected N n tau)]
  rw [three_lane_signed (frozenOnly N n tau) (frozenOnlyBad N) lower Q f w]
  rw [three_lane_signed (rejectedFrozen N n tau)
    (rejectedFrozenBad N n tau) lower Q f w]
  ring

/-- A receiver assigned to the frozenOnly OUTSIDE lane really is
absent from the original post-root remaining carrier; there is
no invented historical owner for that receipt. -/
theorem frozen_outside_not_remaining
    (N n cap k : ℕ) (hk : 0 < k) (tau z0 : ℝ)
    (parent : Bool → List ℕ → Bool) (f : FirstExitDepthState ℕ)
    (hfrontier : f ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    {z : TaggedReceiver}
    (hz : z ∈ outsideCarrier (frozenOnly N n tau) (frozenOnlyBad N) f) :
    frozenOnlyBad N z ∉ f.remaining := by
  intro hm
  have h := Finset.mem_filter.mp hz
  exact h.2 ((frozen_only_bad_post_root_remaining_iff
    N n cap k hk tau z0 parent f hfrontier h.1).1 hm)

/-- Distinct frozen-rejected cutoff, identical exact out-of-carrier
argument on the genuine raw quotient. -/
theorem rejected_outside_not_remaining
    (N n cap k : ℕ) (hk : 0 < k) (tau z0 : ℝ)
    (parent : Bool → List ℕ → Bool) (f : FirstExitDepthState ℕ)
    (hfrontier : f ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    {z : TaggedReceiver}
    (hz : z ∈ outsideCarrier (rejectedFrozen N n tau)
      (rejectedFrozenBad N n tau) f) :
    rejectedFrozenBad N n tau z ∉ f.remaining := by
  intro hm
  have h := Finset.mem_filter.mp hz
  exact h.2 ((rejected_frozen_bad_post_root_remaining_iff
    N n cap k hk tau z0 parent f hfrontier h.1).1 hm)

/-- Every frozenOnly receipt in the FAILED lane has a literal
historical event. Order and Rosser failure are derived from its
CLASSIFIED ORIGINAL receipt rather than hypothesized per receiver.
The event witness need not be unique across different q receipts. -/
theorem frozen_failed_has_event
    (N n cap k : ℕ) (hk : 0 < k) (tau z0 Q : ℝ)
    (lower : Bool) (f : FirstExitDepthState ℕ)
    (hfrontier : f ∈ firstExitDepthFrontier k
      (ordinaryRosserRetainedPolicy lower Q)
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    {z : TaggedReceiver}
    (hz : z ∈ policyFail (frozenOnly N n tau)
      (frozenOnlyBad N) lower Q f) :
    ∃ event : FirstExitDepthState ℕ,
      event ∈ historicalRejectedEvents
        (ordinaryRosserRetainedPolicy lower Q)
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        f.selectedPrefix f.positive f.mass f.remaining ∧
      event.selectedPrefix = frozenOnlyBad N z :: f.selectedPrefix ∧
      event.positive = !f.positive ∧
      event.mass = f.mass * (1 / ((frozenOnlyBad N z : ℝ) - 1)) := by
  have h := Finset.mem_filter.mp hz
  exact frozen_only_bad_post_root_first_exit
    N n cap k hk tau z0 Q lower f hfrontier h.1 h.2.1 h.2.2

/-- The separate still-frozen-rejected FAIL lane has an actual
historical event with the original changed parity and local weight. -/
theorem rejected_failed_has_event
    (N n cap k : ℕ) (hk : 0 < k) (tau z0 Q : ℝ)
    (lower : Bool) (f : FirstExitDepthState ℕ)
    (hfrontier : f ∈ firstExitDepthFrontier k
      (ordinaryRosserRetainedPolicy lower Q)
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    {z : TaggedReceiver}
    (hz : z ∈ policyFail (rejectedFrozen N n tau)
      (rejectedFrozenBad N n tau) lower Q f) :
    ∃ event : FirstExitDepthState ℕ,
      event ∈ historicalRejectedEvents
        (ordinaryRosserRetainedPolicy lower Q)
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        f.selectedPrefix f.positive f.mass f.remaining ∧
      event.selectedPrefix = rejectedFrozenBad N n tau z :: f.selectedPrefix ∧
      event.positive = !f.positive ∧
      event.mass = f.mass *
        (1 / ((rejectedFrozenBad N n tau z : ℝ) - 1)) := by
  have h := Finset.mem_filter.mp hz
  exact rejected_frozen_bad_post_root_first_exit
    N n cap k hk tau z0 Q lower f hfrontier h.1 h.2.1 h.2.2

end
end ImbalancedChen.Part5OriginalH430HistoricalReceiverSixLanes
