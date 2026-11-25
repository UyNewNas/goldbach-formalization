import ImbalancedChen.Part5OriginalH430EventOccurrenceCapacity

/-!
P5.6 / h34: genuine rank-two signed first-exit correction vs
original U3/U4 arithmetic (tag,p,q) receipt weights.

One real (p,ell) historical event is not one event PER q, and its
payment is not the positive bare weight 1/(p-1)/(ell-1): it includes
the actual historical sign and the full remaining Euler product.
We expose its exact contribution and retain all remaining signed
difference and source-fibre/cross-lane multiplicities.

This is exact manuscript-internal accounting, not a positive payment
bound, full/selected/inherited owner, or count induction.
SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430RealSignedExitPayment

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430HistoricalRejectedExitLedger
open Part5OriginalH430ReceiverEventFibreWeights
open Part5OriginalH430EventOccurrenceCapacity
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedSourceRejections

/-- Only the genuinely immediate first-excluded event at [ell,p],
not deeper histories or a copied event for each arithmetic q. -/
def actualRankTwoHistory (N cap : ℕ) (lower : Bool)
    (Q : ℝ) (key : EventKey) : List (FirstExitDepthState ℕ) :=
  (historicalRejectedEvents
    (ordinaryRosserRetainedPolicy lower Q)
    (fun x : ℕ => 1 / ((x : ℝ) - 1))
    [key.1] false (1 / ((key.1 : ℝ) - 1))
    (roughPrimeUniverse N cap 0 (key.1 : ℝ))).filter
      (fun e => decide (e.selectedPrefix = [key.2, key.1]))

/-- Actual signed correction with literal Euler suffix. -/
def actualRankTwoSignedExit (N cap : ℕ) (lower : Bool)
    (Q : ℝ) (key : EventKey) : ℝ :=
  ((actualRankTwoHistory N cap lower Q key).map
    (historicalExitValue (fun x : ℕ => 1 / ((x : ℝ) - 1)))).sum

/-- The still-unpaid difference between a bare receipt and the actual
signed history correction; neither direction nor zero is assumed. -/
def actualRankTwoExitGap (N cap : ℕ) (lower : Bool)
    (Q : ℝ) (key : EventKey) : ℝ :=
  originalEventMass key - actualRankTwoSignedExit N cap lower Q key

private theorem singleton_of_member_length_one {α : Type*}
    (xs : List α) (e : α) (he : e ∈ xs)
    (hlen : xs.length = 1) : xs = [e] := by
  cases xs with
  | nil => cases he
  | cons x tail =>
      cases tail with
      | nil =>
          have h : e = x := by simpa using he
          subst x
          rfl
      | cons y ys =>
          simp only [List.length_cons] at hlen
          omega

/-- A key from EITHER real fourth rejection lane determines exactly
one rank-two event at its true fixed root, when z0 <= cap. -/
theorem original_fourth_lane_key_unique_signed_event
    (N n cap : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (key : EventKey)
    (hk : key ∈
      eventKeys
        (ownPolicyFail (frozenOnly N n tau) (frozenOnlyBad N)
          N z0 Q lower) (frozenOnlyBad N) ∪
      eventKeys
        (ownPolicyFail (rejectedFrozen N n tau)
          (rejectedFrozenBad N n tau) N z0 Q lower)
        (rejectedFrozenBad N n tau)) :
    ∃ event : FirstExitDepthState ℕ,
      actualRankTwoHistory N cap lower Q key = [event] ∧
      event.selectedPrefix = [key.2, key.1] ∧
      event.positive = true ∧
      event.mass = originalEventMass key := by
  rcases Finset.mem_union.mp hk with hf | hr
  · obtain ⟨event, hmem, hprefix, hpositive, hmass⟩ :=
      frozen_fail_key_has_historical_event
        N n cap tau z0 Q lower hzcap key hf
    have hlen : (actualRankTwoHistory N cap lower Q key).length = 1 := by
      simpa [actualRankTwoHistory] using
        (frozen_fail_key_exactly_one_rank_two_event
          N n cap tau z0 Q lower hzcap key hf)
    have hevent : event ∈ actualRankTwoHistory N cap lower Q key := by
      simp [actualRankTwoHistory, hmem, hprefix]
    refine ⟨event, singleton_of_member_length_one _ _ hevent hlen,
      hprefix, hpositive, hmass⟩
  · obtain ⟨event, hmem, hprefix, hpositive, hmass⟩ :=
      rejected_frozen_fail_key_has_historical_event
        N n cap tau z0 Q lower hzcap key hr
    have hlen : (actualRankTwoHistory N cap lower Q key).length = 1 := by
      simpa [actualRankTwoHistory] using
        (rejected_frozen_fail_key_exactly_one_rank_two_event
          N n cap tau z0 Q lower hzcap key hr)
    have hevent : event ∈ actualRankTwoHistory N cap lower Q key := by
      simp [actualRankTwoHistory, hmem, hprefix]
    refine ⟨event, singleton_of_member_length_one _ _ hevent hlen,
      hprefix, hpositive, hmass⟩

/-- The real rank-two correction is NEGATIVE bare mass times the
genuine remaining Euler product. Its suffix is read from the actual
event, not supplied by a different owner or replaced with one. -/
theorem original_fourth_lane_key_signed_euler_exact
    (N n cap : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (key : EventKey)
    (hk : key ∈
      eventKeys
        (ownPolicyFail (frozenOnly N n tau) (frozenOnlyBad N)
          N z0 Q lower) (frozenOnlyBad N) ∪
      eventKeys
        (ownPolicyFail (rejectedFrozen N n tau)
          (rejectedFrozenBad N n tau) N z0 Q lower)
        (rejectedFrozenBad N n tau)) :
    ∃ remaining : List ℕ,
      actualRankTwoSignedExit N cap lower Q key =
        -originalEventMass key *
          (remaining.map
            (fun q : ℕ => 1 - (1 / ((q : ℝ) - 1)))).prod := by
  obtain ⟨event, hsingleton, _, hpositive, hmass⟩ :=
    original_fourth_lane_key_unique_signed_event
      N n cap tau z0 Q lower hzcap key hk
  refine ⟨event.remaining, ?_⟩
  simp [actualRankTwoSignedExit, hsingleton,
    historicalExitValue, hpositive, hmass]

/-- Signed reindexing: one unique-key real correction plus its exact
signed discrepancy, across-lane overlap and within-lane q/tag excess.
These extra terms are NOT historical payments. -/
theorem two_source_signed_history_gap_ledger
    (N cap : ℕ) (lower : Bool) (Q : ℝ)
    (F R : Finset TaggedReceiver)
    (badF badR : TaggedReceiver → ℕ) :
    (∑ z ∈ F, originalEventMass (receiverEventKey badF z)) +
    (∑ z ∈ R, originalEventMass (receiverEventKey badR z)) =
    (∑ key ∈ eventKeys F badF ∪ eventKeys R badR,
      actualRankTwoSignedExit N cap lower Q key) +
    (∑ key ∈ eventKeys F badF ∪ eventKeys R badR,
      actualRankTwoExitGap N cap lower Q key) +
    (∑ key ∈ eventKeys F badF ∩ eventKeys R badR,
      originalEventMass key) +
    (∑ key ∈ eventKeys F badF,
      (excessReceipts F badF key : ℝ) * originalEventMass key) +
    (∑ key ∈ eventKeys R badR,
      (excessReceipts R badR key : ℝ) * originalEventMass key) := by
  classical
  have hf := signed_source_one_event_plus_excess F badF originalEventMass
  have hr := signed_source_one_event_plus_excess R badR originalEventMass
  have hkeys :
      (∑ key ∈ eventKeys F badF, originalEventMass key) +
      (∑ key ∈ eventKeys R badR, originalEventMass key) =
      (∑ key ∈ eventKeys F badF ∪ eventKeys R badR,
        originalEventMass key) +
      (∑ key ∈ eventKeys F badF ∩ eventKeys R badR,
        originalEventMass key) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_union_inter (eventKeys F badF)
        (eventKeys R badR) originalEventMass).symm
  have hreplace :
      (∑ key ∈ eventKeys F badF ∪ eventKeys R badR,
        originalEventMass key) =
      (∑ key ∈ eventKeys F badF ∪ eventKeys R badR,
        actualRankTwoSignedExit N cap lower Q key) +
      (∑ key ∈ eventKeys F badF ∪ eventKeys R badR,
        actualRankTwoExitGap N cap lower Q key) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro key _
    unfold actualRankTwoExitGap
    ring
  rw [hf, hr, hkeys, hreplace]
  ring

/-- The two original fourth-lane families; their real tags and distinct
bad-factor maps remain intact. -/
theorem original_fourth_lanes_signed_history_gap_ledger
    (N n cap : ℕ) (tau z0 Q : ℝ) (lower : Bool) :
    let F := ownPolicyFail (frozenOnly N n tau)
      (frozenOnlyBad N) N z0 Q lower
    let R := ownPolicyFail (rejectedFrozen N n tau)
      (rejectedFrozenBad N n tau) N z0 Q lower
    let KF := eventKeys F (frozenOnlyBad N)
    let KR := eventKeys R (rejectedFrozenBad N n tau)
    (∑ z ∈ F, originalEventMass
      (receiverEventKey (frozenOnlyBad N) z)) +
    (∑ z ∈ R, originalEventMass
      (receiverEventKey (rejectedFrozenBad N n tau) z)) =
    (∑ key ∈ KF ∪ KR,
      actualRankTwoSignedExit N cap lower Q key) +
    (∑ key ∈ KF ∪ KR,
      actualRankTwoExitGap N cap lower Q key) +
    (∑ key ∈ KF ∩ KR, originalEventMass key) +
    (∑ key ∈ KF,
      (excessReceipts F (frozenOnlyBad N) key : ℝ) *
        originalEventMass key) +
    (∑ key ∈ KR,
      (excessReceipts R (rejectedFrozenBad N n tau) key : ℝ) *
        originalEventMass key) := by
  dsimp
  exact two_source_signed_history_gap_ledger N cap lower Q
    (ownPolicyFail (frozenOnly N n tau)
      (frozenOnlyBad N) N z0 Q lower)
    (ownPolicyFail (rejectedFrozen N n tau)
      (rejectedFrozenBad N n tau) N z0 Q lower)
    (frozenOnlyBad N) (rejectedFrozenBad N n tau)

end
end ImbalancedChen.Part5OriginalH430RealSignedExitPayment
