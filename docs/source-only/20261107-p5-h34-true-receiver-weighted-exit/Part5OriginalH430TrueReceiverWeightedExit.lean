import ImbalancedChen.Part5OriginalH430RealSignedExitPayment

/-!
P5.6 / h34 — the real U3/U4 tagged quotient-receiver weights, not a
bare (p,ell) mass copied once for each q. Source-only candidate.

The previous signed Euler ledger grouped only the *bare event mass*
W(p,ell). Here every original tagged (U3/U4,p,q) receiver carries
its own arbitrary real weight, and all six genuine non-event lanes
are retained. In particular w := 1 gives the actual integer receiver
count, whereas another w may retain q-dependent coefficients.

Exactly ONE genuine historical first-excluded correction is charged
per distinct (p,ell) key. The difference is deliberately NOT called
paid: it includes all q/tag multiplicities, cross-lane overlap, and
the mismatch between unit/weighted arithmetic counts and the signed
Euler-product historical correction.

No full/selected/inherited owner, count-to-Theta inequality or h34
closure is assumed. SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430TrueReceiverWeightedExit

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430ReceiverRootGateAccounting
open Part5OriginalH430ReceiverEventFibreWeights
open Part5OriginalH430RealSignedExitPayment

/-- Both original, independently tagged, event-bearing fourth lanes.
The U3/U4 overlap and two different bad-factor cutoffs are preserved. -/
def fourthFrozenFail (N n : ℕ) (tau z0 Q : ℝ) (lower : Bool) :
    Finset TaggedReceiver :=
  ownPolicyFail (frozenOnly N n tau) (frozenOnlyBad N) N z0 Q lower

def fourthRejectedFail (N n : ℕ) (tau z0 Q : ℝ) (lower : Bool) :
    Finset TaggedReceiver :=
  ownPolicyFail (rejectedFrozen N n tau) (rejectedFrozenBad N n tau)
    N z0 Q lower

/-- A key is included ONCE even if both original lanes contain it. -/
def fourthDistinctKeys (N n : ℕ) (tau z0 Q : ℝ) (lower : Bool) :
    Finset EventKey :=
  eventKeys (fourthFrozenFail N n tau z0 Q lower) (frozenOnlyBad N) ∪
  eventKeys (fourthRejectedFail N n tau z0 Q lower)
    (rejectedFrozenBad N n tau)

/-- Exact source weight in a key, including every original q and tag.
An empty fibre contributes zero. -/
def fourthKeyReceipt (N n : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) (key : EventKey) : ℝ :=
  (∑ z ∈ eventFibre (fourthFrozenFail N n tau z0 Q lower)
      (frozenOnlyBad N) key, w z) +
  (∑ z ∈ eventFibre (fourthRejectedFail N n tau z0 Q lower)
      (rejectedFrozenBad N n tau) key, w z)

/-- The three non-event rejection lanes for each ACTUAL source:
root blocked, bad factor outside the true suffix, policy pass.
Their weights must not be booked as historical first-exit payments. -/
def fourthNonEventWeight (N n : ℕ) (tau z0 Q : ℝ)
    (lower : Bool) (w : TaggedReceiver → ℝ) : ℝ :=
  (∑ z ∈ gateBlocked (frozenOnly N n tau) N z0 Q lower, w z) +
  (∑ z ∈ ownCarrierOutside (frozenOnly N n tau) (frozenOnlyBad N)
      N z0 Q lower, w z) +
  (∑ z ∈ ownPolicyPass (frozenOnly N n tau) (frozenOnlyBad N)
      N z0 Q lower, w z) +
  (∑ z ∈ gateBlocked (rejectedFrozen N n tau) N z0 Q lower, w z) +
  (∑ z ∈ ownCarrierOutside (rejectedFrozen N n tau)
      (rejectedFrozenBad N n tau) N z0 Q lower, w z) +
  (∑ z ∈ ownPolicyPass (rejectedFrozen N n tau)
      (rejectedFrozenBad N n tau) N z0 Q lower, w z)

/-- An empty (p,ell) key fibre really has zero receiver count/weight.
This is not an assumption of injectivity. -/
private theorem fibre_empty_of_key_outside
    (S : Finset TaggedReceiver) (bad : TaggedReceiver → ℕ)
    (key : EventKey) (hkey : key ∉ eventKeys S bad) :
    eventFibre S bad key = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro z hz
  obtain ⟨hzS, hzkey⟩ := (mem_eventFibre_iff S bad key z).mp hz
  exact hkey (Finset.mem_image.mpr ⟨z, hzS, hzkey⟩)

/-- Reindex TWO original receiver sources over their union of keys,
counting noninjective fibres separately, and with arbitrary *signed,
q-dependent* weights. Neither common keys nor different q's are lost. -/
theorem two_source_true_weight_sum_by_keys
    (F R : Finset TaggedReceiver)
    (badF badR : TaggedReceiver → ℕ)
    (wF wR : TaggedReceiver → ℝ) :
    (∑ key ∈ eventKeys F badF ∪ eventKeys R badR,
       (∑ z ∈ eventFibre F badF key, wF z) +
       (∑ z ∈ eventFibre R badR key, wR z)) =
      (∑ z ∈ F, wF z) + (∑ z ∈ R, wR z) := by
  classical
  have hf :
      (∑ key ∈ eventKeys F badF,
        ∑ z ∈ eventFibre F badF key, wF z) =
      (∑ key ∈ eventKeys F badF ∪ eventKeys R badR,
        ∑ z ∈ eventFibre F badF key, wF z) := by
    apply Finset.sum_subset Finset.subset_union_left
    intro key _ hnot
    rw [fibre_empty_of_key_outside F badF key hnot]
    simp
  have hr :
      (∑ key ∈ eventKeys R badR,
        ∑ z ∈ eventFibre R badR key, wR z) =
      (∑ key ∈ eventKeys F badF ∪ eventKeys R badR,
        ∑ z ∈ eventFibre R badR key, wR z) := by
    apply Finset.sum_subset Finset.subset_union_right
    intro key _ hnot
    rw [fibre_empty_of_key_outside R badR key hnot]
    simp
  calc
    _ = (∑ key ∈ eventKeys F badF ∪ eventKeys R badR,
             ∑ z ∈ eventFibre F badF key, wF z) +
        (∑ key ∈ eventKeys F badF ∪ eventKeys R badR,
             ∑ z ∈ eventFibre R badR key, wR z) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ key ∈ eventKeys F badF,
             ∑ z ∈ eventFibre F badF key, wF z) +
        (∑ key ∈ eventKeys R badR,
             ∑ z ∈ eventFibre R badR key, wR z) := by
          rw [← hf, ← hr]
    _ = _ := by
          rw [sum_by_event_fibres, sum_by_event_fibres]

/-- EXACT signed history comparison with the original arbitrary
q/tag-dependent receiver weights. The per-key residual has NOT been
paid or bounded. Crucially the historical signed Euler correction
is included only ONCE per distinct key in the union. -/
theorem two_source_true_weight_signed_exit_gap
    (N cap : ℕ) (lower : Bool) (Q : ℝ)
    (F R : Finset TaggedReceiver)
    (badF badR : TaggedReceiver → ℕ)
    (wF wR : TaggedReceiver → ℝ) :
    (∑ z ∈ F, wF z) + (∑ z ∈ R, wR z) =
      (∑ key ∈ eventKeys F badF ∪ eventKeys R badR,
        actualRankTwoSignedExit N cap lower Q key) +
      (∑ key ∈ eventKeys F badF ∪ eventKeys R badR,
        ((∑ z ∈ eventFibre F badF key, wF z) +
         (∑ z ∈ eventFibre R badR key, wR z)) -
          actualRankTwoSignedExit N cap lower Q key) := by
  calc
    _ = (∑ key ∈ eventKeys F badF ∪ eventKeys R badR,
        ((∑ z ∈ eventFibre F badF key, wF z) +
         (∑ z ∈ eventFibre R badR key, wR z))) :=
      (two_source_true_weight_sum_by_keys F R badF badR wF wR).symm
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro key _
      ring

/-- Identifies the TRUE finite original U3/U4 rejected arithmetic
source with (a) six unchanged exceptional lanes; (b) exactly one
signed Euler first-exit term per DISTINCT key; and (c) an explicit
unpaid q/tag/cross-lane/signed-weight residual. No bare-mass
substitution or assumed historical owner occurs. All weights are
on original tagged receiver occurrences, not a generated root mark. -/
theorem original_U34_rejected_weighted_signed_exit_gap
    (N n cap : ℕ) (tau z0 Q : ℝ)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ rejectedOriginal N, w z) =
      fourthNonEventWeight N n tau z0 Q lower w +
      (∑ key ∈ fourthDistinctKeys N n tau z0 Q lower,
        actualRankTwoSignedExit N cap lower Q key) +
      (∑ key ∈ fourthDistinctKeys N n tau z0 Q lower,
        fourthKeyReceipt N n tau z0 Q lower w key -
          actualRankTwoSignedExit N cap lower Q key) := by
  have hexc := original_rejected_eight_lane_signed
    N n tau z0 Q hN htau htauhi hn lower w
  have hkeys := two_source_true_weight_signed_exit_gap
    N cap lower Q
    (fourthFrozenFail N n tau z0 Q lower)
    (fourthRejectedFail N n tau z0 Q lower)
    (frozenOnlyBad N) (rejectedFrozenBad N n tau) w w
  have hpart :
      (∑ z ∈ rejectedOriginal N, w z) =
      fourthNonEventWeight N n tau z0 Q lower w +
        ((∑ z ∈ fourthFrozenFail N n tau z0 Q lower, w z) +
         (∑ z ∈ fourthRejectedFail N n tau z0 Q lower, w z)) := by
    dsimp [fourthNonEventWeight, fourthFrozenFail, fourthRejectedFail]
    calc
      _ = _ := hexc
      _ = _ := by ring
  calc
    _ = fourthNonEventWeight N n tau z0 Q lower w +
        ((∑ z ∈ fourthFrozenFail N n tau z0 Q lower, w z) +
         (∑ z ∈ fourthRejectedFail N n tau z0 Q lower, w z)) := hpart
    _ = _ := by
      rw [hkeys]
      dsimp [fourthDistinctKeys, fourthKeyReceipt]
      ring

end
end ImbalancedChen.Part5OriginalH430TrueReceiverWeightedExit
