import ImbalancedChen.Part5OriginalH430RealSignedExitPayment
import ImbalancedChen.Part5OriginalH430PhysicalSelectedRootQFibres
import ImbalancedChen.Part5OriginalH430UpperSignedSuffixDirection

/-!
P5.6 / h34 — original U3/U4 first-excluded receipt lanes at EACH
tag-and-root-specific physical Q; previous signed history comparison
accepted only a globally fixed Q.

The finite source remains the original q/tag receipt set, while the
historical rank-two correction has one event per physical (p,ell)
key, with the genuine remaining Euler product. No quotient q is
identified with a historical prime, no two tags are assigned equal
Q, and no event is automatically counted as paid.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualQFirstExitReceipts
noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430ReceiverRootGateAccounting
open Part5OriginalH430ReceiverEventFibreWeights
open Part5OriginalH430RealSignedExitPayment
open Part5OriginalH430ActualSignedEulerSuffix
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430UpperSignedSuffixDirection

/-- Genuine frozen-only original receipts eligible for rank-two
first-excluded histories at their OWN actual physical Q. -/
def frozenFailAtActualQ (N n precision : ℕ) (tau z0 : ℝ)
    (lower : Bool) : Finset TaggedReceiver :=
  (frozenOnly N n tau).filter (fun z =>
    z ∈ ownPolicyFail (frozenOnly N n tau) (frozenOnlyBad N)
      N z0 (originalPhysicalQ N precision tau z) lower)

/-- Separate frozen-cutoff rejection receipts; their bad-factor
function differs from the N^a frozen-only one. -/
def rejectedFailAtActualQ (N n precision : ℕ) (tau z0 : ℝ)
    (lower : Bool) : Finset TaggedReceiver :=
  (rejectedFrozen N n tau).filter (fun z =>
    z ∈ ownPolicyFail (rejectedFrozen N n tau)
      (rejectedFrozenBad N n tau)
      N z0 (originalPhysicalQ N precision tau z) lower)

/-- First genuinely forbidden prefix AND actual signed remaining
Euler product for a frozen-only receipt at ITS physical Q. The
singleton is a historical event, not a unique original q receipt. -/
theorem frozen_fail_actual_Q_unique_signed_first_exit
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (z : TaggedReceiver)
    (hz : z ∈ frozenFailAtActualQ N n precision tau z0 lower) :
    ∃ event : FirstExitDepthState ℕ,
      actualRankTwoHistory N cap lower
        (originalPhysicalQ N precision tau z)
        (receiverEventKey (frozenOnlyBad N) z) = [event] ∧
      event.selectedPrefix = [frozenOnlyBad N z, arithmeticPrime z] ∧
      event.positive = true ∧
      event.mass = originalEventMass
        (receiverEventKey (frozenOnlyBad N) z) ∧
      actualRankTwoSignedExit N cap lower
        (originalPhysicalQ N precision tau z)
        (receiverEventKey (frozenOnlyBad N) z) =
        -originalEventMass (receiverEventKey (frozenOnlyBad N) z) *
          (event.remaining.map
            (fun q : ℕ => 1 - (1 / ((q : ℝ) - 1)))).prod := by
  have hzfail : z ∈
      ownPolicyFail (frozenOnly N n tau) (frozenOnlyBad N)
        N z0 (originalPhysicalQ N precision tau z) lower :=
    (Finset.mem_filter.mp hz).2
  have hkey : receiverEventKey (frozenOnlyBad N) z ∈
      eventKeys
        (ownPolicyFail (frozenOnly N n tau) (frozenOnlyBad N)
          N z0 (originalPhysicalQ N precision tau z) lower)
        (frozenOnlyBad N) := by
    change receiverEventKey (frozenOnlyBad N) z ∈
      (ownPolicyFail (frozenOnly N n tau) (frozenOnlyBad N)
        N z0 (originalPhysicalQ N precision tau z) lower).image
          (receiverEventKey (frozenOnlyBad N))
    exact Finset.mem_image.mpr ⟨z, hzfail, rfl⟩
  have hunion : receiverEventKey (frozenOnlyBad N) z ∈
      eventKeys
        (ownPolicyFail (frozenOnly N n tau) (frozenOnlyBad N)
          N z0 (originalPhysicalQ N precision tau z) lower)
        (frozenOnlyBad N) ∪
      eventKeys
        (ownPolicyFail (rejectedFrozen N n tau)
          (rejectedFrozenBad N n tau)
          N z0 (originalPhysicalQ N precision tau z) lower)
        (rejectedFrozenBad N n tau) :=
    Finset.mem_union.mpr (Or.inl hkey)
  obtain ⟨event, hsingle, hprefix, hpositive, hmass⟩ :=
    original_fourth_lane_key_unique_signed_event
      N n cap tau z0 (originalPhysicalQ N precision tau z)
      lower hzcap (receiverEventKey (frozenOnlyBad N) z) hunion
  refine ⟨event, hsingle, ?_, hpositive, hmass, ?_⟩
  · simpa [receiverEventKey] using hprefix
  · simp [actualRankTwoSignedExit, hsingle, historicalExitValue,
      hpositive, hmass]

/-- The distinct second source has a different original bad-factor
function. It is matched separately at the true tag/p-dependent Q. -/
theorem rejected_fail_actual_Q_unique_signed_first_exit
    (N n cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (z : TaggedReceiver)
    (hz : z ∈ rejectedFailAtActualQ N n precision tau z0 lower) :
    ∃ event : FirstExitDepthState ℕ,
      actualRankTwoHistory N cap lower
        (originalPhysicalQ N precision tau z)
        (receiverEventKey (rejectedFrozenBad N n tau) z) = [event] ∧
      event.selectedPrefix =
        [rejectedFrozenBad N n tau z, arithmeticPrime z] ∧
      event.positive = true ∧
      event.mass = originalEventMass
        (receiverEventKey (rejectedFrozenBad N n tau) z) ∧
      actualRankTwoSignedExit N cap lower
        (originalPhysicalQ N precision tau z)
        (receiverEventKey (rejectedFrozenBad N n tau) z) =
        -originalEventMass
          (receiverEventKey (rejectedFrozenBad N n tau) z) *
          (event.remaining.map
            (fun q : ℕ => 1 - (1 / ((q : ℝ) - 1)))).prod := by
  have hzfail : z ∈
      ownPolicyFail (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau)
        N z0 (originalPhysicalQ N precision tau z) lower :=
    (Finset.mem_filter.mp hz).2
  have hkey : receiverEventKey (rejectedFrozenBad N n tau) z ∈
      eventKeys
        (ownPolicyFail (rejectedFrozen N n tau)
          (rejectedFrozenBad N n tau)
          N z0 (originalPhysicalQ N precision tau z) lower)
        (rejectedFrozenBad N n tau) := by
    change receiverEventKey (rejectedFrozenBad N n tau) z ∈
      (ownPolicyFail (rejectedFrozen N n tau)
        (rejectedFrozenBad N n tau)
        N z0 (originalPhysicalQ N precision tau z) lower).image
          (receiverEventKey (rejectedFrozenBad N n tau))
    exact Finset.mem_image.mpr ⟨z, hzfail, rfl⟩
  have hunion : receiverEventKey (rejectedFrozenBad N n tau) z ∈
      eventKeys
        (ownPolicyFail (frozenOnly N n tau) (frozenOnlyBad N)
          N z0 (originalPhysicalQ N precision tau z) lower)
        (frozenOnlyBad N) ∪
      eventKeys
        (ownPolicyFail (rejectedFrozen N n tau)
          (rejectedFrozenBad N n tau)
          N z0 (originalPhysicalQ N precision tau z) lower)
        (rejectedFrozenBad N n tau) :=
    Finset.mem_union.mpr (Or.inr hkey)
  obtain ⟨event, hsingle, hprefix, hpositive, hmass⟩ :=
    original_fourth_lane_key_unique_signed_event
      N n cap tau z0 (originalPhysicalQ N precision tau z)
      lower hzcap
      (receiverEventKey (rejectedFrozenBad N n tau) z) hunion
  refine ⟨event, hsingle, ?_, hpositive, hmass, ?_⟩
  · simpa [receiverEventKey] using hprefix
  · simp [actualRankTwoSignedExit, hsingle, historicalExitValue,
      hpositive, hmass]

/-- The actual-Q filters remain disjoint as original RECEIPTS.
They can still project to the SAME physical event key. -/
theorem actual_Q_two_fail_sources_disjoint
    (N n precision : ℕ) (tau z0 : ℝ) (lower : Bool) :
    Disjoint (frozenFailAtActualQ N n precision tau z0 lower)
      (rejectedFailAtActualQ N n precision tau z0 lower) := by
  apply Finset.disjoint_left.mpr
  intro z hfreeze hreject
  exact (Finset.disjoint_left.mp
    (frozen_only_disjoint_rejected N n tau))
    (Finset.mem_filter.mp hfreeze).1
    (Finset.mem_filter.mp hreject).1

/-- Sum arbitrary q/tag-dependent SIGNED receipt weights without
discarding duplicate physical keys or pretending their Euler events
are paid once per original q. -/
theorem actual_Q_two_fail_signed_source_split
    (N n precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ frozenFailAtActualQ N n precision tau z0 lower ∪
       rejectedFailAtActualQ N n precision tau z0 lower, w z) =
      (∑ z ∈ frozenFailAtActualQ N n precision tau z0 lower, w z) +
      (∑ z ∈ rejectedFailAtActualQ N n precision tau z0 lower, w z) := by
  exact Finset.sum_union
    (actual_Q_two_fail_sources_disjoint N n precision tau z0 lower)

/-- The previously proved GLOBAL upper Euler sign is also available
at this specific physical Q. It is NOT the sign of the isolated
rank-two event or the arithmetic/history mismatch. -/
theorem actual_Q_frozen_upper_global_suffix_nonneg
    (N n cap precision : ℕ) (tau z0 : ℝ) (z : TaggedReceiver)
    (_hz : z ∈ frozenFailAtActualQ N n precision tau z0 false)
    (hQ : 1 < originalPhysicalQ N precision tau z) :
    0 ≤ physicalFirstExcludedSuffix false N cap z0
      (originalPhysicalQ N precision tau z) :=
  physical_upper_first_excluded_suffix_nonneg
    N cap z0 (originalPhysicalQ N precision tau z) hQ

end
end ImbalancedChen.Part5OriginalH430ActualQFirstExitReceipts
