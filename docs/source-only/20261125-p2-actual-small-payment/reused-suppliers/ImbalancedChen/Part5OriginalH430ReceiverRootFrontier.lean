import ImbalancedChen.Part5OriginalH430HistoricalReceiverSixLanes
import ImbalancedChen.FirstExitFrontierInvariants

/-!
P5.6 / h34: a RECEIVER-DEPENDENT actual rank-one selected root.

The preceding six-lane audit uses one genuine but common arbitrary positive-
rank historical frontier. Here the ORIGINAL arithmetic receiver's own root
prime is inserted by the literal firstExitDepthFrontier recursion, provided
it belongs to the physical prime universe and passes the actual singleton
ordinary Rosser test. Its true post-root suffix is proved to be the capped,
target-deleted universe STRICTLY below that root. The parity is false and
the mass is the original reciprocal-prime root factor, not an invented
mark one.

The exact factor-in-suffix equivalence is then available for any prime
factor of the real raw U3/U4 quotient. Both original arithmetic rejection
lanes receive conditional event certificates at THEIR OWN root frontier,
with their different bad-factor cutoffs, exact parity and two reciprocal
factors. This is not a universal admission theorem: real cap, root
nondivisibility, root Rosser admission, strict bad-factor order and
post-root policy failure remain explicit physical/manuscript conditions.
There is no event injection, multiplicity payment or complete count bridge.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430ReceiverRootFrontier

noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430TaggedFirstBadPrimeOwner
open Part5OriginalH430HistoricalRejectedExitLedger
open Part5OriginalH430HistoricalReceiverSixLanes
open Part5OriginalH430PostRootRemainingExact

/-- The real rank-one state for THIS arithmetic receiver's actual selected
root. The cutoff is the root itself: the remainder is not an arbitrary
common frontier or the pre-root universe. -/
def receiverRootState (N cap : ℕ) (receiver : TaggedReceiver) :
    FirstExitDepthState ℕ :=
  { selectedPrefix := [arithmeticPrime receiver]
    positive := false
    mass := 1 / ((arithmeticPrime receiver : ℝ) - 1)
    remaining := roughPrimeUniverse N cap 0 (arithmeticPrime receiver : ℝ) }

/-- Literal rank-one reachability for one permitted root in an arbitrary
finite carrier. No replacement owner or assumed history is inserted. -/
private theorem rank_one_selected_occurrence {α : Type*}
    (policy : Bool → List α → Bool) (weight : α → ℝ)
    (carrier : List α) (p : α)
    (hp : p ∈ carrier) (hpass : policy false [p] = true) :
    ∃ suffix : List α,
      ({ selectedPrefix := [p], positive := false
         mass := weight p, remaining := suffix } : FirstExitDepthState α) ∈
        firstExitDepthFrontier 1 policy weight [] true 1 carrier := by
  induction carrier with
  | nil => cases hp
  | cons q qs ih =>
      rcases List.mem_cons.mp hp with hpq | hq
      · subst q
        refine ⟨qs, ?_⟩
        simp [firstExitDepthFrontier, hpass]
      · obtain ⟨suffix, htail⟩ := ih hq
        refine ⟨suffix, ?_⟩
        change ({ selectedPrefix := [p], positive := false
                  mass := weight p, remaining := suffix } :
                    FirstExitDepthState α) ∈
          (firstExitDepthFrontier 1 policy weight [] true 1 qs ++
            if policy false [q] = true then
              firstExitDepthFrontier 1 policy weight [q] false
                (1 * weight q) qs else [])
        exact List.mem_append_left _ htail

/-- This is the exact genuine first-exit rank-one state of the selected
arithmetic root, as soon as root carrier membership and its own original
ordinary Rosser test are established. The suffix equality is derived
from the actual frontier geometry, not stipulated as a new premise. -/
theorem receiver_root_mem_of_physical_and_policy
    (N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    {receiver : TaggedReceiver}
    (hcarrier : arithmeticPrime receiver ∈ roughPrimeUniverse N cap 0 z0)
    (hpolicy : ordinaryRosserPrefixAdmissible lower Q
      [arithmeticPrime receiver]) :
    receiverRootState N cap receiver ∈
      firstExitDepthFrontier 1 (ordinaryRosserRetainedPolicy lower Q)
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z0) := by
  let p := arithmeticPrime receiver
  let weight : ℕ → ℝ := fun q => 1 / ((q : ℝ) - 1)
  have htest : ordinaryRosserRetainedPolicy lower Q false [p] = true := by
    simp [ordinaryRosserRetainedPolicy, hpolicy]
  obtain ⟨suffix, hocc⟩ :=
    rank_one_selected_occurrence (ordinaryRosserRetainedPolicy lower Q)
      weight (roughPrimeUniverse N cap 0 z0) p hcarrier htest
  let f : FirstExitDepthState ℕ :=
    { selectedPrefix := [p], positive := false
      mass := weight p, remaining := suffix }
  have hf : f ∈ firstExitDepthFrontier 1
      (ordinaryRosserRetainedPolicy lower Q) weight
      [] true 1 (roughPrimeUniverse N cap 0 z0) := by
    simpa [f] using hocc
  obtain ⟨q, prefix, hprefix, _, hremaining⟩ :=
    mem_firstExitDepthFrontier_roughPrime_remaining
      1 (by decide) (ordinaryRosserRetainedPolicy lower Q) weight
      N cap 0 z0 f hf
  have hq : q = p := by
    have hEq : [p] = q :: prefix := by simpa [f] using hprefix
    exact (List.cons.inj hEq).1.symm
  subst q
  have hsuffix : suffix = roughPrimeUniverse N cap 0 (p : ℝ) := by
    simpa [f] using hremaining
  simpa [receiverRootState, f, p, weight, hsuffix] using hf

/-- Original U3/U4 root primality comes from the real tagged band.
Nondivisibility, the actual root cutoff and the singleton retained
policy are NOT deduced without proof: these are the explicit root
selection obligations, with cap fixed before the root. -/
theorem raw_receiver_root_mem
    (N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    {receiver : TaggedReceiver} (hraw : receiver ∈ rawTagged N)
    (hnotN : ¬ arithmeticPrime receiver ∣ N)
    (hcut : (arithmeticPrime receiver : ℝ) < z0)
    (hpolicy : ordinaryRosserPrefixAdmissible lower Q
      [arithmeticPrime receiver]) :
    receiverRootState N cap receiver ∈
      firstExitDepthFrontier 1 (ordinaryRosserRetainedPolicy lower Q)
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z0) := by
  have hroot : arithmeticPrime receiver ∈
      roughPrimeUniverse N cap 0 z0 :=
    (mem_roughPrimeUniverse_iff_of_cutoff_le_cap hzcap).2
      ⟨raw_tagged_root_prime hraw, hnotN, Nat.cast_nonneg _, hcut⟩
  exact receiver_root_mem_of_physical_and_policy
    N cap z0 Q lower hroot hpolicy

/-- Exact physical post-root suffix test at the RECEIVER'S OWN selected
prime, for every prime factor of its original q. The last prime in the
inequality is now the actual arithmetic p, not a caller-chosen frontier. -/
theorem raw_receiver_factor_in_root_suffix_iff
    (N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    {receiver : TaggedReceiver} (hraw : receiver ∈ rawTagged N)
    (hnotN : ¬ arithmeticPrime receiver ∣ N)
    (hcut : (arithmeticPrime receiver : ℝ) < z0)
    (hpolicy : ordinaryRosserPrefixAdmissible lower Q
      [arithmeticPrime receiver])
    {ell : ℕ} (hprime : ell.Prime)
    (hdiv : ell ∣ arithmeticQuotientPrime receiver) :
    ell ∈ (receiverRootState N cap receiver).remaining ↔
      (ell : ℝ) < (arithmeticPrime receiver : ℝ) := by
  have hfrontier := raw_receiver_root_mem N cap z0 Q lower
    hzcap hraw hnotN hcut hpolicy
  simpa [receiverRootState] using
    (raw_factor_post_root_remaining_iff N cap 1 (by decide)
      (ordinaryRosserRetainedPolicy lower Q) z0
      (receiverRootState N cap receiver) hfrontier hraw hprime hdiv)

/-- The strict original cutoff branch: at this receiver's actual
selected-root state, first-bad quotient membership is decided by
comparison with its own p, with no missing shared-frontier substitution. -/
theorem frozen_bad_in_own_root_suffix_iff
    (N n cap : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    {receiver : TaggedReceiver} (hr : receiver ∈ frozenOnly N n tau)
    (hnotN : ¬ arithmeticPrime receiver ∣ N)
    (hcut : (arithmeticPrime receiver : ℝ) < z0)
    (hpolicy : ordinaryRosserPrefixAdmissible lower Q
      [arithmeticPrime receiver]) :
    frozenOnlyBad N receiver ∈ (receiverRootState N cap receiver).remaining ↔
      (frozenOnlyBad N receiver : ℝ) < (arithmeticPrime receiver : ℝ) := by
  have hraw : receiver ∈ rawTagged N :=
    frozen_tagged_subset_raw N n tau (Finset.mem_sdiff.mp hr).1
  have hbad := (frozen_only_tagged_first_bad N n tau hr).1
  exact raw_receiver_factor_in_root_suffix_iff N cap z0 Q lower
    hzcap hraw hnotN hcut hpolicy hbad.1 hbad.2.1

/-- Separate frozen cutoff: do not replace the first bad factor by the
original N^a first factor when the frozen threshold differs. -/
theorem rejected_bad_in_own_root_suffix_iff
    (N n cap : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    {receiver : TaggedReceiver} (hr : receiver ∈ rejectedFrozen N n tau)
    (hnotN : ¬ arithmeticPrime receiver ∣ N)
    (hcut : (arithmeticPrime receiver : ℝ) < z0)
    (hpolicy : ordinaryRosserPrefixAdmissible lower Q
      [arithmeticPrime receiver]) :
    rejectedFrozenBad N n tau receiver ∈
      (receiverRootState N cap receiver).remaining ↔
      (rejectedFrozenBad N n tau receiver : ℝ) <
        (arithmeticPrime receiver : ℝ) := by
  have hraw : receiver ∈ rawTagged N := (Finset.mem_sdiff.mp hr).1
  have hbad := rejected_frozen_tagged_first_bad N n tau hr
  exact raw_receiver_factor_in_root_suffix_iff N cap z0 Q lower
    hzcap hraw hnotN hcut hpolicy hbad.1 hbad.2.1

/-- A frozenOnly receiver with a physically admissible root and a
strictly earlier quotient obstruction, whose new prefix REALLY fails the
Rosser test, has an actual history event at its OWN selected root.
Original sign is the second selection's positive parity and the mass
is the PRODUCT of two reciprocal-prime weights. No event injection. -/
theorem frozen_receiver_own_root_first_exit
    (N n cap : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    {receiver : TaggedReceiver} (hr : receiver ∈ frozenOnly N n tau)
    (hnotN : ¬ arithmeticPrime receiver ∣ N)
    (hcut : (arithmeticPrime receiver : ℝ) < z0)
    (hpolicy : ordinaryRosserPrefixAdmissible lower Q
      [arithmeticPrime receiver])
    (horder : (frozenOnlyBad N receiver : ℝ) <
      (arithmeticPrime receiver : ℝ))
    (hfailed : ¬ordinaryRosserPrefixAdmissible lower Q
      [frozenOnlyBad N receiver, arithmeticPrime receiver]) :
    ∃ event : FirstExitDepthState ℕ,
      event ∈ historicalRejectedEvents
        (ordinaryRosserRetainedPolicy lower Q)
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        [arithmeticPrime receiver] false
        (1 / ((arithmeticPrime receiver : ℝ) - 1))
        (roughPrimeUniverse N cap 0 (arithmeticPrime receiver : ℝ)) ∧
      event.selectedPrefix =
        [frozenOnlyBad N receiver, arithmeticPrime receiver] ∧
      event.positive = true ∧
      event.mass =
        (1 / ((arithmeticPrime receiver : ℝ) - 1)) *
          (1 / ((frozenOnlyBad N receiver : ℝ) - 1)) := by
  have hraw : receiver ∈ rawTagged N :=
    frozen_tagged_subset_raw N n tau (Finset.mem_sdiff.mp hr).1
  have hfrontier := raw_receiver_root_mem
    N cap z0 Q lower hzcap hraw hnotN hcut hpolicy
  have h := frozen_only_bad_post_root_first_exit
    N n cap 1 (by decide) tau z0 Q lower
    (receiverRootState N cap receiver) hfrontier hr
    (by simpa [receiverRootState] using horder)
    (by simpa [receiverRootState] using hfailed)
  simpa [receiverRootState] using h

/-- The other genuine U3/U4 rejection lane uses the different frozen
cutoff at the SAME receipt-dependent real selected-root history. -/
theorem rejected_receiver_own_root_first_exit
    (N n cap : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    {receiver : TaggedReceiver} (hr : receiver ∈ rejectedFrozen N n tau)
    (hnotN : ¬ arithmeticPrime receiver ∣ N)
    (hcut : (arithmeticPrime receiver : ℝ) < z0)
    (hpolicy : ordinaryRosserPrefixAdmissible lower Q
      [arithmeticPrime receiver])
    (horder : (rejectedFrozenBad N n tau receiver : ℝ) <
      (arithmeticPrime receiver : ℝ))
    (hfailed : ¬ordinaryRosserPrefixAdmissible lower Q
      [rejectedFrozenBad N n tau receiver, arithmeticPrime receiver]) :
    ∃ event : FirstExitDepthState ℕ,
      event ∈ historicalRejectedEvents
        (ordinaryRosserRetainedPolicy lower Q)
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        [arithmeticPrime receiver] false
        (1 / ((arithmeticPrime receiver : ℝ) - 1))
        (roughPrimeUniverse N cap 0 (arithmeticPrime receiver : ℝ)) ∧
      event.selectedPrefix =
        [rejectedFrozenBad N n tau receiver, arithmeticPrime receiver] ∧
      event.positive = true ∧
      event.mass =
        (1 / ((arithmeticPrime receiver : ℝ) - 1)) *
          (1 / ((rejectedFrozenBad N n tau receiver : ℝ) - 1)) := by
  have hraw : receiver ∈ rawTagged N :=
    (Finset.mem_sdiff.mp hr).1
  have hfrontier := raw_receiver_root_mem
    N cap z0 Q lower hzcap hraw hnotN hcut hpolicy
  have h := rejected_frozen_bad_post_root_first_exit
    N n cap 1 (by decide) tau z0 Q lower
    (receiverRootState N cap receiver) hfrontier hr
    (by simpa [receiverRootState] using horder)
    (by simpa [receiverRootState] using hfailed)
  simpa [receiverRootState] using h

end
end ImbalancedChen.Part5OriginalH430ReceiverRootFrontier
