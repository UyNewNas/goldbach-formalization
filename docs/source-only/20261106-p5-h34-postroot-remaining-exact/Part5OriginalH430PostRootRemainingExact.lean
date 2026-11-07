import ImbalancedChen.Part5OriginalH430QuotientBadPhysicalCarrier

/-!
P5.6 / h34: exact post-root carrier test for genuine U3/U4
quotient prime-factor obstructions.

A positive-rank first-exit frontier has a LAST selected prime. Its
remaining carrier has the ORIGINAL cap and target exclusions, but a
strict upper cutoff equal to that last selected prime. For a prime
factor of a GENUINE raw tagged quotient, primality and coprimality to N
are already proved from the original arithmetic source.

Consequently, at a real positive-rank frontier, membership in the
post-root remaining suffix is equivalent to being STRICTLY smaller
than the last selected prime. In particular no *extra* N<cap or
bad-cutoff<=z0 hypothesis is needed for this POST-ROOT implication.
This is NOT an assertion that the arithmetic receipt selects this
historical frontier or that Rosser actually rejects the next prefix.

Both original rejection lanes and conditional literal first-exit
certificates are carried separately. No owner injection, multiplicity
or rejection-mass payment is claimed.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430PostRootRemainingExact

noncomputable section
open scoped Classical
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430TaggedFirstBadPrimeOwner
open Part5OriginalH430HistoricalCandidateOrder
open Part5OriginalH430HistoricalRejectedExitLedger
open Part5OriginalH430QuotientBadPhysicalCarrier

/-- The exact missing post-root carrier test, for a prime factor of the
ORIGINAL (U3/U4,p,q) raw quotient. No cap or z0 comparison is requested:
the last selected prime is itself a member of the capped alphabet.
The frontier must have positive rank and be genuinely produced by the
original first-exit recursion. -/
theorem raw_factor_post_root_remaining_iff
    (N cap k : ℕ) (hk : 0 < k)
    (parent : Bool → List ℕ → Bool) (z0 : ℝ)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    {receiver : TaggedReceiver} (hr : receiver ∈ rawTagged N)
    {ell : ℕ} (hprime : ell.Prime)
    (hdiv : ell ∣ arithmeticQuotientPrime receiver) :
    ell ∈ frontier.remaining ↔
      (ell : ℝ) < (frontier.selectedPrefix.headD 0 : ℝ) := by
  obtain ⟨p, tail, hprefix, hpGlobal, hremaining⟩ :=
    mem_firstExitDepthFrontier_roughPrime_remaining
      k hk parent (fun p : ℕ => 1 / ((p : ℝ) - 1))
      N cap 0 z0 frontier hfrontier
  have hpData := (mem_roughPrimeUniverse).1 hpGlobal
  have hpCap : p < cap := hpData.1
  have hnotN : ¬ ell ∣ N :=
    raw_quotient_factor_not_target hr hprime hdiv
  constructor
  · intro hmem
    have hmember : ell ∈ roughPrimeUniverse N cap 0 (p : ℝ) := by
      simpa only [hremaining] using hmem
    have hless : (ell : ℝ) < (p : ℝ) :=
      mem_roughPrimeUniverse_upper hmember
    simpa [hprefix] using hless
  · intro hless
    have hlt : (ell : ℝ) < (p : ℝ) := by
      simpa [hprefix] using hless
    have hltNat : ell < p := by exact_mod_cast hlt
    have hmember : ell ∈ roughPrimeUniverse N cap 0 (p : ℝ) :=
      (mem_roughPrimeUniverse).2
        ⟨lt_trans hltNat hpCap, hprime, hnotN, Nat.cast_nonneg _, hlt⟩
    simpa only [hremaining] using hmember

/-- Exact original next-candidate enumeration at an actual positive-rank
frontier, not a naked existence statement for a divisor of N-P. The
candidate still has to pass the ORIGINAL policy separately. -/
theorem raw_factor_post_root_candidate_iff
    (N cap k : ℕ) (hk : 0 < k)
    (parent : Bool → List ℕ → Bool) (z0 : ℝ)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    {receiver : TaggedReceiver} (hr : receiver ∈ rawTagged N)
    {ell : ℕ} (hprime : ell.Prime)
    (hdiv : ell ∣ arithmeticQuotientPrime receiver) :
    (∃ candidate,
      candidate ∈ firstExitNextSelectionCandidates
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        frontier.selectedPrefix frontier.positive frontier.mass frontier.remaining ∧
      candidate.selectedPrefix = ell :: frontier.selectedPrefix) ↔
      (ell : ℝ) < (frontier.selectedPrefix.headD 0 : ℝ) := by
  calc
    _ ↔ ell ∈ frontier.remaining :=
      (actual_next_candidate_iff
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) frontier ell).symm
    _ ↔ _ := raw_factor_post_root_remaining_iff
      N cap k hk parent z0 frontier hfrontier hr hprime hdiv

/-- A failed strict order test is a genuine post-root carrier
obstruction, even when ell is prime and divides the raw quotient. -/
theorem raw_factor_not_post_root_of_order
    (N cap k : ℕ) (hk : 0 < k)
    (parent : Bool → List ℕ → Bool) (z0 : ℝ)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    {receiver : TaggedReceiver} (hr : receiver ∈ rawTagged N)
    {ell : ℕ} (hprime : ell.Prime)
    (hdiv : ell ∣ arithmeticQuotientPrime receiver)
    (hge : (frontier.selectedPrefix.headD 0 : ℝ) ≤ (ell : ℝ)) :
    ell ∉ frontier.remaining := by
  intro hmember
  have hlt := (raw_factor_post_root_remaining_iff
    N cap k hk parent z0 frontier hfrontier hr hprime hdiv).1 hmember
  exact (not_lt_of_ge hge) hlt

/-- The frozen-admitted but originally rejected source has its precise
first bad prime in the POST-ROOT remaining list exactly when that
prime is below the actual last selected historical prime. There is no
unproved N<cap or original-cutoff<=z0 premise in this result. -/
theorem frozen_only_bad_post_root_remaining_iff
    (N n cap k : ℕ) (hk : 0 < k)
    (tau z0 : ℝ) (parent : Bool → List ℕ → Bool)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    {receiver : TaggedReceiver} (hr : receiver ∈ frozenOnly N n tau) :
    firstBadPrime (arithmeticQuotientPrime receiver) ((N : ℝ)^a) ∈
      frontier.remaining ↔
    (firstBadPrime (arithmeticQuotientPrime receiver) ((N : ℝ)^a) : ℝ) <
      (frontier.selectedPrefix.headD 0 : ℝ) := by
  have hraw : receiver ∈ rawTagged N :=
    frozen_tagged_subset_raw N n tau (Finset.mem_sdiff.mp hr).1
  have hbad := (frozen_only_tagged_first_bad N n tau hr).1
  exact raw_factor_post_root_remaining_iff N cap k hk parent z0
    frontier hfrontier hraw hbad.1 hbad.2.1

/-- Distinct still-rejected source: use the ACTUAL root-dependent
frozen cutoff rather than silently substituting the original N^a. -/
theorem rejected_frozen_bad_post_root_remaining_iff
    (N n cap k : ℕ) (hk : 0 < k)
    (tau z0 : ℝ) (parent : Bool → List ℕ → Bool)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k parent
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    {receiver : TaggedReceiver} (hr : receiver ∈ rejectedFrozen N n tau) :
    firstBadPrime (arithmeticQuotientPrime receiver)
      (frozenPrimeCutoff N n tau (arithmeticBand receiver)
        (arithmeticPrime receiver)) ∈ frontier.remaining ↔
    (firstBadPrime (arithmeticQuotientPrime receiver)
      (frozenPrimeCutoff N n tau (arithmeticBand receiver)
        (arithmeticPrime receiver)) : ℝ) <
      (frontier.selectedPrefix.headD 0 : ℝ) := by
  have hraw : receiver ∈ rawTagged N :=
    (Finset.mem_sdiff.mp hr).1
  have hbad := rejected_frozen_tagged_first_bad N n tau hr
  exact raw_factor_post_root_remaining_iff N cap k hk parent z0
    frontier hfrontier hraw hbad.1 hbad.2.1

/-- If the literal post-root order holds and the ORIGINAL ordinary
Rosser prefix fails, a raw quotient prime factor produces an actual
historical first-excluded event with its exact sign, mass and suffix.
No arithmetic-receiver-to-event injection is inferred. -/
theorem raw_factor_post_root_rejected_event
    (N cap k : ℕ) (hk : 0 < k)
    (lower : Bool) (Q z0 : ℝ)
    (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k
      (ordinaryRosserRetainedPolicy lower Q)
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    {receiver : TaggedReceiver} (hr : receiver ∈ rawTagged N)
    {ell : ℕ} (hprime : ell.Prime)
    (hdiv : ell ∣ arithmeticQuotientPrime receiver)
    (horder : (ell : ℝ) < (frontier.selectedPrefix.headD 0 : ℝ))
    (hfailed : ¬ ordinaryRosserPrefixAdmissible lower Q
      (ell :: frontier.selectedPrefix)) :
    ordinaryRosserPrefixAdmissible lower Q frontier.selectedPrefix ∧
      ∃ before after,
        frontier.remaining = before ++ ell :: after ∧
        ({ selectedPrefix := ell :: frontier.selectedPrefix
           positive := !frontier.positive
           mass := frontier.mass * (1 / ((ell : ℝ) - 1))
           remaining := after } : FirstExitDepthState ℕ) ∈
          historicalRejectedEvents (ordinaryRosserRetainedPolicy lower Q)
            (fun p : ℕ => 1 / ((p : ℝ) - 1))
            frontier.selectedPrefix frontier.positive frontier.mass
            frontier.remaining := by
  have hremaining :=
    (raw_factor_post_root_remaining_iff N cap k hk
      (ordinaryRosserRetainedPolicy lower Q) z0 frontier
      hfrontier hr hprime hdiv).2 horder
  exact ordinary_frontier_first_excluded_event
    N cap k hk lower Q z0 frontier hfrontier hremaining hfailed

/-- Conditional first-exit event for the genuine frozenOnly first
bad quotient prime. This does not pay its signed arithmetic mass. -/
theorem frozen_only_bad_post_root_first_exit
    (N n cap k : ℕ) (hk : 0 < k) (tau z0 Q : ℝ)
    (lower : Bool) (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k
      (ordinaryRosserRetainedPolicy lower Q)
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    {receiver : TaggedReceiver} (hr : receiver ∈ frozenOnly N n tau)
    (horder : (firstBadPrime (arithmeticQuotientPrime receiver)
      ((N : ℝ)^a) : ℝ) < (frontier.selectedPrefix.headD 0 : ℝ))
    (hfailed : ¬ ordinaryRosserPrefixAdmissible lower Q
      (firstBadPrime (arithmeticQuotientPrime receiver) ((N : ℝ)^a) ::
        frontier.selectedPrefix)) :
    ∃ event : FirstExitDepthState ℕ,
      event ∈ historicalRejectedEvents (ordinaryRosserRetainedPolicy lower Q)
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        frontier.selectedPrefix frontier.positive frontier.mass
        frontier.remaining ∧
      event.selectedPrefix =
        firstBadPrime (arithmeticQuotientPrime receiver) ((N : ℝ)^a) ::
          frontier.selectedPrefix ∧
      event.positive = !frontier.positive ∧
      event.mass = frontier.mass *
        (1 / ((firstBadPrime (arithmeticQuotientPrime receiver)
          ((N : ℝ)^a) : ℝ) - 1)) := by
  have hraw : receiver ∈ rawTagged N :=
    frozen_tagged_subset_raw N n tau (Finset.mem_sdiff.mp hr).1
  have hbad := (frozen_only_tagged_first_bad N n tau hr).1
  obtain ⟨_, before, after, _, hexit⟩ :=
    raw_factor_post_root_rejected_event N cap k hk lower Q z0 frontier
      hfrontier hraw hbad.1 hbad.2.1 horder hfailed
  exact ⟨_, hexit, rfl, rfl, rfl⟩

/-- Separate certificate for the still-rejected actual frozen cutoff.
It preserves q and its root band, but does not identify event occurrence
multiplicity with the number of arithmetic receivers. -/
theorem rejected_frozen_bad_post_root_first_exit
    (N n cap k : ℕ) (hk : 0 < k) (tau z0 Q : ℝ)
    (lower : Bool) (frontier : FirstExitDepthState ℕ)
    (hfrontier : frontier ∈ firstExitDepthFrontier k
      (ordinaryRosserRetainedPolicy lower Q)
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0))
    {receiver : TaggedReceiver} (hr : receiver ∈ rejectedFrozen N n tau)
    (horder : (firstBadPrime (arithmeticQuotientPrime receiver)
      (frozenPrimeCutoff N n tau (arithmeticBand receiver)
        (arithmeticPrime receiver)) : ℝ) <
      (frontier.selectedPrefix.headD 0 : ℝ))
    (hfailed : ¬ ordinaryRosserPrefixAdmissible lower Q
      (firstBadPrime (arithmeticQuotientPrime receiver)
        (frozenPrimeCutoff N n tau (arithmeticBand receiver)
          (arithmeticPrime receiver)) :: frontier.selectedPrefix)) :
    ∃ event : FirstExitDepthState ℕ,
      event ∈ historicalRejectedEvents (ordinaryRosserRetainedPolicy lower Q)
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        frontier.selectedPrefix frontier.positive frontier.mass
        frontier.remaining ∧
      event.selectedPrefix =
        firstBadPrime (arithmeticQuotientPrime receiver)
          (frozenPrimeCutoff N n tau (arithmeticBand receiver)
            (arithmeticPrime receiver)) :: frontier.selectedPrefix ∧
      event.positive = !frontier.positive ∧
      event.mass = frontier.mass *
        (1 / ((firstBadPrime (arithmeticQuotientPrime receiver)
          (frozenPrimeCutoff N n tau (arithmeticBand receiver)
            (arithmeticPrime receiver)) : ℝ) - 1)) := by
  have hraw : receiver ∈ rawTagged N :=
    (Finset.mem_sdiff.mp hr).1
  have hbad := rejected_frozen_tagged_first_bad N n tau hr
  obtain ⟨_, before, after, _, hexit⟩ :=
    raw_factor_post_root_rejected_event N cap k hk lower Q z0 frontier
      hfrontier hraw hbad.1 hbad.2.1 horder hfailed
  exact ⟨_, hexit, rfl, rfl, rfl⟩

end
end ImbalancedChen.Part5OriginalH430PostRootRemainingExact
