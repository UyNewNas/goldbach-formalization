import ImbalancedChen.Part5OriginalH430HistoricalRejectedExitLedger

/-!
P5.6 / h34: remove two REAL arithmetic obstructions to matching a
rejected U3/U4 quotient's first bad prime to the original historical
prime alphabet: divisibility of N and the finite enumeration cap.

The original unsifted quotient source contains q.Coprime N and q ≤ N.
Consequently every prime factor of q is prime to N and ≤ N.  This
is stronger than merely knowing that the factor divides N-P, and was
not used in the previous first-excluded event packet.

The physical universe membership requires the actual initial historical
upper cutoff z0 to dominate the rejection cutoff, and the actual finite
enumeration cap to exceed N.  NEITHER comparison is inferred for arbitrary
histories.  Membership in the initial historical alphabet is not membership
in an arbitrary post-root remaining suffix, nor does it imply a Rosser
retention or rejected-exit decision.

Preserves U3/U4, (p,P,q) tags, distinct frozenOnly/rejectedFrozen cutoffs
and original 1/(r-1) history weights. SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430QuotientBadPhysicalCarrier

noncomputable section
open scoped Classical
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430TaggedAdditivePrimeLabels
open Part5OriginalH430TaggedFirstBadPrimeOwner
open Part5OriginalH430HistoricalCandidateOrder

/-- This uses the ORIGINAL quotient source's coprimality, not the
generally false assertion that every factor of N-P is coprime to N. -/
theorem raw_quotient_factor_not_target
    {N ell : ℕ} {receiver : TaggedReceiver}
    (hr : receiver ∈ rawTagged N)
    (hprime : ell.Prime)
    (hdiv : ell ∣ arithmeticQuotientPrime receiver) :
    ¬ ell ∣ N := by
  intro hN
  have hdata := raw_quotient_data hr
  have hcommon : ell ∣ Nat.gcd (arithmeticQuotientPrime receiver) N :=
    Nat.dvd_gcd hdiv hN
  have hgcd : Nat.gcd (arithmeticQuotientPrime receiver) N = 1 :=
    hdata.2.2
  rw [hgcd] at hcommon
  have hle : ell ≤ 1 := Nat.le_of_dvd (by decide) hcommon
  exact (not_le_of_gt hprime.one_lt) hle

/-- The bad quotient prime is bounded by the ORIGINAL q≤N, not an
independently postulated historical cap or a root mark-one count. -/
theorem raw_quotient_factor_le_target
    {N ell : ℕ} {receiver : TaggedReceiver}
    (hr : receiver ∈ rawTagged N)
    (hdiv : ell ∣ arithmeticQuotientPrime receiver) :
    ell ≤ N := by
  have hdata := raw_quotient_data hr
  exact (Nat.le_of_dvd hdata.1 hdiv).trans hdata.2.1

/-- A genuine bad divisor of a raw quotient belongs to the ORIGINAL,
capped and N-excluding historical alphabet.  The TWO remaining physical
inequalities are stated explicitly; no post-root remaining claim is made. -/
theorem raw_bad_in_initial_historical_universe
    (N cap : ℕ) (z0 : ℝ) {receiver : TaggedReceiver}
    (hr : receiver ∈ rawTagged N) {ell : ℕ} {cut : ℝ}
    (hbad : BadPrime (arithmeticQuotientPrime receiver) cut ell)
    (hcap : N < cap) (hcut : cut ≤ z0) :
    ell ∈ roughPrimeUniverse N cap 0 z0 := by
  have hle := raw_quotient_factor_le_target hr hbad.2.1
  have hnot := raw_quotient_factor_not_target hr hbad.1 hbad.2.1
  exact (mem_roughPrimeUniverse).2
    ⟨lt_of_le_of_lt hle hcap, hbad.1, hnot,
     Nat.cast_nonneg _, lt_of_lt_of_le hbad.2.2 hcut⟩

/-- Original/frozen surplus: its first bad quotient factor cannot be an
N-divisor.  No cap or Rosser assumption is required for this exclusion. -/
theorem frozen_only_bad_not_target
    (N n : ℕ) (tau : ℝ) {receiver : TaggedReceiver}
    (hr : receiver ∈ frozenOnly N n tau) :
    ¬ firstBadPrime (arithmeticQuotientPrime receiver)
      ((N : ℝ)^a) ∣ N := by
  have hraw : receiver ∈ rawTagged N :=
    frozen_tagged_subset_raw N n tau (Finset.mem_sdiff.mp hr).1
  have hbad := (frozen_only_tagged_first_bad N n tau hr).1
  exact raw_quotient_factor_not_target hraw hbad.1 hbad.2.1

/-- Still rejected after freezing: the same target-exclusion is valid
at its DIFFERENT, root-dependent frozen physical cutoff. -/
theorem rejected_frozen_bad_not_target
    (N n : ℕ) (tau : ℝ) {receiver : TaggedReceiver}
    (hr : receiver ∈ rejectedFrozen N n tau) :
    ¬ firstBadPrime (arithmeticQuotientPrime receiver)
      (frozenPrimeCutoff N n tau (arithmeticBand receiver)
        (arithmeticPrime receiver)) ∣ N := by
  have hraw := (Finset.mem_sdiff.mp hr).1
  have hbad := rejected_frozen_tagged_first_bad N n tau hr
  exact raw_quotient_factor_not_target hraw hbad.1 hbad.2.1

/-- The frozenOnly lane has an actual root-history PRIME-CARRIER member
once the explicit original physical cap and z0 comparisons are paid. -/
theorem frozen_only_bad_in_initial_historical_universe
    (N n cap : ℕ) (tau z0 : ℝ)
    (hcap : N < cap) (hz0 : (N : ℝ)^a ≤ z0)
    {receiver : TaggedReceiver}
    (hr : receiver ∈ frozenOnly N n tau) :
    firstBadPrime (arithmeticQuotientPrime receiver) ((N : ℝ)^a) ∈
      roughPrimeUniverse N cap 0 z0 := by
  have hraw : receiver ∈ rawTagged N :=
    frozen_tagged_subset_raw N n tau (Finset.mem_sdiff.mp hr).1
  exact raw_bad_in_initial_historical_universe N cap z0 hraw
    (frozen_only_tagged_first_bad N n tau hr).1 hcap hz0

/-- This distinct lane uses exactly its own frozen cutoff and does NOT
pretend that it is the original N^a cutoff. -/
theorem rejected_frozen_bad_in_initial_historical_universe
    (N n cap : ℕ) (tau z0 : ℝ)
    (hcap : N < cap)
    {receiver : TaggedReceiver}
    (hr : receiver ∈ rejectedFrozen N n tau)
    (hz0 : frozenPrimeCutoff N n tau
      (arithmeticBand receiver) (arithmeticPrime receiver) ≤ z0) :
    firstBadPrime (arithmeticQuotientPrime receiver)
      (frozenPrimeCutoff N n tau (arithmeticBand receiver)
        (arithmeticPrime receiver)) ∈ roughPrimeUniverse N cap 0 z0 := by
  have hraw : receiver ∈ rawTagged N := (Finset.mem_sdiff.mp hr).1
  exact raw_bad_in_initial_historical_universe N cap z0 hraw
    (rejected_frozen_tagged_first_bad N n tau hr) hcap hz0

/-- A concrete PRE-ROOT next-selection occurrence, not merely an
arithmetic divisor. The actual root tree uses the original reciprocal
prime weight and opposite-parity next-selection state.  This does not
assert the policy admits it or an arbitrary post-root frontier retains it. -/
theorem frozen_only_bad_root_enumerated
    (N n cap : ℕ) (tau z0 : ℝ)
    (hcap : N < cap) (hz0 : (N : ℝ)^a ≤ z0)
    {receiver : TaggedReceiver}
    (hr : receiver ∈ frozenOnly N n tau) :
    ∃ candidate,
      candidate ∈ firstExitNextSelectionCandidates
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z0) ∧
      candidate.selectedPrefix =
        [firstBadPrime (arithmeticQuotientPrime receiver) ((N : ℝ)^a)] := by
  let root : FirstExitDepthState ℕ :=
    { selectedPrefix := [], positive := true, mass := 1,
      remaining := roughPrimeUniverse N cap 0 z0 }
  have hmem := frozen_only_bad_in_initial_historical_universe
    N n cap tau z0 hcap hz0 hr
  obtain ⟨candidate, hc, hpref⟩ :=
    (actual_next_candidate_iff
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) root
      (firstBadPrime (arithmeticQuotientPrime receiver) ((N : ℝ)^a))).1
      (show firstBadPrime (arithmeticQuotientPrime receiver)
        ((N : ℝ)^a) ∈ root.remaining from hmem)
  exact ⟨candidate, hc, hpref⟩

/-- Same literal pre-root enumeration for the still-rejected lane.
No U3/U4 tag, q occurrence, or cutoff has been identified away. -/
theorem rejected_frozen_bad_root_enumerated
    (N n cap : ℕ) (tau z0 : ℝ) (hcap : N < cap)
    {receiver : TaggedReceiver}
    (hr : receiver ∈ rejectedFrozen N n tau)
    (hz0 : frozenPrimeCutoff N n tau
      (arithmeticBand receiver) (arithmeticPrime receiver) ≤ z0) :
    ∃ candidate,
      candidate ∈ firstExitNextSelectionCandidates
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z0) ∧
      candidate.selectedPrefix = [firstBadPrime
        (arithmeticQuotientPrime receiver)
        (frozenPrimeCutoff N n tau (arithmeticBand receiver)
          (arithmeticPrime receiver))] := by
  let root : FirstExitDepthState ℕ :=
    { selectedPrefix := [], positive := true, mass := 1,
      remaining := roughPrimeUniverse N cap 0 z0 }
  have hmem := rejected_frozen_bad_in_initial_historical_universe
    N n cap tau z0 hcap hr hz0
  obtain ⟨candidate, hc, hpref⟩ :=
    (actual_next_candidate_iff
      (fun p : ℕ => 1 / ((p : ℝ) - 1)) root
      (firstBadPrime (arithmeticQuotientPrime receiver)
        (frozenPrimeCutoff N n tau (arithmeticBand receiver)
          (arithmeticPrime receiver)))).1
      (show firstBadPrime (arithmeticQuotientPrime receiver)
        (frozenPrimeCutoff N n tau (arithmeticBand receiver)
          (arithmeticPrime receiver)) ∈ root.remaining from hmem)
  exact ⟨candidate, hc, hpref⟩

end
end ImbalancedChen.Part5OriginalH430QuotientBadPhysicalCarrier
