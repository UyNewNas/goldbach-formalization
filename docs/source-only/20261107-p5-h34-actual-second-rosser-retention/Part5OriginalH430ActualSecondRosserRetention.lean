import ImbalancedChen.Part5OriginalH430OriginalSecondFactorWindow
import ImbalancedChen.Part5OriginalH430HistoricalPolicyGates

/-!
P5.6 / h34: actual second-rank ordinary Rosser admission of prime
factors of the ORIGINAL U3/U4 selected quotient.

Unlike the preceding enumerator-only packet, this packet tests the
literal SECOND ordinary Rosser prefix [ell,p] at the actual
tag/p-dependent physical Q. The first rank must already have passed
its own root policy. The integer quotient q is not identified with
a prime, and a common (p,ell) candidate is never charged once per q.

The final signed ledger keeps separate all original tagged q positions:
admitted second-rank factor, possible factor with no admitted second
rank, and no possible post-root factor. Root cutoff and root-policy
blockers remain separate. None is a completed historical owner or a
proved mass payment.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualSecondRosserRetention

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedReceiverFibres
open Part5OriginalH430OriginalSelectedRootFibres
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430ActualRootStageReceipts
open Part5OriginalH430StageZeroMassFibreGap
open Part5OriginalH430OriginalSecondFactorWindow
open Part5OriginalH430HistoricalPolicyGates

/-- A literal second enumerated candidate that passes the ACTUAL
ordinary policy at its new prefix. Both policy checks use the same
physical Q of this particular tagged original root. -/
def retainedOriginalSecond
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver) (ell : ℕ) : Prop :=
  ∃ c d : FirstExitDepthState ℕ,
    c ∈ firstExitNextSelectionCandidates
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0) ∧
    c.selectedPrefix = [arithmeticPrime z] ∧
    ordinaryRosserRetainedPolicy lower
      (originalPhysicalQ N precision tau z)
      c.positive c.selectedPrefix = true ∧
    d ∈ firstExitNextSelectionCandidates
      (fun r : ℕ => 1 / ((r : ℝ) - 1))
      c.selectedPrefix c.positive c.mass c.remaining ∧
    d.selectedPrefix = ell :: c.selectedPrefix ∧
    ordinaryRosserRetainedPolicy lower
      (originalPhysicalQ N precision tau z)
      d.positive d.selectedPrefix = true

/-- Exact missing second-rank policy test. For an ORIGINAL prime
divisor ell of q, the second candidate passes precisely when the
actual root is already admitted, ell is below p, and the full
ordinary Rosser [ell,p] test holds at this root's physical Q.
There is no permission to substitute one Q shared by U3/U4. -/
theorem retained_original_second_iff
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    {z : TaggedReceiver} (hz : z ∈ originalTagged N)
    {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ arithmeticQuotientPrime z) :
    retainedOriginalSecond N cap precision tau z0 lower z ell ↔
      selectedOriginalRootStage N cap precision tau z0 lower z ∧
      ell < arithmeticPrime z ∧
      ordinaryRosserPrefixAdmissible lower
        (originalPhysicalQ N precision tau z)
        [ell, arithmeticPrime z] := by
  constructor
  · rintro ⟨c, d, hc, hp, hroot, hd, hdpre, hsecond⟩
    have hpossible : possibleOriginalSecond
        N cap precision tau z0 lower z ell :=
      ⟨c, d, hc, hp, hroot, hd, hdpre⟩
    have hpair := (possible_original_second_iff
      N cap precision tau z0 lower hz hell hdiv).mp hpossible
    have hfinal : ordinaryRosserPrefixAdmissible lower
        (originalPhysicalQ N precision tau z) d.selectedPrefix := by
      apply of_decide_eq_true
      simpa only [ordinaryRosserRetainedPolicy] using hsecond
    exact ⟨hpair.1, hpair.2, by
      simpa only [hdpre, hp] using hfinal⟩
  · rintro ⟨hroot, hlt, hfinal⟩
    obtain ⟨c, d, hc, hp, hrootPolicy, hd, hdpre⟩ :=
      (possible_original_second_iff
        N cap precision tau z0 lower hz hell hdiv).mpr ⟨hroot, hlt⟩
    have hsecond : ordinaryRosserPrefixAdmissible lower
        (originalPhysicalQ N precision tau z) d.selectedPrefix := by
      simpa only [hdpre, hp] using hfinal
    refine ⟨c, d, hc, hp, hrootPolicy, hd, hdpre, ?_⟩
    simpa only [ordinaryRosserRetainedPolicy] using
      (decide_eq_true hsecond)

/-- The retained second candidate has the TRUE alternating sign
and multiplicative historical mass. It is not an independently
paid original q/tag receipt or a full/inherited owner. -/
theorem retained_second_real_sign_and_mass
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver) (ell : ℕ)
    (hret : retainedOriginalSecond
      N cap precision tau z0 lower z ell) :
    ∃ c d : FirstExitDepthState ℕ,
      c ∈ firstExitNextSelectionCandidates
        (fun r : ℕ => 1 / ((r : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z0) ∧
      c.selectedPrefix = [arithmeticPrime z] ∧
      d ∈ firstExitNextSelectionCandidates
        (fun r : ℕ => 1 / ((r : ℝ) - 1))
        c.selectedPrefix c.positive c.mass c.remaining ∧
      d.selectedPrefix = [ell, arithmeticPrime z] ∧
      ordinaryRosserRetainedPolicy lower
        (originalPhysicalQ N precision tau z)
        d.positive d.selectedPrefix = true ∧
      d.positive = true ∧
      d.mass = historicalFirstRootMass (arithmeticPrime z) *
        (1 / ((ell : ℝ) - 1)) := by
  obtain ⟨c, d, hc, hp, _hroot, hd, hdpre, hsecond⟩ := hret
  obtain ⟨hsign, hmass⟩ := second_candidate_true_mass_sign
    N cap z0 (arithmeticPrime z) ell c d hc hp hd hdpre
  refine ⟨c, d, hc, hp, hd, ?_, hsecond, hsign, hmass⟩
  simpa only [hp] using hdpre

/-- The genuine retained factor still lies in [N^a,p).
This statement combines the original q sieve, the TRUE ordered
history carrier, and the extra second Rosser policy test. -/
theorem retained_original_second_window_and_policy
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    {z : TaggedReceiver} (hz : z ∈ originalTagged N)
    {ell : ℕ} (hell : ell.Prime)
    (hdiv : ell ∣ arithmeticQuotientPrime z)
    (hret : retainedOriginalSecond
      N cap precision tau z0 lower z ell) :
    (N : ℝ) ^ Part5OriginalUpsilon5CausalDictionary.a ≤ (ell : ℝ) ∧
      (ell : ℝ) < (arithmeticPrime z : ℝ) ∧
      ordinaryRosserPrefixAdmissible lower
        (originalPhysicalQ N precision tau z)
        [ell, arithmeticPrime z] := by
  have h := (retained_original_second_iff
    N cap precision tau z0 lower hz hell hdiv).mp hret
  exact ⟨original_quotient_factor_lower N hz hell hdiv,
    by exact_mod_cast h.2.1, h.2.2⟩

/-- A second candidate at the same (U3,p,ell) is shared across
quotients: changing q never creates another historical selection. -/
theorem retained_U3_independent_of_quotient
    (N cap precision p q₁ q₂ ell : ℕ) (tau z0 : ℝ) (lower : Bool) :
    retainedOriginalSecond N cap precision tau z0 lower
      (Sum.inl (⟨p, q₁⟩ : TaggedPair)) ell ↔
    retainedOriginalSecond N cap precision tau z0 lower
      (Sum.inl (⟨p, q₂⟩ : TaggedPair)) ell := by
  simp [retainedOriginalSecond, originalPhysicalQ, arithmeticPrime]

/-- The analogous U4 fact uses its own physical Q, which must
not be silently identified with U3's Q on overlapping p bands. -/
theorem retained_U4_independent_of_quotient
    (N cap precision p q₁ q₂ ell : ℕ) (tau z0 : ℝ) (lower : Bool) :
    retainedOriginalSecond N cap precision tau z0 lower
      (Sum.inr (⟨p, q₁⟩ : TaggedPair)) ell ↔
    retainedOriginalSecond N cap precision tau z0 lower
      (Sum.inr (⟨p, q₂⟩ : TaggedPair)) ell := by
  simp [retainedOriginalSecond, originalPhysicalQ, arithmeticPrime]

/-- This existential is attached to one ORIGINAL tagged q receipt.
It does not pick an injective q-to-history owner. -/
def hasRetainedOriginalSecond
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver) : Prop :=
  ∃ ell : ℕ, ell.Prime ∧ ell ∣ arithmeticQuotientPrime z ∧
    retainedOriginalSecond N cap precision tau z0 lower z ell

/-- A retained q factor is necessarily geometrically eligible.
The converse is FALSE without the actual two-prime Rosser test. -/
theorem has_retained_second_implies_post_root_factor
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    {z : TaggedReceiver} (hz : z ∈ originalTagged N)
    (hret : hasRetainedOriginalSecond
      N cap precision tau z0 lower z) :
    hasPostRootPrimeFactor z := by
  obtain ⟨ell, hell, hdiv, hsecond⟩ := hret
  have h := (retained_original_second_iff
    N cap precision tau z0 lower hz hell hdiv).mp hsecond
  exact ⟨ell, hell, hdiv, h.2.1⟩

/-- No post-root prime divisor means no retained rank-two q factor.
In particular this receipt must stay in an unpaid complement. -/
theorem no_retained_second_of_no_post_root_factor
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    {z : TaggedReceiver} (hz : z ∈ originalTagged N)
    (hno : ¬ hasPostRootPrimeFactor z) :
    ¬ hasRetainedOriginalSecond N cap precision tau z0 lower z := by
  intro hret
  exact hno (has_retained_second_implies_post_root_factor
    N cap precision tau z0 lower hz hret)

/-- Exact q/tag-sensitive signed partition AFTER actual root admission.
Every original q position lies in exactly one of:
  (1) has at least one genuinely retained second prime factor;
  (2) has a geometrically possible factor, but none passes Rosser;
  (3) no geometrically possible factor.
A q with several factors stays ONE arithmetic receipt in (1).
No term is called paid history mass. -/
theorem stage_original_second_retention_signed_partition
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower), w z) =
    (∑ z ∈ (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower),
      if hasRetainedOriginalSecond N cap precision tau z0 lower z
        then w z else 0) +
    (∑ z ∈ (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower),
      if hasPostRootPrimeFactor z ∧
          ¬ hasRetainedOriginalSecond N cap precision tau z0 lower z
        then w z else 0) +
    (∑ z ∈ (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower),
      if ¬ hasPostRootPrimeFactor z then w z else 0) := by
  classical
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  have hzOriginal : z ∈ originalTagged N :=
    (Finset.mem_filter.mp hz).1
  by_cases hr : hasRetainedOriginalSecond N cap precision tau z0 lower z
  · have hf : hasPostRootPrimeFactor z :=
      has_retained_second_implies_post_root_factor
        N cap precision tau z0 lower hzOriginal hr
    simp [hr, hf]
  · by_cases hf : hasPostRootPrimeFactor z
    · simp [hr, hf]
    · simp [hr, hf]

/-- Entire ORIGINAL U3/U4 signed source, not just one historical root
mark, is partitioned into three post-root classes and the two
already-established root blockers. Every q and both tags survive.
The five terms are bookkeeping, not a count-to-history payment. -/
theorem original_count_source_five_unpaid_lanes
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ)) (w : TaggedReceiver → ℝ) :
    (∑ z ∈ originalTagged N, w z) =
    ((∑ z ∈ (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower),
      if hasRetainedOriginalSecond N cap precision tau z0 lower z
        then w z else 0) +
     (∑ z ∈ (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower),
      if hasPostRootPrimeFactor z ∧
          ¬ hasRetainedOriginalSecond N cap precision tau z0 lower z
        then w z else 0) +
     (∑ z ∈ (originalTagged N).filter
      (selectedOriginalRootStage N cap precision tau z0 lower),
      if ¬ hasPostRootPrimeFactor z then w z else 0)) +
    (∑ z ∈ rootCutoffBlocked (originalTagged N) z0, w z) +
    (∑ z ∈ physicalPolicyBlocked N precision tau z0 lower, w z) := by
  rw [actual_original_signed_with_historical_root_candidates
    N cap precision tau z0 lower hzcap w,
    stage_original_second_retention_signed_partition
      N cap precision tau z0 lower w]

end
end ImbalancedChen.Part5OriginalH430ActualSecondRosserRetention
