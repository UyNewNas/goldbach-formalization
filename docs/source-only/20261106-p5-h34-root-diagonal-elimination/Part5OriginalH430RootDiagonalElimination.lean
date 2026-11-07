import ImbalancedChen.Part5OriginalH430ReceiverRootGateAccounting

/-!
P5.6 / h34 — ORIGINAL U3/U4 selected-root diagonal exclusion.

The previous eight-lane ledger allowed a root-gate failure p ∣ N.
This is a meaningful potential count cost only if the ORIGINAL raw
arithmetic root selector allows such primes. It does not: each root
is selected from chenAdditivePrimeCarrier N, and the established
original_band_prime proves its coprimality with N.

This packet traces that fact through BOTH actual tagged raw source bands,
then removes ONLY the p ∣ N diagonal from the own-root gate accounting.
The real root upper cutoff p < z0 and singleton Rosser policy are
NOT inferred. All U3/U4 tags and original p,q occurrences remain.
No independent analytic input, global h34 count licence, or numerical
estimate is added.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430RootDiagonalElimination

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedReceiverFibres
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430ReceiverRootFrontier
open Part5OriginalH430ReceiverRootGateAccounting

/-- A raw (possibly composite-q) receiver has its selected p in the
literal original band matching its ORIGINAL U3 or U4 tag. -/
theorem raw_root_in_original_band {N : ℕ} {z : TaggedReceiver}
    (hz : z ∈ rawTagged N) :
    arithmeticPrime z ∈ originalBand N (arithmeticBand z) := by
  cases z with
  | inl x =>
      have hx : x ∈ rawPairs N .U3 := by
        simpa [rawTagged] using hz
      simpa [arithmeticPrime, arithmeticBand] using
        (Finset.mem_sigma.mp hx).1
  | inr x =>
      have hx : x ∈ rawPairs N .U4 := by
        simpa [rawTagged] using hz
      simpa [arithmeticPrime, arithmeticBand] using
        (Finset.mem_sigma.mp hx).1

/-- The ACTUAL raw U3/U4 root is prime and coprime to N.
This statement is sourced from the original selector rather than
asserted for an arbitrary historical candidate. -/
theorem raw_root_prime_coprime {N : ℕ} {z : TaggedReceiver}
    (hz : z ∈ rawTagged N) :
    (arithmeticPrime z).Prime ∧ (arithmeticPrime z).Coprime N :=
  original_band_prime (raw_root_in_original_band hz)

/-- The p ∣ N root diagonal is EMPTY in the original tagged source.
This is the missing physical-gate deduction: an additive P and
a quotient q are retained; no step identifies p with P or q. -/
theorem raw_root_not_dvd_target {N : ℕ} {z : TaggedReceiver}
    (hz : z ∈ rawTagged N) :
    ¬ arithmeticPrime z ∣ N := by
  intro hdiv
  have hp := (raw_root_prime_coprime hz).1
  have hcop : Nat.gcd (arithmeticPrime z) N = 1 :=
    (raw_root_prime_coprime hz).2
  have hcommon : arithmeticPrime z ∣
      Nat.gcd (arithmeticPrime z) N :=
    Nat.dvd_gcd (dvd_refl _) hdiv
  rw [hcop] at hcommon
  have hsmall : arithmeticPrime z ≤ 1 :=
    Nat.le_of_dvd (by decide) hcommon
  exact (not_le_of_gt hp.one_lt) hsmall

/-- The original frozen-only extra receiver does not create any
p-divides-N diagonal that could be charged to history. -/
theorem frozen_only_root_not_dvd_target
    (N n : ℕ) (tau : ℝ) {z : TaggedReceiver}
    (hz : z ∈ frozenOnly N n tau) :
    ¬ arithmeticPrime z ∣ N := by
  have hraw : z ∈ rawTagged N :=
    frozen_tagged_subset_raw N n tau (Finset.mem_sdiff.mp hz).1
  exact raw_root_not_dvd_target hraw

/-- The second, distinct rejection cutoff has the same root
coprimality, without equating its quotient to a prime. -/
theorem rejected_frozen_root_not_dvd_target
    (N n : ℕ) (tau : ℝ) {z : TaggedReceiver}
    (hz : z ∈ rejectedFrozen N n tau) :
    ¬ arithmeticPrime z ∣ N := by
  exact raw_root_not_dvd_target (Finset.mem_sdiff.mp hz).1

/-- RootLicensed on an ACTUAL raw receipt has exactly TWO remaining
tests, not three: physical strict upper cutoff and singleton Rosser
retention. Neither remaining test is proven here. -/
theorem root_licensed_iff_cutoff_and_rosser
    (N : ℕ) (z0 Q : ℝ) (lower : Bool)
    {z : TaggedReceiver} (hz : z ∈ rawTagged N) :
    rootLicensed N z0 Q lower z ↔
      (arithmeticPrime z : ℝ) < z0 ∧
      ordinaryRosserPrefixAdmissible lower Q [arithmeticPrime z] := by
  constructor
  · intro h
    exact ⟨h.2.1, h.2.2⟩
  · rintro ⟨hcut, hrosser⟩
    exact ⟨raw_root_not_dvd_target hz, hcut, hrosser⟩

/-- The zero diagonal statement holds for EVERY subfamily of the
original raw source, so the two cutoff-specific exception sets need
no extra finite count or target-divisor mass payment. -/
theorem root_dividing_filter_empty
    (N : ℕ) (S : Finset TaggedReceiver)
    (hS : S ⊆ rawTagged N) :
    S.filter (fun z => arithmeticPrime z ∣ N) = ∅ := by
  classical
  ext z
  simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false]
  intro h
  exact raw_root_not_dvd_target (hS h.1) h.2

/-- Exact replacement of the original gateBlocked filter on any
genuine raw-source subfamily. This is NOT an identification with the
selected/full/inherited count history. -/
theorem gate_blocked_eq_cutoff_or_rosser_failure
    (N : ℕ) (z0 Q : ℝ) (lower : Bool)
    (S : Finset TaggedReceiver)
    (hS : S ⊆ rawTagged N) :
    gateBlocked S N z0 Q lower =
      S.filter (fun z =>
        ¬ ((arithmeticPrime z : ℝ) < z0 ∧
          ordinaryRosserPrefixAdmissible lower Q
            [arithmeticPrime z])) := by
  classical
  ext z
  simp only [gateBlocked, Finset.mem_filter]
  constructor
  · rintro ⟨hz, hb⟩
    exact ⟨hz, fun hcp =>
      hb ((root_licensed_iff_cutoff_and_rosser
        N z0 Q lower (hS hz)).2 hcp)⟩
  · rintro ⟨hz, hb⟩
    exact ⟨hz, fun hl =>
      hb ((root_licensed_iff_cutoff_and_rosser
        N z0 Q lower (hS hz)).1 hl)⟩

/-- The first actual rejection lane now has NO target-divisor part.
Only real p<z0 and Rosser singleton obligations survive. -/
theorem frozen_gate_blocked_exact
    (N n : ℕ) (tau z0 Q : ℝ) (lower : Bool) :
    gateBlocked (frozenOnly N n tau) N z0 Q lower =
      (frozenOnly N n tau).filter (fun z =>
        ¬ ((arithmeticPrime z : ℝ) < z0 ∧
          ordinaryRosserPrefixAdmissible lower Q
            [arithmeticPrime z])) := by
  apply gate_blocked_eq_cutoff_or_rosser_failure
  intro z hz
  exact frozen_tagged_subset_raw N n tau (Finset.mem_sdiff.mp hz).1

/-- Different frozen cutoff, same literal original selected prime
coprimality and consequently no p ∣ N exception. -/
theorem rejected_gate_blocked_exact
    (N n : ℕ) (tau z0 Q : ℝ) (lower : Bool) :
    gateBlocked (rejectedFrozen N n tau) N z0 Q lower =
      (rejectedFrozen N n tau).filter (fun z =>
        ¬ ((arithmeticPrime z : ℝ) < z0 ∧
          ordinaryRosserPrefixAdmissible lower Q
            [arithmeticPrime z])) := by
  apply gate_blocked_eq_cutoff_or_rosser_failure
  intro z hz
  exact (Finset.mem_sdiff.mp hz).1

/-- Genuine rank-one root membership no longer needs a separately
assumed p∤N hypothesis for ORIGINAL U3/U4 receipts. The cap,
cutoff and singleton policy still must be proved at the right N,Q. -/
theorem raw_root_frontier_of_cutoff_and_rosser
    (N cap : ℕ) (z0 Q : ℝ) (lower : Bool)
    (hzcap : z0 ≤ (cap : ℝ))
    {z : TaggedReceiver} (hz : z ∈ rawTagged N)
    (hcut : (arithmeticPrime z : ℝ) < z0)
    (hrosser : ordinaryRosserPrefixAdmissible lower Q
      [arithmeticPrime z]) :
    receiverRootState N cap z ∈
      firstExitDepthFrontier 1 (ordinaryRosserRetainedPolicy lower Q)
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z0) := by
  exact raw_receiver_root_mem N cap z0 Q lower hzcap hz
    (raw_root_not_dvd_target hz) hcut hrosser

end
end ImbalancedChen.Part5OriginalH430RootDiagonalElimination
