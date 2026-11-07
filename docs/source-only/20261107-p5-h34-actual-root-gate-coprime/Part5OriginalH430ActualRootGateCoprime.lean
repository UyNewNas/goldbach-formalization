import ImbalancedChen.Part5OriginalH430EvenSignedExitBounds

/-!
P5.6 / h34 — actual original U3/U4 root-gate obstructions.

The original tagged (root-band,p,q) source supplies p.Prime and
p.Coprime N, separately in U3 and U4 even on their overlapping p bands.
Thus the nondivisibility component of rootLicensed is automatically
discharged for EVERY real frozenOnly or rejectedFrozen receipt.

The remaining gateBlocked receipts are partitioned DISJOINTLY by
failure of the actual root upper cutoff and failure of the genuine
singleton ordinary Rosser test AFTER passing that cutoff.

This sharpens the true six non-event lanes in the preceding signed
original-receiver ledger. Neither remaining gate failure is discarded,
and the actual signed rank-two Euler event remains an unpaid negative
correction. There is no fabricated selected/full/inherited owner,
root-weight equality or count-to-history payment.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430ActualRootGateCoprime

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedReceiverFibres
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430ReceiverRootGateAccounting
open Part5OriginalH430HistoricalReceiverSixLanes
open Part5OriginalH430HistoricalRejectedExitLedger
open Part5OriginalH430RealSignedExitPayment
open Part5OriginalH430TrueReceiverWeightedExit

/-- The actual raw source retains the original p prime and the
original coprimality test, not the quotient q's prime status. -/
theorem raw_root_prime_coprime (N : ℕ) {z : TaggedReceiver}
    (hz : z ∈ rawTagged N) :
    (arithmeticPrime z).Prime ∧
      Nat.Coprime (arithmeticPrime z) N := by
  cases z with
  | inl v =>
      have hv : v ∈ rawPairs N .U3 := by
        simpa [rawTagged] using hz
      simpa [arithmeticPrime] using
        (original_band_prime (Finset.mem_sigma.mp hv).1)
  | inr v =>
      have hv : v ∈ rawPairs N .U4 := by
        simpa [rawTagged] using hz
      simpa [arithmeticPrime] using
        (original_band_prime (Finset.mem_sigma.mp hv).1)

/-- A genuine original root p cannot divide N. This is proved from
the selected-prime source, not assumed as a gate licence. -/
theorem raw_root_not_target (N : ℕ) {z : TaggedReceiver}
    (hz : z ∈ rawTagged N) :
    ¬ arithmeticPrime z ∣ N := by
  intro hdiv
  obtain ⟨hp, hcop⟩ := raw_root_prime_coprime N hz
  have hcommon : arithmeticPrime z ∣
      Nat.gcd (arithmeticPrime z) N :=
    Nat.dvd_gcd (dvd_refl _) hdiv
  have hgcd : Nat.gcd (arithmeticPrime z) N = 1 := hcop
  rw [hgcd] at hcommon
  have hsmall : arithmeticPrime z ≤ 1 :=
    Nat.le_of_dvd (by decide) hcommon
  exact (not_le_of_gt hp.one_lt) hsmall

/-- For an actual raw U3/U4 receiver, the literal root licence has
EXACTLY the two remaining physical/policy tests. -/
theorem raw_root_licensed_iff (N : ℕ) (z0 Q : ℝ)
    (lower : Bool) {z : TaggedReceiver}
    (hz : z ∈ rawTagged N) :
    rootLicensed N z0 Q lower z ↔
      (arithmeticPrime z : ℝ) < z0 ∧
      ordinaryRosserPrefixAdmissible lower Q [arithmeticPrime z] := by
  have hnot := raw_root_not_target N hz
  simp [rootLicensed, hnot]

/-- An original receiver whose p is not strictly below the actual
root cutoff. It is NOT a historical first-excluded event. -/
def rootCutoffBlocked (S : Finset TaggedReceiver) (z0 : ℝ) :
    Finset TaggedReceiver :=
  S.filter (fun z => ¬ (arithmeticPrime z : ℝ) < z0)

/-- An original receiver whose real root p is below z0 but whose
singleton ordinary Rosser prefix is not retained. -/
def rootPolicyBlocked (S : Finset TaggedReceiver)
    (z0 Q : ℝ) (lower : Bool) : Finset TaggedReceiver :=
  S.filter (fun z =>
    (arithmeticPrime z : ℝ) < z0 ∧
    ¬ ordinaryRosserPrefixAdmissible lower Q [arithmeticPrime z])

/-- No third N-divisibility root-gate failure is possible for a set
of genuine raw U3/U4 source positions. The two remaining lanes are
classified without identifying q/tag fibres. -/
theorem actual_root_gate_split
    (N : ℕ) (S : Finset TaggedReceiver)
    (hS : S ⊆ rawTagged N)
    (z0 Q : ℝ) (lower : Bool) :
    gateBlocked S N z0 Q lower =
      rootCutoffBlocked S z0 ∪ rootPolicyBlocked S z0 Q lower := by
  classical
  ext z
  simp only [gateBlocked, rootCutoffBlocked, rootPolicyBlocked,
    Finset.mem_filter, Finset.mem_union]
  by_cases hz : z ∈ S
  · simp only [hz, true_and]
    rw [raw_root_licensed_iff N z0 Q lower (hS hz)]
    tauto
  · simp [hz]

private theorem root_blockers_disjoint
    (S : Finset TaggedReceiver) (z0 Q : ℝ) (lower : Bool) :
    Disjoint (rootCutoffBlocked S z0)
      (rootPolicyBlocked S z0 Q lower) := by
  apply Finset.disjoint_left.mpr
  intro z hc hp
  exact (Finset.mem_filter.mp hc).2
    (Finset.mem_filter.mp hp).2.1

/-- Root gate failures have an exact count with genuine q/tag
multiplicity, and no divisibility-failure summand. -/
theorem actual_root_gate_card
    (N : ℕ) (S : Finset TaggedReceiver)
    (hS : S ⊆ rawTagged N)
    (z0 Q : ℝ) (lower : Bool) :
    (gateBlocked S N z0 Q lower).card =
      (rootCutoffBlocked S z0).card +
      (rootPolicyBlocked S z0 Q lower).card := by
  rw [actual_root_gate_split N S hS z0 Q lower]
  exact Finset.card_union_of_disjoint
    (root_blockers_disjoint S z0 Q lower)

/-- The classification also preserves arbitrary signed per-receiver
weights, not merely a positive or unit root mark. -/
theorem actual_root_gate_signed
    (N : ℕ) (S : Finset TaggedReceiver)
    (hS : S ⊆ rawTagged N)
    (z0 Q : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ gateBlocked S N z0 Q lower, w z) =
      (∑ z ∈ rootCutoffBlocked S z0, w z) +
      (∑ z ∈ rootPolicyBlocked S z0 Q lower, w z) := by
  rw [actual_root_gate_split N S hS z0 Q lower]
  exact Finset.sum_union (root_blockers_disjoint S z0 Q lower)

private theorem frozen_only_raw (N n : ℕ) (tau : ℝ) :
    frozenOnly N n tau ⊆ rawTagged N := by
  intro z hz
  exact frozen_tagged_subset_raw N n tau
    (Finset.mem_sdiff.mp hz).1

private theorem rejected_frozen_raw (N n : ℕ) (tau : ℝ) :
    rejectedFrozen N n tau ⊆ rawTagged N := by
  intro z hz
  exact (Finset.mem_sdiff.mp hz).1

/-- This is the ACTUAL original frozenOnly and rejectedFrozen source,
not an arbitrary surrogate receiver family. Both q-cutoff kinds stay
separate. -/
theorem original_two_source_gate_card
    (N n : ℕ) (tau z0 Q : ℝ) (lower : Bool) :
    (gateBlocked (frozenOnly N n tau) N z0 Q lower).card +
      (gateBlocked (rejectedFrozen N n tau) N z0 Q lower).card =
    (rootCutoffBlocked (frozenOnly N n tau) z0).card +
      (rootPolicyBlocked (frozenOnly N n tau) z0 Q lower).card +
      (rootCutoffBlocked (rejectedFrozen N n tau) z0).card +
      (rootPolicyBlocked (rejectedFrozen N n tau) z0 Q lower).card := by
  have hf := actual_root_gate_card N (frozenOnly N n tau)
    (frozen_only_raw N n tau) z0 Q lower
  have hr := actual_root_gate_card N (rejectedFrozen N n tau)
    (rejected_frozen_raw N n tau) z0 Q lower
  omega

/-- Signed, q/tag-dependent counterpart for both original rejected
sources. One receiver is counted exactly once in its own source. -/
theorem original_two_source_gate_signed
    (N n : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ gateBlocked (frozenOnly N n tau) N z0 Q lower, w z) +
      (∑ z ∈ gateBlocked (rejectedFrozen N n tau) N z0 Q lower, w z) =
    (∑ z ∈ rootCutoffBlocked (frozenOnly N n tau) z0, w z) +
      (∑ z ∈ rootPolicyBlocked (frozenOnly N n tau) z0 Q lower, w z) +
      (∑ z ∈ rootCutoffBlocked (rejectedFrozen N n tau) z0, w z) +
      (∑ z ∈ rootPolicyBlocked (rejectedFrozen N n tau) z0 Q lower, w z) := by
  rw [actual_root_gate_signed N (frozenOnly N n tau)
    (frozen_only_raw N n tau) z0 Q lower w]
  rw [actual_root_gate_signed N (rejectedFrozen N n tau)
    (rejected_frozen_raw N n tau) z0 Q lower w]
  ring

/-- Refined REAL six-lane non-event accounting: the two gateBlocked
lanes are now split into exact cutoff-failure and singleton-policy-
failure receipts. The other four non-event lanes remain explicit. -/
def refinedNonEventWeight (N n : ℕ) (tau z0 Q : ℝ)
    (lower : Bool) (w : TaggedReceiver → ℝ) : ℝ :=
  (∑ z ∈ rootCutoffBlocked (frozenOnly N n tau) z0, w z) +
  (∑ z ∈ rootPolicyBlocked (frozenOnly N n tau) z0 Q lower, w z) +
  (∑ z ∈ ownCarrierOutside (frozenOnly N n tau) (frozenOnlyBad N)
    N z0 Q lower, w z) +
  (∑ z ∈ ownPolicyPass (frozenOnly N n tau) (frozenOnlyBad N)
    N z0 Q lower, w z) +
  (∑ z ∈ rootCutoffBlocked (rejectedFrozen N n tau) z0, w z) +
  (∑ z ∈ rootPolicyBlocked (rejectedFrozen N n tau) z0 Q lower, w z) +
  (∑ z ∈ ownCarrierOutside (rejectedFrozen N n tau)
    (rejectedFrozenBad N n tau) N z0 Q lower, w z) +
  (∑ z ∈ ownPolicyPass (rejectedFrozen N n tau)
    (rejectedFrozenBad N n tau) N z0 Q lower, w z)

theorem refined_non_event_weight_eq
    (N n : ℕ) (tau z0 Q : ℝ) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    refinedNonEventWeight N n tau z0 Q lower w =
      fourthNonEventWeight N n tau z0 Q lower w := by
  have hf := actual_root_gate_signed N (frozenOnly N n tau)
    (frozen_only_raw N n tau) z0 Q lower w
  have hr := actual_root_gate_signed N (rejectedFrozen N n tau)
    (rejected_frozen_raw N n tau) z0 Q lower w
  dsimp [refinedNonEventWeight, fourthNonEventWeight]
  linarith

/-- Replace the genuine original rejection ledger's vague gateBlocked
terms by their two REAL outstanding physical/policy reasons. The signed
Euler correction is NOT treated as payment of positive receivers. -/
theorem original_rejected_refined_signed_gap
    (N n cap : ℕ) (tau z0 Q : ℝ)
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) (lower : Bool)
    (w : TaggedReceiver → ℝ) :
    (∑ z ∈ rejectedOriginal N, w z) =
      refinedNonEventWeight N n tau z0 Q lower w +
      (∑ key ∈ fourthDistinctKeys N n tau z0 Q lower,
        actualRankTwoSignedExit N cap lower Q key) +
      (∑ key ∈ fourthDistinctKeys N n tau z0 Q lower,
        fourthKeyReceipt N n tau z0 Q lower w key -
          actualRankTwoSignedExit N cap lower Q key) := by
  rw [refined_non_event_weight_eq]
  exact original_U34_rejected_weighted_signed_exit_gap
    N n cap tau z0 Q hN htau htauhi hn lower w

end
end ImbalancedChen.Part5OriginalH430ActualRootGateCoprime
