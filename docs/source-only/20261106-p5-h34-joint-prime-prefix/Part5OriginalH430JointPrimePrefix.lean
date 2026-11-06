import ImbalancedChen.Part5OriginalH430FirstObstructionPrefix

/-!
P5.6 / h34: the PRIME PREFIX OF THE COMPLETE ORIGINAL DIFFERENCE N-P,
not just the quotient q after the selected root p has been removed.

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The arithmetic least-factor owner below is NOT yet the manuscript's
causal full/selected/inherited first-excluded-history owner. In particular
no historical cap decision, sign, parity or multiplicity is asserted here.
Every arithmetic occurrence retains (U3/U4,p,P,q).
-/

namespace ImbalancedChen.Part5OriginalH430JointPrimePrefix
noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedReceiverFibres
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430TaggedAdditivePrimeLabels
open Part5OriginalH430TaggedFirstBadPrimeOwner
open Part5OriginalH430FirstObstructionPrefix

/-- Every raw arithmetic occurrence has its original selected prime p
in the original tagged root band. This holds even for rejected q. -/
theorem raw_tagged_band {N : ℕ} {z : TaggedReceiver}
    (hz : z ∈ rawTagged N) :
    arithmeticPrime z ∈ originalBand N (arithmeticBand z) := by
  cases z with
  | inl x =>
      have hx : x ∈ rawPairs N .U3 := by
        simpa [rawTagged] using hz
      exact (Finset.mem_sigma.mp hx).1
  | inr x =>
      have hx : x ∈ rawPairs N .U4 := by
        simpa [rawTagged] using hz
      exact (Finset.mem_sigma.mp hx).1

theorem raw_tagged_root_prime {N : ℕ} {z : TaggedReceiver}
    (hz : z ∈ rawTagged N) : (arithmeticPrime z).Prime :=
  (original_band_prime (raw_tagged_band hz)).1

/-- The actual raw receiver has EXACTLY N-P = p*q, before any
minimum-prime analysis. The integer division is the original one. -/
theorem raw_tagged_product {N : ℕ} {z : TaggedReceiver}
    (hz : z ∈ rawTagged N) :
    arithmeticPrime z * arithmeticQuotientPrime z =
      N - additivePrimeLabel N z := by
  have hdiv := raw_label_divides N hz
  have hquot := (raw_prime_label_data hz).2
  calc
    arithmeticPrime z * arithmeticQuotientPrime z =
      arithmeticPrime z *
        ((N - additivePrimeLabel N z) / arithmeticPrime z) := by
          rw [hquot]
    _ = N - additivePrimeLabel N z := Nat.mul_div_cancel' hdiv

/-- If p is prime and ell is the first prime factor of the actually
rejected q, then min(p,ell) is the least prime factor of p*q.
This is where the selected p is restored to the complete prefix.
No first-exit sieve policy is used or silently inferred. -/
theorem min_root_and_quotient_first_prime (p q : ℕ) (hp : p.Prime)
    {cut : ℝ} (hnot : ¬ ChenPrimeRough cut q) :
    (min p (firstBadPrime q cut)).Prime ∧
    min p (firstBadPrime q cut) ∣ p * q ∧
    (∀ r : ℕ, r.Prime → r ∣ p * q →
      min p (firstBadPrime q cut) ≤ r) := by
  have hb := first_bad_spec hnot
  rcases le_total p (firstBadPrime q cut) with hple | hlep
  · rw [min_eq_left hple]
    refine ⟨hp, ⟨q, rfl⟩, ?_⟩
    intro r hr hdiv
    rcases (hr.dvd_mul).mp hdiv with hpr | hqr
    · have heq : r = p :=
        (Nat.prime_dvd_prime_iff_eq hr hp).mp hpr
      exact heq.symm.le
    · exact hple.trans
        (first_bad_le_every_prime_divisor hnot hr hqr)
  · rw [min_eq_right hlep]
    refine ⟨hb.1, ?_, ?_⟩
    · obtain ⟨t, ht⟩ := hb.2.1
      refine ⟨p * t, ?_⟩
      rw [ht]
      ac_rfl
    · intro r hr hdiv
      rcases (hr.dvd_mul).mp hdiv with hpr | hqr
      · have heq : r = p :=
          (Nat.prime_dvd_prime_iff_eq hr hp).mp hpr
        exact hlep.trans heq.symm.le
      · exact first_bad_le_every_prime_divisor hnot hr hqr

/-- Explicit joint arithmetic candidate. It cannot be replaced by the
quotient owner when the selected root p is the earlier prime. -/
noncomputable def jointFirstPrime (z : TaggedReceiver) (cut : ℝ) : ℕ :=
  min (arithmeticPrime z)
    (firstBadPrime (arithmeticQuotientPrime z) cut)

/-- The joint candidate is genuinely the least prime divisor of
the same original N-P for EVERY raw (tag,p,P,q) receiver failing cut. -/
theorem joint_first_prime_spec (N : ℕ) {z : TaggedReceiver}
    (hz : z ∈ rawTagged N) {cut : ℝ}
    (hnot : ¬ ChenPrimeRough cut (arithmeticQuotientPrime z)) :
    (jointFirstPrime z cut).Prime ∧
    jointFirstPrime z cut ∣ N - additivePrimeLabel N z ∧
    (∀ r : ℕ, r.Prime → r ∣ N - additivePrimeLabel N z →
      jointFirstPrime z cut ≤ r) := by
  unfold jointFirstPrime
  rw [← raw_tagged_product hz]
  exact min_root_and_quotient_first_prime
    (arithmeticPrime z) (arithmeticQuotientPrime z)
    (raw_tagged_root_prime hz) hnot

/-- Literal strict prefix: no prime smaller than the joint candidate
divides the original N-P. It is not an assertion about which prefix the
historical retained/excluded tree admits. -/
theorem no_prime_before_joint_on_difference (N : ℕ)
    {z : TaggedReceiver} (hz : z ∈ rawTagged N) {cut : ℝ}
    (hnot : ¬ ChenPrimeRough cut (arithmeticQuotientPrime z))
    {r : ℕ} (hr : r.Prime) (hlt : r < jointFirstPrime z cut) :
    ¬ r ∣ N - additivePrimeLabel N z := by
  intro hdiv
  exact (Nat.not_lt_of_ge
    (joint_first_prime_spec N hz hnot).2.2 r hr hdiv) hlt

/-- Correct and exhaustive order split, with equality charged once
to the root-p case. It makes no claim that either case is selected. -/
theorem joint_owner_order_split (z : TaggedReceiver) (cut : ℝ) :
    (arithmeticPrime z ≤
        firstBadPrime (arithmeticQuotientPrime z) cut ∧
      jointFirstPrime z cut = arithmeticPrime z) ∨
    (firstBadPrime (arithmeticQuotientPrime z) cut <
        arithmeticPrime z ∧
      jointFirstPrime z cut =
        firstBadPrime (arithmeticQuotientPrime z) cut) := by
  by_cases h : arithmeticPrime z ≤
      firstBadPrime (arithmeticQuotientPrime z) cut
  · exact Or.inl ⟨h, by
      unfold jointFirstPrime
      exact min_eq_left h⟩
  · have hlt : firstBadPrime (arithmeticQuotientPrime z) cut <
        arithmeticPrime z := Nat.lt_of_not_ge h
    exact Or.inr ⟨hlt, by
      unfold jointFirstPrime
      exact min_eq_right hlt.le⟩

/-- When the original selected p is earlier, p is the first factor
of the full N-P. This DISAGREES with claiming ell is always the
historical first factor; the cap/filter owner remains to be shown. -/
theorem root_precedes_quotient_obstruction (N : ℕ)
    {z : TaggedReceiver} (hz : z ∈ rawTagged N) {cut : ℝ}
    (hnot : ¬ ChenPrimeRough cut (arithmeticQuotientPrime z))
    (hord : arithmeticPrime z ≤
      firstBadPrime (arithmeticQuotientPrime z) cut) :
    (arithmeticPrime z).Prime ∧
    arithmeticPrime z ∣ N - additivePrimeLabel N z ∧
    (∀ r : ℕ, r.Prime → r ∣ N - additivePrimeLabel N z →
      arithmeticPrime z ≤ r) := by
  have h := joint_first_prime_spec N hz hnot
  simpa [jointFirstPrime, min_eq_left hord] using h

/-- If the quotient's first obstructing prime comes before p,
it is the first factor of the full N-P, not merely of q. -/
theorem quotient_obstruction_precedes_root (N : ℕ)
    {z : TaggedReceiver} (hz : z ∈ rawTagged N) {cut : ℝ}
    (hnot : ¬ ChenPrimeRough cut (arithmeticQuotientPrime z))
    (hord : firstBadPrime (arithmeticQuotientPrime z) cut ≤
      arithmeticPrime z) :
    (firstBadPrime (arithmeticQuotientPrime z) cut).Prime ∧
    firstBadPrime (arithmeticQuotientPrime z) cut ∣
      N - additivePrimeLabel N z ∧
    (∀ r : ℕ, r.Prime → r ∣ N - additivePrimeLabel N z →
      firstBadPrime (arithmeticQuotientPrime z) cut ≤ r) := by
  have h := joint_first_prime_spec N hz hnot
  simpa [jointFirstPrime, min_eq_right hord] using h

/-- Original rejected, but frozen-admitted: keep the original cutoff,
actual physical tag, p, q and P. The joint divisor may be p rather
than the quotient's frozen-only first bad prime. -/
theorem frozen_only_joint_prime_spec (N n : ℕ) (tau : ℝ)
    {z : TaggedReceiver} (hz : z ∈ frozenOnly N n tau) :
    (jointFirstPrime z ((N : ℝ)^a)).Prime ∧
    jointFirstPrime z ((N : ℝ)^a) ∣ N - additivePrimeLabel N z ∧
    (∀ r : ℕ, r.Prime → r ∣ N - additivePrimeLabel N z →
      jointFirstPrime z ((N : ℝ)^a) ≤ r) := by
  have hr : z ∈ rawTagged N :=
    frozen_tagged_subset_raw N n tau (Finset.mem_sdiff.mp hz).1
  have hf := frozen_only_tagged_first_bad N n tau hz
  exact joint_first_prime_spec N hr (bad_implies_not_rough hf.1)

/-- Still rejected at the frozen physical cutoff. The same N-P
minimum divisor theorem applies with its ACTUAL frozen cutoff. -/
theorem rejected_frozen_joint_prime_spec (N n : ℕ) (tau : ℝ)
    {z : TaggedReceiver} (hz : z ∈ rejectedFrozen N n tau) :
    (jointFirstPrime z
      (frozenPrimeCutoff N n tau (arithmeticBand z)
        (arithmeticPrime z))).Prime ∧
    jointFirstPrime z
      (frozenPrimeCutoff N n tau (arithmeticBand z)
        (arithmeticPrime z)) ∣ N - additivePrimeLabel N z ∧
    (∀ r : ℕ, r.Prime → r ∣ N - additivePrimeLabel N z →
      jointFirstPrime z
        (frozenPrimeCutoff N n tau (arithmeticBand z)
          (arithmeticPrime z)) ≤ r) := by
  have hr : z ∈ rawTagged N := (Finset.mem_sdiff.mp hz).1
  have hf := rejected_frozen_tagged_first_bad N n tau hz
  exact joint_first_prime_spec N hr (bad_implies_not_rough hf)

/-- A prime STRICTLY before the complete difference's first factor
cannot occur in a frozen-only tagged receiver. -/
theorem frozen_only_joint_prefix_clear (N n : ℕ) (tau : ℝ)
    {z : TaggedReceiver} (hz : z ∈ frozenOnly N n tau)
    {r : ℕ} (hr : r.Prime)
    (hlt : r < jointFirstPrime z ((N : ℝ)^a)) :
    ¬ r ∣ N - additivePrimeLabel N z := by
  have hr : z ∈ rawTagged N :=
    frozen_tagged_subset_raw N n tau (Finset.mem_sdiff.mp hz).1
  have hf := frozen_only_tagged_first_bad N n tau hz
  exact no_prime_before_joint_on_difference N hr
    (bad_implies_not_rough hf.1) hr hlt

/-- A prime STRICTLY before the complete difference's first factor
also cannot occur in the still-rejected tagged receiver. -/
theorem rejected_frozen_joint_prefix_clear (N n : ℕ) (tau : ℝ)
    {z : TaggedReceiver} (hz : z ∈ rejectedFrozen N n tau)
    {r : ℕ} (hr : r.Prime)
    (hlt : r < jointFirstPrime z
      (frozenPrimeCutoff N n tau (arithmeticBand z)
        (arithmeticPrime z))) :
    ¬ r ∣ N - additivePrimeLabel N z := by
  have hraw : z ∈ rawTagged N := (Finset.mem_sdiff.mp hz).1
  have hf := rejected_frozen_tagged_first_bad N n tau hz
  exact no_prime_before_joint_on_difference N hraw
    (bad_implies_not_rough hf) hr hlt

end
end ImbalancedChen.Part5OriginalH430JointPrimePrefix
