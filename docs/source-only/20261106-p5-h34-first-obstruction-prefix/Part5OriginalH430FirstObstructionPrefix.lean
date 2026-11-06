import ImbalancedChen.Part5OriginalH430TaggedFirstBadPrimeOwner

/-!
P5.6 / h34: the exact ordered-prime PREFIX behind each actual
arithmetic first-obstruction certificate.

SOURCE ONLY / UNCOMPILED / ZERO KERNEL CREDIT.
This is the least prime factor of the integer quotient q, NOT an
identification with the full/selected/inherited causal-history owner.
The already-selected root p may precede it among factors of N-P.
-/
namespace ImbalancedChen.Part5OriginalH430FirstObstructionPrefix

noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedReceiverFibres
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430TaggedAdditivePrimeLabels
open Part5OriginalH430TaggedFirstBadPrimeOwner

/-- The actual first obstruction is the LEAST prime divisor of q,
not merely an arbitrary divisor below the physical cutoff. -/
theorem first_bad_le_every_prime_divisor {q : ℕ} {cut : ℝ}
    (hnot : ¬ ChenPrimeRough cut q) {r : ℕ}
    (hprime : r.Prime) (hdiv : r ∣ q) :
    firstBadPrime q cut ≤ r := by
  classical
  by_contra hle
  have hlt : r < firstBadPrime q cut := Nat.lt_of_not_ge hle
  have hx : (r : ℝ) < (firstBadPrime q cut : ℝ) := by
    exact_mod_cast hlt
  have hspec := first_bad_spec hnot
  have hr : BadPrime q cut r := ⟨hprime, hdiv, hx.trans hspec.2.2⟩
  have he := bad_exists_of_not_rough q cut hnot
  unfold firstBadPrime at hlt
  rw [dif_pos he] at hlt
  exact (Nat.find_min he hlt) hr

/-- The ordered prefix below the first obstruction has no prime
factor of q. This is the precise arithmetic-prefix statement. -/
theorem no_earlier_prime_divides {q : ℕ} {cut : ℝ}
    (hnot : ¬ ChenPrimeRough cut q) {r : ℕ}
    (hprime : r.Prime) (hdiv : r ∣ q)
    (hlt : r < firstBadPrime q cut) : False :=
  (Nat.not_lt_of_ge (first_bad_le_every_prime_divisor hnot hprime hdiv)) hlt

/-- The first obstruction is an exact threshold for the existing
strict roughness test, at EVERY real cutoff x (including equality).
No new sieve or smooth approximation is introduced. -/
theorem rough_iff_below_first_bad {q : ℕ} {cut : ℝ}
    (hnot : ¬ ChenPrimeRough cut q) (x : ℝ) :
    ChenPrimeRough x q ↔ x ≤ (firstBadPrime q cut : ℝ) := by
  constructor
  · intro hx
    have hb := first_bad_spec hnot
    exact hx _ hb.1 hb.2.1
  · intro hx r hp hd
    have hle := first_bad_le_every_prime_divisor hnot hp hd
    exact hx.trans (by exact_mod_cast hle)

/-- In particular, the original smaller-prime prefix passes the
actual strict test precisely at its first obstructing prime. -/
theorem rough_at_first_bad {q : ℕ} {cut : ℝ}
    (hnot : ¬ ChenPrimeRough cut q) :
    ChenPrimeRough (firstBadPrime q cut : ℝ) q :=
  (rough_iff_below_first_bad hnot _).2 le_rfl

/-- The owner does NOT depend on which cutoff first detects the
failure, as long as BOTH actual tests reject the same q. -/
theorem first_bad_cutoff_invariant {q : ℕ} {cut₁ cut₂ : ℝ}
    (h₁ : ¬ ChenPrimeRough cut₁ q)
    (h₂ : ¬ ChenPrimeRough cut₂ q) :
    firstBadPrime q cut₁ = firstBadPrime q cut₂ := by
  have hb₁ := first_bad_spec h₁
  have hb₂ := first_bad_spec h₂
  exact Nat.le_antisymm
    (first_bad_le_every_prime_divisor h₁ hb₂.1 hb₂.2.1)
    (first_bad_le_every_prime_divisor h₂ hb₁.1 hb₁.2.1)

/-- Cutoff monotonicity is stated at the REAL roughness predicate,
not by comparing unrelated request owners. -/
theorem fails_at_larger_cutoff {q : ℕ} {lo hi : ℝ}
    (hcut : lo ≤ hi) (hfail : ¬ ChenPrimeRough lo q) :
    ¬ ChenPrimeRough hi q := by
  intro hhi
  apply hfail
  intro r hp hd
  exact hcut.trans (hhi r hp hd)

/-- For two actual comparable cutoffs on a rejected quotient,
the least-factor owner is stable; the original source cutoff may be
inserted only after its inequality has been supplied by geometry. -/
theorem first_bad_ordered_cutoffs {q : ℕ} {lo hi : ℝ}
    (hcut : lo ≤ hi) (hfail : ¬ ChenPrimeRough lo q) :
    firstBadPrime q lo = firstBadPrime q hi :=
  first_bad_cutoff_invariant hfail (fails_at_larger_cutoff hcut hfail)

/-- Every actual frozen-only receiver has a single precise threshold
between the frozen physical cutoff and the original N^a cutoff.
The additive-prime P and quotient q are retained without identifying
either with a feedback-history occurrence. -/
theorem frozen_only_additive_prefix (N n : ℕ) (tau : ℝ)
    {z : TaggedReceiver} (hz : z ∈ frozenOnly N n tau) :
    additivePrimeLabel N z ∈ chenAdditivePrimeCarrier N ∧
    (N - additivePrimeLabel N z) / arithmeticPrime z =
      arithmeticQuotientPrime z ∧
    frozenPrimeCutoff N n tau (arithmeticBand z) (arithmeticPrime z) ≤
      (firstBadPrime (arithmeticQuotientPrime z) ((N : ℝ)^a) : ℝ) ∧
    (firstBadPrime (arithmeticQuotientPrime z) ((N : ℝ)^a) : ℝ) <
      (N : ℝ)^a ∧
    ∀ x : ℝ, ChenPrimeRough x (arithmeticQuotientPrime z) ↔
      x ≤ (firstBadPrime (arithmeticQuotientPrime z) ((N : ℝ)^a) : ℝ) := by
  have h := frozen_only_P_and_obstruction N n tau hz
  have hn := bad_implies_not_rough h.2.2.1
  exact ⟨h.1, h.2.1, h.2.2.2, h.2.2.1.2.2,
    fun x => rough_iff_below_first_bad hn x⟩

/-- A still-rejected receiver fails AT the physical frozen cutoff.
Its exact prefix threshold remains attached to the same (tag,p,P,q). -/
theorem rejected_frozen_additive_prefix (N n : ℕ) (tau : ℝ)
    {z : TaggedReceiver} (hz : z ∈ rejectedFrozen N n tau) :
    additivePrimeLabel N z ∈ chenAdditivePrimeCarrier N ∧
    (N - additivePrimeLabel N z) / arithmeticPrime z =
      arithmeticQuotientPrime z ∧
    (firstBadPrime (arithmeticQuotientPrime z)
      (frozenPrimeCutoff N n tau (arithmeticBand z) (arithmeticPrime z)) : ℝ) <
      frozenPrimeCutoff N n tau (arithmeticBand z) (arithmeticPrime z) ∧
    ∀ x : ℝ, ChenPrimeRough x (arithmeticQuotientPrime z) ↔
      x ≤ (firstBadPrime (arithmeticQuotientPrime z)
        (frozenPrimeCutoff N n tau (arithmeticBand z)
          (arithmeticPrime z)) : ℝ) := by
  have h := rejected_frozen_P_and_obstruction N n tau hz
  have hn := bad_implies_not_rough h.2.2
  exact ⟨h.1, h.2.1, h.2.2.2.2,
    fun x => rough_iff_below_first_bad hn x⟩

/-- Divisibility is transported through the ORIGINAL integer quotient,
not through the total feedback mark (whose initial weight is one). -/
theorem first_bad_divides_difference (N p P q : ℕ) {cut : ℝ}
    (hdiv : p ∣ N - P) (hquot : (N - P) / p = q)
    (hfail : ¬ ChenPrimeRough cut q) :
    firstBadPrime q cut ∣ N - P := by
  have hprod : p * q = N - P := by
    rw [← hquot]
    exact Nat.mul_div_cancel' hdiv
  obtain ⟨t, ht⟩ := (first_bad_spec hfail).2.1
  rw [← hprod, ht]
  exact ⟨p * t, by ac_rfl⟩

/-- Actual tagged raw receivers carry the divisibility needed above.
No prime status is falsely assigned to the integer quotient q. -/
theorem raw_label_divides (N : ℕ) {z : TaggedReceiver}
    (hz : z ∈ rawTagged N) :
    arithmeticPrime z ∣ N - additivePrimeLabel N z := by
  obtain ⟨P, hPc, hd, heq⟩ :=
    (raw_prime_fibre_iff N (arithmeticPrime z)
      (arithmeticQuotientPrime z)).mp (tagged_raw_quotient hz)
  have hPN : P < N := (mem_chenAdditivePrimeCarrier.mp hPc).1
  have hprod : arithmeticPrime z * arithmeticQuotientPrime z = N - P := by
    rw [← heq]
    exact Nat.mul_div_cancel' hd
  have hlabel : additivePrimeLabel N z = P := by
    unfold additivePrimeLabel
    rw [hprod]
    omega
  rwa [hlabel]

/-- The frozen rejection's first obstructing prime divides the ORIGINAL
N-P integer, but need not be its first divisor: the chosen root p may
occur earlier. Historical first-exit ownership is therefore still open. -/
theorem rejected_first_bad_divides_N_sub_P (N n : ℕ) (tau : ℝ)
    {z : TaggedReceiver} (hz : z ∈ rejectedFrozen N n tau) :
    firstBadPrime (arithmeticQuotientPrime z)
      (frozenPrimeCutoff N n tau (arithmeticBand z) (arithmeticPrime z)) ∣
      N - additivePrimeLabel N z := by
  have hr : z ∈ rawTagged N := (Finset.mem_sdiff.mp hz).1
  exact first_bad_divides_difference N (arithmeticPrime z)
    (additivePrimeLabel N z) (arithmeticQuotientPrime z)
    (raw_label_divides N hr) (raw_prime_label_data hr).2
    (bad_implies_not_rough (rejected_frozen_tagged_first_bad N n tau hz))

/-- The additional frozen-only receivers retain the same genuine
additive-prime difference, with the ORIGINAL strict test's owner. -/
theorem frozen_only_first_bad_divides_N_sub_P (N n : ℕ) (tau : ℝ)
    {z : TaggedReceiver} (hz : z ∈ frozenOnly N n tau) :
    firstBadPrime (arithmeticQuotientPrime z) ((N : ℝ)^a) ∣
      N - additivePrimeLabel N z := by
  have hr : z ∈ rawTagged N :=
    frozen_tagged_subset_raw N n tau (Finset.mem_sdiff.mp hz).1
  exact first_bad_divides_difference N (arithmeticPrime z)
    (additivePrimeLabel N z) (arithmeticQuotientPrime z)
    (raw_label_divides N hr) (raw_prime_label_data hr).2
    (bad_implies_not_rough (frozen_only_tagged_first_bad N n tau hz).1)

end
end ImbalancedChen.Part5OriginalH430FirstObstructionPrefix
