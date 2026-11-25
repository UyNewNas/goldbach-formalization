import ImbalancedChen.Part5OriginalH430TaggedAdditivePrimeLabels

/-! P5.6 / h34: exact prime-factor owner of a literal rejected quotient.
SOURCE ONLY / UNCOMPILED / ZERO KERNEL CREDIT.
This is not yet the manuscript full/selected/inherited history owner.
The quotient q is a positive integer, not necessarily prime. -/
namespace ImbalancedChen.Part5OriginalH430TaggedFirstBadPrimeOwner
noncomputable section
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedReceiverFibres
open Part5OriginalH430TaggedSourceRejections
open Part5OriginalH430TaggedAdditivePrimeLabels

def BadPrime (q : ℕ) (cut : ℝ) (ell : ℕ) : Prop :=
  ell.Prime ∧ ell ∣ q ∧ (ell : ℝ) < cut

/-- Failure of the actual strict roughness test gives a prime divisor
below the same actual cutoff. -/
theorem bad_exists_of_not_rough (q : ℕ) (cut : ℝ)
    (h : ¬ ChenPrimeRough cut q) : ∃ ell : ℕ, BadPrime q cut ell := by
  classical
  by_contra hn
  apply h
  intro ell hprime hdiv
  by_contra hcut
  apply hn
  exact ⟨ell, hprime, hdiv, lt_of_not_ge hcut⟩

theorem bad_implies_not_rough {q : ℕ} {cut : ℝ} {ell : ℕ}
    (h : BadPrime q cut ell) : ¬ ChenPrimeRough cut q := by
  intro hr
  exact (not_le_of_gt h.2.2) (hr ell h.1 h.2.1)

/-- The first prime-factor obstruction, selected deterministically
from actual q and actual cutoff. 0 is used only on admitted q. -/
noncomputable def firstBadPrime (q : ℕ) (cut : ℝ) : ℕ :=
  if h : ∃ ell : ℕ, BadPrime q cut ell then Nat.find h else 0

theorem first_bad_spec {q : ℕ} {cut : ℝ}
    (h : ¬ ChenPrimeRough cut q) :
    BadPrime q cut (firstBadPrime q cut) := by
  have he := bad_exists_of_not_rough q cut h
  unfold firstBadPrime
  rw [dif_pos he]
  exact Nat.find_spec he

/-- frozenOnly has an ORIGINAL first bad prime in the genuine
[frozen cutoff, original N^a cutoff) band. -/
theorem frozen_only_fibre_first_bad (N n : ℕ) (tau : ℝ)
    (k : Root) (p q : ℕ)
    (hf : q ∈ frozenReceiver N n tau k p)
    (ho : q ∉ originalReceiver N p) :
    BadPrime q ((N : ℝ)^a) (firstBadPrime q ((N : ℝ)^a)) ∧
    frozenPrimeCutoff N n tau k p ≤
      (firstBadPrime q ((N : ℝ)^a) : ℝ) := by
  have hf' : q ∈ (chenQuotientPrimeSource N p).filter
      (ChenPrimeRough (frozenPrimeCutoff N n tau k p)) := hf
  obtain ⟨hraw, hrough⟩ := Finset.mem_filter.mp hf'
  have hnot : ¬ ChenPrimeRough ((N : ℝ)^a) q := by
    intro hr
    apply ho
    exact Finset.mem_filter.mpr ⟨hraw, hr⟩
  have hb := first_bad_spec hnot
  exact ⟨hb, hrough _ hb.1 hb.2.1⟩

/-- rejectedFrozen has a prime divisor below the true frozen Q/max-two
cutoff; no original N^a cutoff has been substituted. -/
theorem rejected_frozen_fibre_first_bad (N n : ℕ) (tau : ℝ)
    (k : Root) (p q : ℕ)
    (hr : q ∈ chenQuotientPrimeSource N p)
    (hf : q ∉ frozenReceiver N n tau k p) :
    BadPrime q (frozenPrimeCutoff N n tau k p)
      (firstBadPrime q (frozenPrimeCutoff N n tau k p)) := by
  have hnot : ¬ ChenPrimeRough (frozenPrimeCutoff N n tau k p) q := by
    intro hrough
    apply hf
    exact Finset.mem_filter.mpr ⟨hr, hrough⟩
  exact first_bad_spec hnot

/-- Preserve the U3/U4 tag and original p while assigning the prime
factor to every surplus q. The two prime bands are not deduplicated. -/
theorem frozen_only_tagged_first_bad (N n : ℕ) (tau : ℝ)
    {z : TaggedReceiver} (hz : z ∈ frozenOnly N n tau) :
    BadPrime (arithmeticQuotientPrime z) ((N : ℝ)^a)
      (firstBadPrime (arithmeticQuotientPrime z) ((N : ℝ)^a)) ∧
    frozenPrimeCutoff N n tau (arithmeticBand z) (arithmeticPrime z) ≤
      (firstBadPrime (arithmeticQuotientPrime z) ((N : ℝ)^a) : ℝ) := by
  cases z with
  | inl x =>
      obtain ⟨p, q⟩ := x
      obtain ⟨_, hf, ho⟩ := (frozen_only_U3_iff N n p q tau).mp hz
      simpa [arithmeticQuotientPrime, arithmeticBand, arithmeticPrime] using
        (frozen_only_fibre_first_bad N n tau .U3 p q hf ho)
  | inr x =>
      obtain ⟨p, q⟩ := x
      obtain ⟨_, hf, ho⟩ := (frozen_only_U4_iff N n p q tau).mp hz
      simpa [arithmeticQuotientPrime, arithmeticBand, arithmeticPrime] using
        (frozen_only_fibre_first_bad N n tau .U4 p q hf ho)

/-- The still-rejected channel is owned by a prime below the frozen
cutoff, rather than the middle-band owner of frozenOnly. -/
theorem rejected_frozen_tagged_first_bad (N n : ℕ) (tau : ℝ)
    {z : TaggedReceiver} (hz : z ∈ rejectedFrozen N n tau) :
    BadPrime (arithmeticQuotientPrime z)
      (frozenPrimeCutoff N n tau (arithmeticBand z) (arithmeticPrime z))
      (firstBadPrime (arithmeticQuotientPrime z)
        (frozenPrimeCutoff N n tau (arithmeticBand z) (arithmeticPrime z))) := by
  cases z with
  | inl x =>
      obtain ⟨p, q⟩ := x
      obtain ⟨_, hr, hf⟩ := (rejected_frozen_U3_iff N n p q tau).mp hz
      simpa [arithmeticQuotientPrime, arithmeticBand, arithmeticPrime] using
        (rejected_frozen_fibre_first_bad N n tau .U3 p q hr hf)
  | inr x =>
      obtain ⟨p, q⟩ := x
      obtain ⟨_, hr, hf⟩ := (rejected_frozen_U4_iff N n p q tau).mp hz
      simpa [arithmeticQuotientPrime, arithmeticBand, arithmeticPrime] using
        (rejected_frozen_fibre_first_bad N n tau .U4 p q hr hf)

/-- A rejected quotient retains both its true original additive prime P
and its first frozen-cutoff small-prime obstruction. -/
theorem rejected_frozen_P_and_obstruction (N n : ℕ) (tau : ℝ)
    {z : TaggedReceiver} (hz : z ∈ rejectedFrozen N n tau) :
    additivePrimeLabel N z ∈ chenAdditivePrimeCarrier N ∧
    (N - additivePrimeLabel N z) / arithmeticPrime z =
      arithmeticQuotientPrime z ∧
    BadPrime (arithmeticQuotientPrime z)
      (frozenPrimeCutoff N n tau (arithmeticBand z) (arithmeticPrime z))
      (firstBadPrime (arithmeticQuotientPrime z)
        (frozenPrimeCutoff N n tau (arithmeticBand z) (arithmeticPrime z))) := by
  have hr : z ∈ rawTagged N := (Finset.mem_sdiff.mp hz).1
  have hP := raw_prime_label_data hr
  exact ⟨hP.1, hP.2, rejected_frozen_tagged_first_bad N n tau hz⟩

theorem frozen_only_P_and_obstruction (N n : ℕ) (tau : ℝ)
    {z : TaggedReceiver} (hz : z ∈ frozenOnly N n tau) :
    additivePrimeLabel N z ∈ chenAdditivePrimeCarrier N ∧
    (N - additivePrimeLabel N z) / arithmeticPrime z =
      arithmeticQuotientPrime z ∧
    BadPrime (arithmeticQuotientPrime z) ((N : ℝ)^a)
      (firstBadPrime (arithmeticQuotientPrime z) ((N : ℝ)^a)) ∧
    frozenPrimeCutoff N n tau (arithmeticBand z) (arithmeticPrime z) ≤
      (firstBadPrime (arithmeticQuotientPrime z) ((N : ℝ)^a) : ℝ) := by
  have hr : z ∈ rawTagged N :=
    frozen_tagged_subset_raw N n tau (Finset.mem_sdiff.mp hz).1
  have hP := raw_prime_label_data hr
  have hB := frozen_only_tagged_first_bad N n tau hz
  exact ⟨hP.1, hP.2, hB.1, hB.2⟩

/-- The exact first obstruction divides positive q <= N, so each
still-rejected source has an ACTUAL finite owner index in Fin (N+1). -/
theorem rejected_frozen_owner_le_target (N n : ℕ) (tau : ℝ)
    {z : TaggedReceiver} (hz : z ∈ rejectedFrozen N n tau) :
    firstBadPrime (arithmeticQuotientPrime z)
      (frozenPrimeCutoff N n tau (arithmeticBand z) (arithmeticPrime z)) ≤ N := by
  have hr : z ∈ rawTagged N := (Finset.mem_sdiff.mp hz).1
  have hq := raw_quotient_data hr
  have hb := rejected_frozen_tagged_first_bad N n tau hz
  exact (Nat.le_of_dvd hq.1 hb.2.1).trans hq.2.1

noncomputable def rejectedOwnerIndex (N n : ℕ) (tau : ℝ)
    (z : TaggedReceiver) (hz : z ∈ rejectedFrozen N n tau) : Fin (N+1) :=
  ⟨firstBadPrime (arithmeticQuotientPrime z)
    (frozenPrimeCutoff N n tau (arithmeticBand z) (arithmeticPrime z)),
   Nat.lt_succ_of_le (rejected_frozen_owner_le_target N n tau hz)⟩

/-- Exact owner fibres retain every tagged (p,q) without collapsing the
arithmetic receiver multiplicity to the root history mark one. -/
noncomputable def rejectedOwnerFibre (N n : ℕ) (tau : ℝ)
    (ell : Fin (N+1)) : Finset TaggedReceiver :=
  (rejectedFrozen N n tau).filter (fun z =>
    firstBadPrime (arithmeticQuotientPrime z)
      (frozenPrimeCutoff N n tau (arithmeticBand z) (arithmeticPrime z)) = ell.val)

theorem rejected_mem_own_fibre (N n : ℕ) (tau : ℝ)
    {z : TaggedReceiver} (hz : z ∈ rejectedFrozen N n tau) :
    z ∈ rejectedOwnerFibre N n tau (rejectedOwnerIndex N n tau z hz) := by
  exact Finset.mem_filter.mpr ⟨hz, rfl⟩

/-- A tagged rejected quotient cannot be charged to two different
prime-factor owners. Historical full/selected/inherited owner remains open. -/
theorem rejected_fibre_owner_unique (N n : ℕ) (tau : ℝ)
    (z : TaggedReceiver) (ell₁ ell₂ : Fin (N+1))
    (h₁ : z ∈ rejectedOwnerFibre N n tau ell₁)
    (h₂ : z ∈ rejectedOwnerFibre N n tau ell₂) : ell₁ = ell₂ := by
  apply Fin.ext
  exact (Finset.mem_filter.mp h₁).2.symm.trans (Finset.mem_filter.mp h₂).2

end
end ImbalancedChen.Part5OriginalH430TaggedFirstBadPrimeOwner
