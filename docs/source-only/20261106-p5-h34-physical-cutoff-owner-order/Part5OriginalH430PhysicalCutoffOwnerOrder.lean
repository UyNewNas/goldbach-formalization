import ImbalancedChen.Part5OriginalH430JointPrimePrefix

/-!
P5.6 / h34: an actual physical-cutoff comparison for the ORIGINAL
(U3/U4,p,P,q) arithmetic rejection lanes.

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The least divisor of N-P is not assumed to be a historical first-excluded
owner. In particular, the hypotheses comparing the actual selected p to
a physical cutoff are NOT asserted to hold at all roots. Every signed
mass identity below is an exact partition, NOT a bound on either part.
-/

namespace ImbalancedChen.Part5OriginalH430PhysicalCutoffOwnerOrder
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
open Part5OriginalH430JointPrimePrefix

/-- The quotient's least obstruction is at least the selected original
prime precisely when the ORIGINAL quotient is rough at that prime.
No arbitrary historic retention policy is inserted into this test. -/
theorem root_le_bad_iff_quotient_rough_at_root (z : TaggedReceiver)
    {cut : ℝ}
    (hfail : ¬ ChenPrimeRough cut (arithmeticQuotientPrime z)) :
    arithmeticPrime z ≤
      firstBadPrime (arithmeticQuotientPrime z) cut ↔
    ChenPrimeRough (arithmeticPrime z : ℝ) (arithmeticQuotientPrime z) := by
  constructor
  · intro h
    apply (rough_iff_below_first_bad hfail _).2
    exact_mod_cast h
  · intro h
    have he := (rough_iff_below_first_bad hfail _).1 h
    exact_mod_cast he

/-- Strict quotient-first order is detected by FAILURE of the same
literal p-roughness test; the equality case belongs to root-first. -/
theorem bad_lt_root_iff_quotient_not_rough_at_root (z : TaggedReceiver)
    {cut : ℝ}
    (hfail : ¬ ChenPrimeRough cut (arithmeticQuotientPrime z)) :
    firstBadPrime (arithmeticQuotientPrime z) cut <
      arithmeticPrime z ↔
    ¬ ChenPrimeRough (arithmeticPrime z : ℝ)
      (arithmeticQuotientPrime z) := by
  constructor
  · intro hle hrough
    exact (Nat.not_lt_of_ge
      ((root_le_bad_iff_quotient_rough_at_root z hfail).2 hrough)) hle
  · intro hnot
    exact Nat.lt_of_not_ge (fun hle =>
      hnot ((root_le_bad_iff_quotient_rough_at_root z hfail).1 hle))

/-- A genuine quotient surviving the p-cutoff makes p the first prime
factor of the complete N-P. This does NOT make p a first-excluded exit. -/
theorem joint_eq_root_of_quotient_rough (z : TaggedReceiver)
    {cut : ℝ}
    (hfail : ¬ ChenPrimeRough cut (arithmeticQuotientPrime z))
    (hrough : ChenPrimeRough (arithmeticPrime z : ℝ)
      (arithmeticQuotientPrime z)) :
    jointFirstPrime z cut = arithmeticPrime z := by
  unfold jointFirstPrime
  exact min_eq_left
    ((root_le_bad_iff_quotient_rough_at_root z hfail).2 hrough)

/-- If the quotient fails even at p, its least obstructing prime
strictly precedes p in the full N-P prime order. -/
theorem joint_eq_bad_of_quotient_not_rough (z : TaggedReceiver)
    {cut : ℝ}
    (hfail : ¬ ChenPrimeRough cut (arithmeticQuotientPrime z))
    (hnot : ¬ ChenPrimeRough (arithmeticPrime z : ℝ)
      (arithmeticQuotientPrime z)) :
    jointFirstPrime z cut =
      firstBadPrime (arithmeticQuotientPrime z) cut ∧
    firstBadPrime (arithmeticQuotientPrime z) cut < arithmeticPrime z := by
  have hlt := (bad_lt_root_iff_quotient_not_rough_at_root z hfail).2 hnot
  exact ⟨by
    unfold jointFirstPrime
    exact min_eq_right hlt.le, hlt⟩

/-- Every originally rejected but frozen-admitted arithmetic receipt
has a genuine p-versus-q order split, decided by the p-roughness test.
The q is an INTEGER quotient, not assumed to be prime. -/
theorem frozen_only_joint_order (N n : ℕ) (tau : ℝ)
    {z : TaggedReceiver} (hz : z ∈ frozenOnly N n tau) :
    (ChenPrimeRough (arithmeticPrime z : ℝ)
        (arithmeticQuotientPrime z) ∧
      jointFirstPrime z ((N : ℝ)^a) = arithmeticPrime z) ∨
    (¬ ChenPrimeRough (arithmeticPrime z : ℝ)
        (arithmeticQuotientPrime z) ∧
      jointFirstPrime z ((N : ℝ)^a) =
        firstBadPrime (arithmeticQuotientPrime z) ((N : ℝ)^a) ∧
      firstBadPrime (arithmeticQuotientPrime z) ((N : ℝ)^a) <
        arithmeticPrime z) := by
  have hfail : ¬ ChenPrimeRough ((N : ℝ)^a)
      (arithmeticQuotientPrime z) :=
    bad_implies_not_rough (frozen_only_tagged_first_bad N n tau hz).1
  by_cases h : ChenPrimeRough (arithmeticPrime z : ℝ)
      (arithmeticQuotientPrime z)
  · exact Or.inl ⟨h, joint_eq_root_of_quotient_rough z hfail h⟩
  · exact Or.inr ⟨h, (joint_eq_bad_of_quotient_not_rough z hfail h).1,
      (joint_eq_bad_of_quotient_not_rough z hfail h).2⟩

/-- The same literal order split at the ACTUAL frozen physical cutoff.
Nothing identifies either side with a retained tree first exit. -/
theorem rejected_frozen_joint_order (N n : ℕ) (tau : ℝ)
    {z : TaggedReceiver} (hz : z ∈ rejectedFrozen N n tau) :
    let cut := frozenPrimeCutoff N n tau (arithmeticBand z) (arithmeticPrime z)
    (ChenPrimeRough (arithmeticPrime z : ℝ)
        (arithmeticQuotientPrime z) ∧
      jointFirstPrime z cut = arithmeticPrime z) ∨
    (¬ ChenPrimeRough (arithmeticPrime z : ℝ)
        (arithmeticQuotientPrime z) ∧
      jointFirstPrime z cut =
        firstBadPrime (arithmeticQuotientPrime z) cut ∧
      firstBadPrime (arithmeticQuotientPrime z) cut < arithmeticPrime z) := by
  dsimp
  have hfail : ¬ ChenPrimeRough
      (frozenPrimeCutoff N n tau (arithmeticBand z) (arithmeticPrime z))
      (arithmeticQuotientPrime z) :=
    bad_implies_not_rough (rejected_frozen_tagged_first_bad N n tau hz)
  by_cases h : ChenPrimeRough (arithmeticPrime z : ℝ)
      (arithmeticQuotientPrime z)
  · exact Or.inl ⟨h, joint_eq_root_of_quotient_rough z hfail h⟩
  · exact Or.inr ⟨h, (joint_eq_bad_of_quotient_not_rough z hfail h).1,
      (joint_eq_bad_of_quotient_not_rough z hfail h).2⟩

/-- This condition refers to the REAL frozen cutoff of the same tagged p.
If p lies below that cutoff, a frozen-only q is p-rough, so p is the
least factor of N-P. The bound p<=cut is an explicit, unproved gate. -/
theorem frozen_only_root_first_of_root_le_physical (N n : ℕ) (tau : ℝ)
    {z : TaggedReceiver} (hz : z ∈ frozenOnly N n tau)
    (hroot : (arithmeticPrime z : ℝ) ≤
      frozenPrimeCutoff N n tau (arithmeticBand z) (arithmeticPrime z)) :
    jointFirstPrime z ((N : ℝ)^a) = arithmeticPrime z := by
  have hprefix := frozen_only_additive_prefix N n tau hz
  have hroughFrozen : ChenPrimeRough
      (frozenPrimeCutoff N n tau (arithmeticBand z) (arithmeticPrime z))
      (arithmeticQuotientPrime z) :=
    (hprefix.2.2.2.2 _).2 hprefix.2.2.1
  have hroughRoot : ChenPrimeRough (arithmeticPrime z : ℝ)
      (arithmeticQuotientPrime z) := by
    intro r hr hd
    exact hroot.trans (hroughFrozen r hr hd)
  have hfail : ¬ ChenPrimeRough ((N : ℝ)^a)
      (arithmeticQuotientPrime z) :=
    bad_implies_not_rough (frozen_only_tagged_first_bad N n tau hz).1
  exact joint_eq_root_of_quotient_rough z hfail hroughRoot

/-- If the physical frozen cutoff does not exceed original p, an
actually frozen-rejected q has its first obstructing ell STRICTLY
before p. This is a consequence of the literal strict sieve test. -/
theorem rejected_frozen_quotient_first_of_physical_le_root
    (N n : ℕ) (tau : ℝ)
    {z : TaggedReceiver} (hz : z ∈ rejectedFrozen N n tau)
    (hroot : frozenPrimeCutoff N n tau (arithmeticBand z)
      (arithmeticPrime z) ≤ (arithmeticPrime z : ℝ)) :
    jointFirstPrime z
      (frozenPrimeCutoff N n tau (arithmeticBand z)
        (arithmeticPrime z)) =
      firstBadPrime (arithmeticQuotientPrime z)
        (frozenPrimeCutoff N n tau (arithmeticBand z)
          (arithmeticPrime z)) ∧
    firstBadPrime (arithmeticQuotientPrime z)
      (frozenPrimeCutoff N n tau (arithmeticBand z)
        (arithmeticPrime z)) < arithmeticPrime z := by
  have hprefix := rejected_frozen_additive_prefix N n tau hz
  have hltReal : (firstBadPrime (arithmeticQuotientPrime z)
      (frozenPrimeCutoff N n tau (arithmeticBand z)
        (arithmeticPrime z)) : ℝ) < (arithmeticPrime z : ℝ) :=
    hprefix.2.2.1.trans_le hroot
  have hlt : firstBadPrime (arithmeticQuotientPrime z)
      (frozenPrimeCutoff N n tau (arithmeticBand z)
        (arithmeticPrime z)) < arithmeticPrime z := by
    exact_mod_cast hltReal
  exact ⟨by
    unfold jointFirstPrime
    exact min_eq_right hlt.le, hlt⟩

/-- EXACT (possibly signed) partition of any physical receipt family by
its literal quotient roughness at its selected prime. No count or signed
mass is discarded and no historical exit owner has been inferred. -/
theorem tagged_signed_mass_order_partition
    (S : Finset TaggedReceiver) (w : TaggedReceiver → ℝ) :
    (∑ z ∈ S, w z) =
      (∑ z ∈ S, if ChenPrimeRough (arithmeticPrime z : ℝ)
          (arithmeticQuotientPrime z) then w z else 0) +
      (∑ z ∈ S, if ChenPrimeRough (arithmeticPrime z : ℝ)
          (arithmeticQuotientPrime z) then 0 else w z) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : ChenPrimeRough (arithmeticPrime z : ℝ)
      (arithmeticQuotientPrime z) <;> simp [h]

/-- Apply the exact signed split WITHOUT forgetting U3/U4 labels, p or q
to the previously defined frozen-only rejected mass. -/
theorem frozen_only_signed_mass_order_partition
    (N n : ℕ) (tau : ℝ) (w : TaggedReceiver → ℝ) :
    (∑ z ∈ frozenOnly N n tau, w z) =
      (∑ z ∈ frozenOnly N n tau,
        if ChenPrimeRough (arithmeticPrime z : ℝ)
          (arithmeticQuotientPrime z) then w z else 0) +
      (∑ z ∈ frozenOnly N n tau,
        if ChenPrimeRough (arithmeticPrime z : ℝ)
          (arithmeticQuotientPrime z) then 0 else w z) :=
  tagged_signed_mass_order_partition (frozenOnly N n tau) w

/-- A separate signed split for the still-rejected physical receipts.
Neither right-hand sum is assumed small or positive. -/
theorem rejected_frozen_signed_mass_order_partition
    (N n : ℕ) (tau : ℝ) (w : TaggedReceiver → ℝ) :
    (∑ z ∈ rejectedFrozen N n tau, w z) =
      (∑ z ∈ rejectedFrozen N n tau,
        if ChenPrimeRough (arithmeticPrime z : ℝ)
          (arithmeticQuotientPrime z) then w z else 0) +
      (∑ z ∈ rejectedFrozen N n tau,
        if ChenPrimeRough (arithmeticPrime z : ℝ)
          (arithmeticQuotientPrime z) then 0 else w z) :=
  tagged_signed_mass_order_partition (rejectedFrozen N n tau) w

end
end ImbalancedChen.Part5OriginalH430PhysicalCutoffOwnerOrder
