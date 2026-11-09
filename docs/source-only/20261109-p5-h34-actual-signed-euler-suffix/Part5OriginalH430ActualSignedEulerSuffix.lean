import ImbalancedChen.OrdinaryRosserFirstExitPolicy
import ImbalancedChen.Part5OriginalH430PhysicalSelectedRootQFibres

/-!
P5.6 / h34 — exact FIRST-EXCLUDED signed Euler suffix at the actual
ordinary-Rosser small-prime carrier and original U3/U4 physical root Q.

The manuscript's first-excluded sum is a signed finite tree correction,
NOT the arithmetic six-lane rejection count and NOT a nonnegative payment
unless its sign has separately been established. The local ordinary
Rosser density here is exactly the existing density, not a new sieve
estimate. Both U3/U4 tags keep their own physical Q; distinct q at one
tag/p do not create distinct historical root Euler corrections.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualSignedEulerSuffix

noncomputable section
open scoped BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430PhysicalSelectedRootQFibres

/-- The unique finite physical prime carrier Euler factor.  In
particular it is independent of the Q of the root policy; the original
carrier is NOT the collection of original arithmetic q receipts. -/
def physicalEulerBase (N cap : ℕ) (z0 : ℝ) : ℝ :=
  ((roughPrimeUniverse N cap 0 z0).map
    (fun p : ℕ => 1 - 1 / ((p : ℝ) - 1))).prod

/-- The existing finite first-exit correction with the actual
ordinary-Rosser policy, fixed physical Q, sign/parity recursion,
prime reciprocals, and physical prime carrier.  The suffix products
over unprocessed primes are still present inside firstExitCorrection. -/
def physicalFirstExcludedSuffix (lower : Bool)
    (N cap : ℕ) (z0 Q : ℝ) : ℝ :=
  firstExitCorrection (ordinaryRosserRetainedPolicy lower Q)
    (fun p : ℕ => 1 / ((p : ℝ) - 1))
    [] true 1 (roughPrimeUniverse N cap 0 z0)

/-- Exact signed first-excluded identity at the real finite prime
carrier. The correction's sign is NOT discarded. -/
theorem physical_retained_eq_euler_add_first_excluded
    (lower : Bool) (N cap : ℕ) (z0 Q : ℝ) :
    firstExitRetainedPolynomial
      (ordinaryRosserRetainedPolicy lower Q)
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0) =
      physicalEulerBase N cap z0 +
        physicalFirstExcludedSuffix lower N cap z0 Q := by
  simpa only [physicalEulerBase, physicalFirstExcludedSuffix] using
    (firstExitRetainedPolynomial_eq_product_add_correction
      (ordinaryRosserRetainedPolicy lower Q)
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] (roughPrimeUniverse N cap 0 z0) true (1 : ℝ))

/-- The exact existing UPPER physical Rosser density, with
first-excluded correction retained and no unsigned bound claimed. -/
theorem physical_upper_density_eq_euler_add_first_excluded
    (N cap : ℕ) (z0 Q : ℝ) (hQ : 1 < Q) :
    actualSmallRosserPlusDensity N cap z0 Q =
      physicalEulerBase N cap z0 +
        physicalFirstExcludedSuffix false N cap z0 Q := by
  have h := firstExitRetainedPolynomial_eq_actualSmallRosserDensity
    false N cap z0 Q hQ
  simp only [Bool.false_eq_true, if_false] at h
  calc
    _ = firstExitRetainedPolynomial
          (ordinaryRosserRetainedPolicy false Q)
          (fun p : ℕ => 1 / ((p : ℝ) - 1))
          [] true 1 (roughPrimeUniverse N cap 0 z0) := h.symm
    _ = _ := physical_retained_eq_euler_add_first_excluded
      false N cap z0 Q

/-- The exact existing LOWER density uses the same physical Euler
base, but its OWN signed first-excluded correction. The upper
correction is not substituted for it. -/
theorem physical_lower_density_eq_euler_add_first_excluded
    (N cap : ℕ) (z0 Q : ℝ) (hQ : 1 < Q) :
    actualSmallRosserMinusDensity N cap z0 Q =
      physicalEulerBase N cap z0 +
        physicalFirstExcludedSuffix true N cap z0 Q := by
  have h := firstExitRetainedPolynomial_eq_actualSmallRosserDensity
    true N cap z0 Q hQ
  simp only [if_true] at h
  calc
    _ = firstExitRetainedPolynomial
          (ordinaryRosserRetainedPolicy true Q)
          (fun p : ℕ => 1 / ((p : ℝ) - 1))
          [] true 1 (roughPrimeUniverse N cap 0 z0) := h.symm
    _ = _ := physical_retained_eq_euler_add_first_excluded
      true N cap z0 Q

/-- When the upper and lower small-prime policies use the same
physical Q, their density difference is exactly their difference
of signed first-excluded corrections: no fictitious second Euler
main term or automatic sign cancellation is available. -/
theorem physical_upper_lower_difference_is_signed_suffix_difference
    (N cap : ℕ) (z0 Q : ℝ) (hQ : 1 < Q) :
    actualSmallRosserPlusDensity N cap z0 Q -
      actualSmallRosserMinusDensity N cap z0 Q =
      physicalFirstExcludedSuffix false N cap z0 Q -
        physicalFirstExcludedSuffix true N cap z0 Q := by
  rw [physical_upper_density_eq_euler_add_first_excluded N cap z0 Q hQ,
    physical_lower_density_eq_euler_add_first_excluded N cap z0 Q hQ]
  ring

/-- A physical root's upper density is evaluated at the ACTUAL
tag/p-dependent Q already defined by the selected U3/U4 q-fibre.
The original q is not the root level. The strict level condition is
kept explicit rather than silently transferred from an unrelated Q. -/
theorem tagged_original_physical_upper_density
    (N cap precision : ℕ) (tau z0 : ℝ) (z : TaggedReceiver)
    (hQ : 1 < originalPhysicalQ N precision tau z) :
    actualSmallRosserPlusDensity N cap z0
        (originalPhysicalQ N precision tau z) =
      physicalEulerBase N cap z0 +
      physicalFirstExcludedSuffix false N cap z0
        (originalPhysicalQ N precision tau z) :=
  physical_upper_density_eq_euler_add_first_excluded
    N cap z0 (originalPhysicalQ N precision tau z) hQ

/-- Two original U3 and U4 receipts at the same (p,q) share the
physical prime carrier but NOT necessarily the same Q. Their upper
density difference is precisely the difference of the two original
signed Euler suffixes; in particular no unproved same-Q hypothesis
or zero-collision payment is inserted. -/
theorem original_U4_overlap_two_Q_upper_difference
    (N cap precision p q : ℕ) (tau z0 : ℝ)
    (hQ3 : 1 < originalPhysicalQ N precision tau
      (Sum.inl (⟨p, q⟩ : TaggedPair)))
    (hQ4 : 1 < originalPhysicalQ N precision tau
      (Sum.inr (⟨p, q⟩ : TaggedPair))) :
    actualSmallRosserPlusDensity N cap z0
        (originalPhysicalQ N precision tau
          (Sum.inl (⟨p, q⟩ : TaggedPair))) -
      actualSmallRosserPlusDensity N cap z0
        (originalPhysicalQ N precision tau
          (Sum.inr (⟨p, q⟩ : TaggedPair))) =
      physicalFirstExcludedSuffix false N cap z0
        (originalPhysicalQ N precision tau
          (Sum.inl (⟨p, q⟩ : TaggedPair))) -
      physicalFirstExcludedSuffix false N cap z0
        (originalPhysicalQ N precision tau
          (Sum.inr (⟨p, q⟩ : TaggedPair))) := by
  rw [physical_upper_density_eq_euler_add_first_excluded
        N cap z0 _ hQ3,
      physical_upper_density_eq_euler_add_first_excluded
        N cap z0 _ hQ4]
  ring

/-- At a fixed original U3 root p, two different original q
receipts do NOT create two independent historical Euler suffixes.
This is a literal property of originalPhysicalQ, not an injection or
payment theorem. -/
theorem original_U3_quotient_independent_signed_suffix
    (N cap precision p q₁ q₂ : ℕ) (tau z0 : ℝ) :
    physicalFirstExcludedSuffix false N cap z0
        (originalPhysicalQ N precision tau
          (Sum.inl (⟨p, q₁⟩ : TaggedPair))) =
      physicalFirstExcludedSuffix false N cap z0
        (originalPhysicalQ N precision tau
          (Sum.inl (⟨p, q₂⟩ : TaggedPair))) := by
  rfl

end
end ImbalancedChen.Part5OriginalH430ActualSignedEulerSuffix
