import ImbalancedChen.Part5OriginalH430ActualSignedEulerSuffix

/-!
P5.6 / h34 — SIGN of the genuine upper ordinary-Rosser first-excluded
Euler correction, at the fixed physical prime carrier and actual Q.

The full-prefix ordinary policy may fail its even-rank test on an
arbitrary invalid prefix.  Positivity therefore cannot be obtained by
applying the generic even-retained tree lemma directly to that policy.
Instead the existing verified-path equivalence transports the correction
to the PARITY-SAFE upper policy, which retains every even-rank step.
This uses the same strict physical level and the same finite carrier.

This establishes a sign for the UPPER finite Euler suffix only.  It
does NOT equate it with any of the six original q/tag rejected source
lanes, nor does it prove a selected-count owner, a weighted payment, or
an H430 error bound.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430UpperSignedSuffixDirection

noncomputable section

open Part5OriginalH430ActualSignedEulerSuffix
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430TaggedArithmeticReceivers

/-- Actual reciprocal-totient prime factors lie in [0,1] at every
member of the REAL physical presieve carrier; no artificial lower
prime cutoff is inserted. -/
theorem physical_prime_reciprocal_between_zero_one
    (N cap : ℕ) (z0 : ℝ) (p : ℕ)
    (hp : p ∈ roughPrimeUniverse N cap 0 z0) :
    0 ≤ (1 : ℝ) / ((p : ℝ) - 1) ∧
      (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 := by
  have hprime : p.Prime := mem_roughPrimeUniverse_prime hp
  have htwo : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hprime.two_le
  have hd : 0 < (p : ℝ) - 1 := by linarith
  constructor
  · exact div_nonneg (by norm_num) hd.le
  · apply (div_le_iff₀ hd).2
    linarith

/-- At the same real Q and the same physical carrier, the upper
full-prefix and parity-safe Rosser policies have IDENTICAL signed
first-excluded totals, even though their tests are not pointwise
equal at arbitrary unreachable prefixes.  This is a consequence of
the existing retained-polynomial equivalence, not an assumed sign. -/
theorem physical_upper_suffix_eq_parity_safe_correction
    (N cap : ℕ) (z0 Q : ℝ) (hQ : 1 < Q) :
    physicalFirstExcludedSuffix false N cap z0 Q =
      firstExitCorrection (ordinaryParityRosserPolicy false Q)
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z0) := by
  have hpol :=
    firstExitRetainedPolynomial_ordinaryParityRosser
      false Q hQ (roughPrimeUniverse N cap 0 z0)
      (roughPrimeUniverse_pairwise_gt N cap 0 z0)
      (fun p hp => mem_roughPrimeUniverse_prime hp)
      (by simp)
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
  rw [firstExitRetainedPolynomial_eq_product_add_correction
        (ordinaryParityRosserPolicy false Q)
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        [] (roughPrimeUniverse N cap 0 z0) true (1 : ℝ),
      firstExitRetainedPolynomial_eq_product_add_correction
        (ordinaryRosserRetainedPolicy false Q)
        (fun p : ℕ => 1 / ((p : ℝ) - 1))
        [] (roughPrimeUniverse N cap 0 z0) true (1 : ℝ)] at hpol
  simp only [signedTreeCoefficient_true, one_mul] at hpol
  change firstExitCorrection (ordinaryRosserRetainedPolicy false Q)
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0) =
    firstExitCorrection (ordinaryParityRosserPolicy false Q)
      (fun p : ℕ => 1 / ((p : ℝ) - 1))
      [] true 1 (roughPrimeUniverse N cap 0 z0)
  linarith

/-- The physical UPPER first-excluded suffix is nonnegative.
The proof does NOT discard the signed terms individually: it uses
the real upper parity-safe first-exit tree, whose even-rank steps
cannot be exits, and then transports the entire signed sum. -/
theorem physical_upper_first_excluded_suffix_nonneg
    (N cap : ℕ) (z0 Q : ℝ) (hQ : 1 < Q) :
    0 ≤ physicalFirstExcludedSuffix false N cap z0 Q := by
  rw [physical_upper_suffix_eq_parity_safe_correction N cap z0 Q hQ]
  exact firstExitCorrection_nonneg_of_even_retained
    (ordinaryParityRosserPolicy false Q)
    (fun p : ℕ => 1 / ((p : ℝ) - 1))
    [] (roughPrimeUniverse N cap 0 z0) true 1
    (fun pre => ordinaryParityRosserPolicy_upper_even Q pre)
    (by norm_num)
    (fun p hp => physical_prime_reciprocal_between_zero_one N cap z0 p hp)

/-- The actual upper Rosser density at real physical Q dominates
the one common complete Euler product. This is a finite density
direction, NOT the original H430 selected-count estimate. -/
theorem physical_upper_density_ge_euler_base
    (N cap : ℕ) (z0 Q : ℝ) (hQ : 1 < Q) :
    physicalEulerBase N cap z0 ≤
      actualSmallRosserPlusDensity N cap z0 Q := by
  rw [physical_upper_density_eq_euler_add_first_excluded N cap z0 Q hQ]
  exact le_add_of_nonneg_right
    (physical_upper_first_excluded_suffix_nonneg N cap z0 Q hQ)

/-- The sign in the original Chen lower-bound subtraction is opposite
to the now-proved positive UPPER finite Euler correction. This says
NOTHING about the signs of arithmetic/history mismatches and six
unpaid rejection lanes, which remain separate. -/
theorem chen_negative_quarter_upper_suffix_nonpos
    (N cap : ℕ) (z0 Q : ℝ) (hQ : 1 < Q) :
    -(1 / 4 : ℝ) * physicalFirstExcludedSuffix false N cap z0 Q ≤ 0 := by
  exact mul_nonpos_of_nonpos_of_nonneg
    (by norm_num)
    (physical_upper_first_excluded_suffix_nonneg N cap z0 Q hQ)

/-- The sign is also available at the EXACT tag- and root-specific
physical Q, with its strict-level premise explicitly retained. -/
theorem tagged_original_upper_first_excluded_nonneg
    (N cap precision : ℕ) (tau z0 : ℝ) (z : TaggedReceiver)
    (hQ : 1 < originalPhysicalQ N precision tau z) :
    0 ≤ physicalFirstExcludedSuffix false N cap z0
      (originalPhysicalQ N precision tau z) :=
  physical_upper_first_excluded_suffix_nonneg N cap z0
    (originalPhysicalQ N precision tau z) hQ

end
end ImbalancedChen.Part5OriginalH430UpperSignedSuffixDirection
