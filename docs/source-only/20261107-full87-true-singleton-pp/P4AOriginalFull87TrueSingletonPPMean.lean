import ImbalancedChen.P4AOriginalFull87WeightedModulusMeanBridge
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

The pinned manuscript defines X_W^(q) for k=1 as the actual prime
weight restricted to primes coprime to q.  It is NOT a new analytic
constant, nor the unrestricted prime mass T_W.  Consequently the
weighted modulus-prime correction in the predecessor's three-term
identity cancels *exactly* when its X(q) is the genuine singleton
coprime mass.  This packet connects the SAME physical full-beta rho
and both literal original-prime endpoints to that true PP normalization.

The only still-unverified identification is that the eventual Gevrey
weight has exactly the same prime universe as chenPrimePrefix (N+D),
and meets the original PP permissions. No PP estimate is asserted.
-/

namespace ImbalancedChen.P4AOriginalFull87TrueSingletonPPMean
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87WeightedSharpSmooth
open P4AOriginalFull87WeightedPrimitiveRecentering
open P4AOriginalFull87WeightedModulusMeanBridge

/-- For the actual frozen sixth/eighth physical full-modulus rho,
the manuscript's singleton X_W^(q) is literally finiteCoprimeMass,
not weightedPrimeMass. Thus its exact signed PP remainder is the
original primitive discrepancy, with NO separate T_W-X_W^(q) charge.
This is a finite equality even for signed weights and the totalized
modulus-zero convention. Analytic PP use still requires q>0. -/
theorem original_smooth_true_singleton_PP_remainder
    (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ)
    (hN : ¬ Nat.Prime N) :
    originalSmoothLiteral P N D cap w z L W -
        (∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
          actualSmallRoughRho (P false) N cap w z L d *
            (finiteCoprimeMass (chenPrimePrefix (N + D)) W d /
              (Nat.totient d : ℝ))) =
      ∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
        actualSmallRoughRho (P false) N cap w z L d *
          finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d := by
  classical
  rw [original_smooth_eq_actual_weighted_AP P N D cap w z L W hN]
  simp only [finitePrimitiveDiscrepancy, mul_sub, Finset.sum_sub_distrib]

/-- Exact sharp-original-prime bridge at the TRUE modulus-dependent
coprime mean: the only finite errors are the same-rho signed lower
endpoint, the MINUS upper endpoint, and the same-rho primitive PP
remainder. The unrestricted-mass mismatch has cancelled by definition
of X_W^(q), not by a hypothetical asymptotic estimate. -/
theorem original_sharp_true_singleton_PP_exact
    (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ)
    (hN : ¬ Nat.Prime N)
    (hInterior : ∀ p, p < N → D < N - p → W p = 1) :
    originalSharpLiteral P N D cap w z L -
        (∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
          actualSmallRoughRho (P false) N cap w z L d *
            (finiteCoprimeMass (chenPrimePrefix (N + D)) W d /
              (Nat.totient d : ℝ))) =
      (weightedLowerBoundary P N D cap w z L W -
        weightedUpperBoundary P N D cap w z L W) +
      (∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
        actualSmallRoughRho (P false) N cap w z L d *
          finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d) := by
  let M : ℝ :=
    ∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
      actualSmallRoughRho (P false) N cap w z L d *
        (finiteCoprimeMass (chenPrimePrefix (N + D)) W d /
          (Nat.totient d : ℝ))
  let E : ℝ :=
    ∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
      actualSmallRoughRho (P false) N cap w z L d *
        finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d
  have hSS := sharp_minus_smooth_eq_weighted_boundaries
    P N D cap w z L W hInterior
  have hPP : originalSmoothLiteral P N D cap w z L W - M = E :=
    original_smooth_true_singleton_PP_remainder P N D cap w z L W hN
  change originalSharpLiteral P N D cap w z L - M =
    (weightedLowerBoundary P N D cap w z L W -
      weightedUpperBoundary P N D cap w z L W) + E
  calc
    _ = (originalSharpLiteral P N D cap w z L -
          originalSmoothLiteral P N D cap w z L W) +
        (originalSmoothLiteral P N D cap w z L W - M) := by ring
    _ = _ := by rw [hSS, hPP]

/-- The precise finite budget ready for the *licensed* singleton PP:
the signed primitive term remains intact, and only one real
sharp/smooth endpoint invoice is charged. This is NOT o(H_N) and
does not invoke or replace the external PP. -/
theorem original_sharp_true_singleton_PP_invoice
    (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ)
    (hN : ¬ Nat.Prime N)
    (hInterior : ∀ p, p < N → D < N - p → W p = 1)
    (hW : ∀ p, 0 ≤ W p ∧ W p ≤ 1) :
    |originalSharpLiteral P N D cap w z L -
        (∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
          actualSmallRoughRho (P false) N cap w z L d *
            (finiteCoprimeMass (chenPrimePrefix (N + D)) W d /
              (Nat.totient d : ℝ)))| ≤
      |∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
        actualSmallRoughRho (P false) N cap w z L d *
          finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d| +
      lowerEndpointInvoice P N D cap w z L +
      upperEndpointInvoice P N D cap w z L := by
  let sharp := originalSharpLiteral P N D cap w z L
  let smooth := originalSmoothLiteral P N D cap w z L W
  let M : ℝ :=
    ∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
      actualSmallRoughRho (P false) N cap w z L d *
        (finiteCoprimeMass (chenPrimePrefix (N + D)) W d /
          (Nat.totient d : ℝ))
  let E : ℝ :=
    ∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
      actualSmallRoughRho (P false) N cap w z L d *
        finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d
  let B := lowerEndpointInvoice P N D cap w z L +
    upperEndpointInvoice P N D cap w z L
  have hPP : smooth - M = E :=
    original_smooth_true_singleton_PP_remainder P N D cap w z L W hN
  have hEndpoint : |sharp - smooth| ≤ B :=
    sharp_smooth_abs_le_actual_endpoint_invoices
      P N D cap w z L W hInterior hW
  change |sharp - M| ≤ |E| + B
  calc
    |sharp - M| = |(sharp - smooth) + (smooth - M)| := by congr 1; ring
    _ ≤ |sharp - smooth| + |smooth - M| := abs_add_le _ _
    _ = |sharp - smooth| + |E| := by rw [hPP]
    _ ≤ B + |E| := add_le_add_right hEndpoint _
    _ = |E| + B := by ring

end
end ImbalancedChen.P4AOriginalFull87TrueSingletonPPMean
