import ImbalancedChen.P4AOriginalFull87PairedSmoothPrimitive
import ImbalancedChen.P4AOriginalFull87SharpMeanPaymentLedger
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
This closes an EXACT finite P1.4 bridge from the genuine RAW/LICENSED
original Chen receiver source to ONE paired full-q primitive discrepancy.
The centre deletion, lower (1-W) endpoint, upper -W endpoint, weighted
prime-mass defect and weighted modulus-prime correction each occur ONCE.
The coefficient is the ORIGINAL supportedPhysicalRho for each real policy;
there is no surrogate sieve, detached terminal or second numerical reserve.
This is neither legal PP integer-cutoff certification nor an H_N payment.
-/

namespace ImbalancedChen.P4AOriginalFull87PairedTrueSharpPrimitive
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87PhysicalQAggregateInvoice (pairActualPhysicalModuli)
open P4AOriginalFull87FullRhoQBridge (supportedPhysicalRho)
open P4AOriginalFull87WeightedSharpSmooth
  (originalSmoothLiteral weightedLowerBoundary weightedUpperBoundary
   sharp_minus_smooth_eq_weighted_boundaries)
open P4AOriginalFull87WeightedPrimitiveRecentering
  (weightedPrimeMass weightedModulusPrimeMass)
open P4AOriginalFull87SharpMeanPaymentLedger
  (lowerWeightDefect upperWeightTail weighted_prime_mass_sharp_split)
open P4AOriginalFull87SharpCentreCarrier
  (actualSharpCarrierLiteral centreSharpSigned sharp_eq_actual_carrier_add_centre)
open P4AOriginalFull87PairedSmoothPrimitive
  (raw_licensed_smooth_primitive_same_full_q)

/-- The ORIGINAL RAW-minus-LICENSED sharp receiver comparison, centred at
its literal prime-prefix cardinality, is exactly a SINGLE complete-modulus
paired primitive AP discrepancy, minus its true modulus-prime correction,
plus one common smoothing mass defect, its signed endpoint difference, and
its signed target-prime deletion. The two policies may have different actual
stopped histories and rank-eight frontiers. Only the *modulus labels* are
unified; all physical Rosser and terminal occurrences remain within rho.
No positivity of W is needed for this algebraic identity. -/
theorem actual_raw_licensed_true_sharp_primitive_same_full_q
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ)
    (hN : ¬ Nat.Prime N)
    (hInterior : ∀ p, p < N → D < N - p → W p = 1) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    (actualSharpCarrierLiteral R N cap w z L -
      actualSharpCarrierLiteral S N cap w z L) -
      ((chenPrimePrefix N).card : ℝ) *
        ((∑ d ∈ actualSmallRoughModuli (R false) N cap w z,
             actualSmallRoughRho (R false) N cap w z L d /
               (Nat.totient d : ℝ)) -
         (∑ d ∈ actualSmallRoughModuli (S false) N cap w z,
             actualSmallRoughRho (S false) N cap w z L d /
               (Nat.totient d : ℝ))) =
    ((∑ d ∈ pairActualPhysicalModuli R S N cap w z,
       (supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d) *
          finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d) -
     (∑ d ∈ pairActualPhysicalModuli R S N cap w z,
       (supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d) *
          (weightedModulusPrimeMass N D d W / (Nat.totient d : ℝ)))) +
    (upperWeightTail N D W - lowerWeightDefect N W) *
        ((∑ d ∈ actualSmallRoughModuli (R false) N cap w z,
             actualSmallRoughRho (R false) N cap w z L d /
               (Nat.totient d : ℝ)) -
         (∑ d ∈ actualSmallRoughModuli (S false) N cap w z,
             actualSmallRoughRho (S false) N cap w z L d /
               (Nat.totient d : ℝ))) +
    ((weightedLowerBoundary R N D cap w z L W -
        weightedLowerBoundary S N D cap w z L W) -
      (weightedUpperBoundary R N D cap w z L W -
        weightedUpperBoundary S N D cap w z L W)) -
    (centreSharpSigned R N cap w z L -
      centreSharpSigned S N cap w z L) := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  let V_R : ℝ := ∑ d ∈ actualSmallRoughModuli (R false) N cap w z,
    actualSmallRoughRho (R false) N cap w z L d / (Nat.totient d : ℝ)
  let V_S : ℝ := ∑ d ∈ actualSmallRoughModuli (S false) N cap w z,
    actualSmallRoughRho (S false) N cap w z L d / (Nat.totient d : ℝ)
  let P : ℝ := ((chenPrimePrefix N).card : ℝ)
  let T : ℝ := weightedPrimeMass N D W
  let E : ℝ := ∑ d ∈ pairActualPhysicalModuli R S N cap w z,
    (supportedPhysicalRho R N cap w z L d -
     supportedPhysicalRho S N cap w z L d) *
       finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d
  let C : ℝ := ∑ d ∈ pairActualPhysicalModuli R S N cap w z,
    (supportedPhysicalRho R N cap w z L d -
     supportedPhysicalRho S N cap w z L d) *
       (weightedModulusPrimeMass N D d W / (Nat.totient d : ℝ))
  let B : ℝ :=
    (weightedLowerBoundary R N D cap w z L W -
     weightedLowerBoundary S N D cap w z L W) -
    (weightedUpperBoundary R N D cap w z L W -
     weightedUpperBoundary S N D cap w z L W)
  let Z : ℝ := centreSharpSigned R N cap w z L -
    centreSharpSigned S N cap w z L
  have hPair := raw_licensed_smooth_primitive_same_full_q
    delta n e q om N D cap w z L W hN
  change (originalSmoothLiteral R N D cap w z L W -
    originalSmoothLiteral S N D cap w z L W) - T * (V_R - V_S) =
    E - C at hPair
  have hMass : T - P = upperWeightTail N D W - lowerWeightDefect N W := by
    dsimp [T, P]
    rw [weighted_prime_mass_sharp_split]
    ring
  have hSharpR :
      actualSharpCarrierLiteral R N cap w z L =
        originalSmoothLiteral R N D cap w z L W +
          weightedLowerBoundary R N D cap w z L W -
          weightedUpperBoundary R N D cap w z L W -
          centreSharpSigned R N cap w z L := by
    have hEndpoint := sharp_minus_smooth_eq_weighted_boundaries
      R N D cap w z L W hInterior
    have hCentre := sharp_eq_actual_carrier_add_centre
      R N D cap w z L hN
    linarith
  have hSharpS :
      actualSharpCarrierLiteral S N cap w z L =
        originalSmoothLiteral S N D cap w z L W +
          weightedLowerBoundary S N D cap w z L W -
          weightedUpperBoundary S N D cap w z L W -
          centreSharpSigned S N cap w z L := by
    have hEndpoint := sharp_minus_smooth_eq_weighted_boundaries
      S N D cap w z L W hInterior
    have hCentre := sharp_eq_actual_carrier_add_centre
      S N D cap w z L hN
    linarith
  have hSharpPair :
      actualSharpCarrierLiteral R N cap w z L -
        actualSharpCarrierLiteral S N cap w z L =
        (originalSmoothLiteral R N D cap w z L W -
         originalSmoothLiteral S N D cap w z L W) + B - Z := by
    dsimp [B, Z]
    rw [hSharpR, hSharpS]
    ring
  change
    (actualSharpCarrierLiteral R N cap w z L -
     actualSharpCarrierLiteral S N cap w z L) - P * (V_R - V_S) =
      (E - C) +
      (upperWeightTail N D W - lowerWeightDefect N W) * (V_R - V_S) +
      B - Z
  calc
    _ = ((originalSmoothLiteral R N D cap w z L W -
          originalSmoothLiteral S N D cap w z L W) - T * (V_R - V_S)) +
        (T - P) * (V_R - V_S) + B - Z := by
          rw [hSharpPair]
          ring
    _ = (E - C) +
          (upperWeightTail N D W - lowerWeightDefect N W) * (V_R - V_S) +
          B - Z := by rw [hPair, hMass]

end
end ImbalancedChen.P4AOriginalFull87PairedTrueSharpPrimitive
