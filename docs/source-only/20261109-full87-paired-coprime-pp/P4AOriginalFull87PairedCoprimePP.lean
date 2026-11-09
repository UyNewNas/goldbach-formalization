import ImbalancedChen.P4AOriginalFull87PairedTrueSharpPrimitive
import ImbalancedChen.P4AOriginalFull87TrueSingletonPPMean
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The manuscript's singleton PP mean is the q-dependent COPRIME mass
X_W^(q), not the unrestricted weighted prime mass.  For the genuine
RAW and LICENSED policies, subtract that true mean BEFORE measuring
the discrepancy. The weighted modulus-prime and global mass-defect
terms then cancel algebraically; they must NOT be charged again as
independent PP errors.  Actual prime-centre deletion and the two sharp
endpoints remain, with their original signs and only one occurrence.
All full-q signed Rosser coefficients and repeated terminal occurrences
are inherited from the original supportedPhysicalRho.
This is a finite identity, NOT an invocation of the external PP theorem
and NOT an H_N payment, legal X, or saved87 certificate.
-/

namespace ImbalancedChen.P4AOriginalFull87PairedCoprimePP
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87PhysicalQAggregateInvoice (pairActualPhysicalModuli)
open P4AOriginalFull87FullRhoQBridge (supportedPhysicalRho)
open P4AOriginalFull87WeightedSharpSmooth
  (originalSharpLiteral weightedLowerBoundary weightedUpperBoundary)
open P4AOriginalFull87SharpCentreCarrier
  (actualSharpCarrierLiteral centreSharpSigned sharp_eq_actual_carrier_add_centre)
open P4AOriginalFull87TrueSingletonPPMean
  (original_sharp_true_singleton_PP_exact)

/-- Extend a REAL original policy's signed finite modulus sum by zero to
the union of TWO real original supports. This changes labels only: no
small Rosser factor, selected prime, parent, sign or occurrence is
discarded. The earlier private pair helper is not an exported theorem. -/
private theorem pair_real_source_sum
    (R S : Bool → List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (f : ℕ → ℝ) :
    (∑ d ∈ actualSmallRoughModuli (R false) N cap w z,
      actualSmallRoughRho (R false) N cap w z L d * f d) -
    (∑ d ∈ actualSmallRoughModuli (S false) N cap w z,
      actualSmallRoughRho (S false) N cap w z L d * f d) =
    ∑ d ∈ pairActualPhysicalModuli R S N cap w z,
      (supportedPhysicalRho R N cap w z L d -
       supportedPhysicalRho S N cap w z L d) * f d := by
  classical
  let MR : Finset ℕ := actualSmallRoughModuli (R false) N cap w z
  let MS : Finset ℕ := actualSmallRoughModuli (S false) N cap w z
  let M : Finset ℕ := pairActualPhysicalModuli R S N cap w z
  have hrsub : MR ⊆ M := by
    intro d hd
    exact Finset.mem_union.mpr (Or.inl hd)
  have hssub : MS ⊆ M := by
    intro d hd
    exact Finset.mem_union.mpr (Or.inr hd)
  have hrzero : ∀ d ∈ M, d ∉ MR →
      supportedPhysicalRho R N cap w z L d * f d = 0 := by
    intro d _ hn
    simp [supportedPhysicalRho, MR, hn]
  have hszero : ∀ d ∈ M, d ∉ MS →
      supportedPhysicalRho S N cap w z L d * f d = 0 := by
    intro d _ hn
    simp [supportedPhysicalRho, MS, hn]
  have hr :
      (∑ d ∈ MR, actualSmallRoughRho (R false) N cap w z L d * f d) =
      ∑ d ∈ M, supportedPhysicalRho R N cap w z L d * f d := by
    calc
      _ = ∑ d ∈ MR, supportedPhysicalRho R N cap w z L d * f d := by
        apply Finset.sum_congr rfl
        intro d hd
        simp [supportedPhysicalRho, MR, hd]
      _ = _ := Finset.sum_subset hrsub hrzero
  have hs :
      (∑ d ∈ MS, actualSmallRoughRho (S false) N cap w z L d * f d) =
      ∑ d ∈ M, supportedPhysicalRho S N cap w z L d * f d := by
    calc
      _ = ∑ d ∈ MS, supportedPhysicalRho S N cap w z L d * f d := by
        apply Finset.sum_congr rfl
        intro d hd
        simp [supportedPhysicalRho, MS, hd]
      _ = _ := Finset.sum_subset hssub hszero
  change
    (∑ d ∈ MR, actualSmallRoughRho (R false) N cap w z L d * f d) -
    (∑ d ∈ MS, actualSmallRoughRho (S false) N cap w z L d * f d) =
    ∑ d ∈ M,
      (supportedPhysicalRho R N cap w z L d -
       supportedPhysicalRho S N cap w z L d) * f d
  rw [hr, hs, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- The genuine paired sharp Chen receiver, recentered at the
manuscript's TRUE q-dependent singleton coprime mean, equals ONE
same-full-q signed primitive PP discrepancy, plus the signed lower
and upper sharp/smooth boundaries, minus the actual centre deletion.

In contrast to recentering at #primes ≤ N, there is NO additional
modulus-prime or weighted-mass-defect invoice: both are already built
into X_W^(q). No raw/filtered or analytic loss is declared small here. -/
theorem actual_raw_licensed_true_sharp_coprime_PP_same_full_q
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ)
    (hN : ¬ Nat.Prime N)
    (hInterior : ∀ p, p < N → D < N - p → W p = 1) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    (actualSharpCarrierLiteral R N cap w z L -
      actualSharpCarrierLiteral S N cap w z L) -
      (∑ d ∈ pairActualPhysicalModuli R S N cap w z,
        (supportedPhysicalRho R N cap w z L d -
         supportedPhysicalRho S N cap w z L d) *
        (finiteCoprimeMass (chenPrimePrefix (N + D)) W d /
          (Nat.totient d : ℝ))) =
    (∑ d ∈ pairActualPhysicalModuli R S N cap w z,
      (supportedPhysicalRho R N cap w z L d -
       supportedPhysicalRho S N cap w z L d) *
        finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d) +
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
  let MR : Finset ℕ := actualSmallRoughModuli (R false) N cap w z
  let MS : Finset ℕ := actualSmallRoughModuli (S false) N cap w z
  let M : Finset ℕ := pairActualPhysicalModuli R S N cap w z
  let f : ℕ → ℝ := fun d =>
    finiteCoprimeMass (chenPrimePrefix (N + D)) W d /
      (Nat.totient d : ℝ)
  let g : ℕ → ℝ := fun d =>
    finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d
  let VR : ℝ := ∑ d ∈ MR,
    actualSmallRoughRho (R false) N cap w z L d * f d
  let VS : ℝ := ∑ d ∈ MS,
    actualSmallRoughRho (S false) N cap w z L d * f d
  let ER : ℝ := ∑ d ∈ MR,
    actualSmallRoughRho (R false) N cap w z L d * g d
  let ES : ℝ := ∑ d ∈ MS,
    actualSmallRoughRho (S false) N cap w z L d * g d
  have hMean := pair_real_source_sum R S N cap w z L f
  change VR - VS =
    ∑ d ∈ M,
      (supportedPhysicalRho R N cap w z L d -
       supportedPhysicalRho S N cap w z L d) * f d at hMean
  have hError := pair_real_source_sum R S N cap w z L g
  change ER - ES =
    ∑ d ∈ M,
      (supportedPhysicalRho R N cap w z L d -
       supportedPhysicalRho S N cap w z L d) * g d at hError
  have hSharpR := original_sharp_true_singleton_PP_exact
    R N D cap w z L W hN hInterior
  change originalSharpLiteral R N D cap w z L - VR =
    (weightedLowerBoundary R N D cap w z L W -
     weightedUpperBoundary R N D cap w z L W) + ER at hSharpR
  have hSharpS := original_sharp_true_singleton_PP_exact
    S N D cap w z L W hN hInterior
  change originalSharpLiteral S N D cap w z L - VS =
    (weightedLowerBoundary S N D cap w z L W -
     weightedUpperBoundary S N D cap w z L W) + ES at hSharpS
  have hCentreR := sharp_eq_actual_carrier_add_centre
    R N D cap w z L hN
  have hCentreS := sharp_eq_actual_carrier_add_centre
    S N D cap w z L hN
  have hR :
      actualSharpCarrierLiteral R N cap w z L - VR =
        ER + weightedLowerBoundary R N D cap w z L W -
          weightedUpperBoundary R N D cap w z L W -
          centreSharpSigned R N cap w z L := by
    linarith
  have hS :
      actualSharpCarrierLiteral S N cap w z L - VS =
        ES + weightedLowerBoundary S N D cap w z L W -
          weightedUpperBoundary S N D cap w z L W -
          centreSharpSigned S N cap w z L := by
    linarith
  change
    (actualSharpCarrierLiteral R N cap w z L -
      actualSharpCarrierLiteral S N cap w z L) -
      (∑ d ∈ M, (supportedPhysicalRho R N cap w z L d -
       supportedPhysicalRho S N cap w z L d) * f d) =
    (∑ d ∈ M, (supportedPhysicalRho R N cap w z L d -
     supportedPhysicalRho S N cap w z L d) * g d) +
    ((weightedLowerBoundary R N D cap w z L W -
       weightedLowerBoundary S N D cap w z L W) -
     (weightedUpperBoundary R N D cap w z L W -
       weightedUpperBoundary S N D cap w z L W)) -
    (centreSharpSigned R N cap w z L -
      centreSharpSigned S N cap w z L)
  calc
    _ = (actualSharpCarrierLiteral R N cap w z L - VR) -
        (actualSharpCarrierLiteral S N cap w z L - VS) := by
          rw [← hMean]
          ring
    _ = (ER - ES) +
        ((weightedLowerBoundary R N D cap w z L W -
          weightedLowerBoundary S N D cap w z L W) -
         (weightedUpperBoundary R N D cap w z L W -
          weightedUpperBoundary S N D cap w z L W)) -
        (centreSharpSigned R N cap w z L -
          centreSharpSigned S N cap w z L) := by
          rw [hR, hS]
          ring
    _ = _ := by rw [hError]

end
end ImbalancedChen.P4AOriginalFull87PairedCoprimePP
