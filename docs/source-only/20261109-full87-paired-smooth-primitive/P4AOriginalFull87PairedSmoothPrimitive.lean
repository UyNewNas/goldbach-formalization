import ImbalancedChen.P4AOriginalFull87PhysicalQAggregateInvoice
import ImbalancedChen.P4AOriginalFull87WeightedPrimitiveRecentering
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
This is an exact paired RAW/LICENSED smooth original-prime identity, not an
analytic estimate. The primitive AP discrepancy alone is not the recentered
smooth discrepancy: the weighted prime divisors of the COMPLETE physical q
must still be subtracted. Here both terms are first put on the union of
the two ACTUAL small-rough q supports. Only labels, not original signed
Rosser/rough occurrences, are deduplicated. No geometric saved87 witness,
H_N payment, legal integer PP cutoff or manuscript AP input is claimed.
-/

namespace ImbalancedChen.P4AOriginalFull87PairedSmoothPrimitive
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87PhysicalQAggregateInvoice (pairActualPhysicalModuli)
open P4AOriginalFull87FullRhoQBridge (supportedPhysicalRho)
open P4AOriginalFull87WeightedSharpSmooth (originalSmoothLiteral)
open P4AOriginalFull87WeightedPrimitiveRecentering
  (weightedPrimeMass weightedModulusPrimeMass
   original_smooth_primitive_recentered_same_rho)

/-- The same original signed rho from each actual policy is extended by
zero to the union of its REAL physical full-q moduli. The helper is applied
to two different genuine arithmetic tests, not a new sieve coefficient. -/
private theorem pair_actual_original_sum
    (R S : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (f : ℕ → ℝ) :
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

/-- The two ORIGINAL smooth prime sources, after subtracting the
difference of their SAME complete-rho densities, equal ONE paired
primitive AP discrepancy MINUS ONE paired modulus-prime correction.
N is nonprime to exclude the prime centre p=N in the actual smooth
prime-source identity. W can be signed; no new positivity is presumed.
No absolute value, independent sieve bound or second reserve is used. -/
theorem raw_licensed_smooth_primitive_same_full_q
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ)
    (hN : ¬ Nat.Prime N) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    (originalSmoothLiteral R N D cap w z L W -
      originalSmoothLiteral S N D cap w z L W) -
    weightedPrimeMass N D W *
      ((∑ d ∈ actualSmallRoughModuli (R false) N cap w z,
          actualSmallRoughRho (R false) N cap w z L d /
            (Nat.totient d : ℝ)) -
       (∑ d ∈ actualSmallRoughModuli (S false) N cap w z,
          actualSmallRoughRho (S false) N cap w z L d /
            (Nat.totient d : ℝ))) =
    (∑ d ∈ pairActualPhysicalModuli R S N cap w z,
       (supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d) *
       finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d) -
    (∑ d ∈ pairActualPhysicalModuli R S N cap w z,
       (supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d) *
       (weightedModulusPrimeMass N D d W / (Nat.totient d : ℝ))) := by
  dsimp only
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  let MR : Finset ℕ := actualSmallRoughModuli (R false) N cap w z
  let MS : Finset ℕ := actualSmallRoughModuli (S false) N cap w z
  let M : Finset ℕ := pairActualPhysicalModuli R S N cap w z
  let T : ℝ := weightedPrimeMass N D W
  let VR : ℝ := ∑ d ∈ MR,
    actualSmallRoughRho (R false) N cap w z L d / (Nat.totient d : ℝ)
  let VS : ℝ := ∑ d ∈ MS,
    actualSmallRoughRho (S false) N cap w z L d / (Nat.totient d : ℝ)
  let A : ℕ → ℝ := fun d =>
    finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d
  let C : ℕ → ℝ := fun d =>
    weightedModulusPrimeMass N D d W / (Nat.totient d : ℝ)
  have hR := original_smooth_primitive_recentered_same_rho
    R N D cap w z L W hN
  have hS := original_smooth_primitive_recentered_same_rho
    S N D cap w z L W hN
  change originalSmoothLiteral R N D cap w z L W - T * VR =
      (∑ d ∈ MR, actualSmallRoughRho (R false) N cap w z L d * A d) -
      (∑ d ∈ MR, actualSmallRoughRho (R false) N cap w z L d * C d) at hR
  change originalSmoothLiteral S N D cap w z L W - T * VS =
      (∑ d ∈ MS, actualSmallRoughRho (S false) N cap w z L d * A d) -
      (∑ d ∈ MS, actualSmallRoughRho (S false) N cap w z L d * C d) at hS
  have hA := pair_actual_original_sum R S N cap w z L A
  have hC := pair_actual_original_sum R S N cap w z L C
  change
    (∑ d ∈ MR, actualSmallRoughRho (R false) N cap w z L d * A d) -
    (∑ d ∈ MS, actualSmallRoughRho (S false) N cap w z L d * A d) =
    ∑ d ∈ M,
      (supportedPhysicalRho R N cap w z L d -
       supportedPhysicalRho S N cap w z L d) * A d at hA
  change
    (∑ d ∈ MR, actualSmallRoughRho (R false) N cap w z L d * C d) -
    (∑ d ∈ MS, actualSmallRoughRho (S false) N cap w z L d * C d) =
    ∑ d ∈ M,
      (supportedPhysicalRho R N cap w z L d -
       supportedPhysicalRho S N cap w z L d) * C d at hC
  change
    (originalSmoothLiteral R N D cap w z L W -
      originalSmoothLiteral S N D cap w z L W) - T * (VR - VS) =
    (∑ d ∈ M,
       (supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d) * A d) -
    (∑ d ∈ M,
       (supportedPhysicalRho R N cap w z L d -
        supportedPhysicalRho S N cap w z L d) * C d)
  calc
    _ = (originalSmoothLiteral R N D cap w z L W - T * VR) -
        (originalSmoothLiteral S N D cap w z L W - T * VS) := by ring
    _ = ((∑ d ∈ MR, actualSmallRoughRho (R false) N cap w z L d * A d) -
         (∑ d ∈ MR, actualSmallRoughRho (R false) N cap w z L d * C d)) -
        ((∑ d ∈ MS, actualSmallRoughRho (S false) N cap w z L d * A d) -
         (∑ d ∈ MS, actualSmallRoughRho (S false) N cap w z L d * C d)) := by
           rw [hR, hS]
    _ = ((∑ d ∈ MR, actualSmallRoughRho (R false) N cap w z L d * A d) -
         (∑ d ∈ MS, actualSmallRoughRho (S false) N cap w z L d * A d)) -
        ((∑ d ∈ MR, actualSmallRoughRho (R false) N cap w z L d * C d) -
         (∑ d ∈ MS, actualSmallRoughRho (S false) N cap w z L d * C d)) := by
           ring
    _ = _ := by rw [hA, hC]

end
end ImbalancedChen.P4AOriginalFull87PairedSmoothPrimitive
