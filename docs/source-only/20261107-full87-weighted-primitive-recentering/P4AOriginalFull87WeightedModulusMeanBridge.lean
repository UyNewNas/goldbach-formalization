import ImbalancedChen.P4AOriginalFull87WeightedPrimitiveRecentering
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

The manuscript's smooth singleton PP uses a q-dependent analytic X_W^(q).
It is *not* automatically the finite weighted prime mass. This equality
keeps their exact mismatch as an additional signed physical sum, with no
bound assumed and no replacement of rho. The analytic identification is an
open obligation, not a hypothesis silently granted to the main result.
-/

namespace ImbalancedChen.P4AOriginalFull87WeightedModulusMeanBridge
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87WeightedSharpSmooth
open P4AOriginalFull87WeightedPrimitiveRecentering

/-- Exact algebraic bridge from the finite smooth original-prime count
to ANY q-dependent comparison mean, including the one eventually supplied
by the permitted smooth singleton PP. All THREE terms survive. -/
theorem original_smooth_modulus_dependent_mean_exact
    (P : Bool → List ℕ → Bool)
    (N D cap : ℕ) (w z L : ℝ) (W : ℕ → ℝ)
    (X : ℕ → ℝ) (hN : ¬ Nat.Prime N) :
    originalSmoothLiteral P N D cap w z L W -
      (∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
        actualSmallRoughRho (P false) N cap w z L d *
          (X d / (Nat.totient d : ℝ))) =
      (∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
        actualSmallRoughRho (P false) N cap w z L d *
          finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d) -
      (∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
        actualSmallRoughRho (P false) N cap w z L d *
          (weightedModulusPrimeMass N D d W / (Nat.totient d : ℝ))) +
      (∑ d ∈ actualSmallRoughModuli (P false) N cap w z,
        actualSmallRoughRho (P false) N cap w z L d *
          ((weightedPrimeMass N D W - X d) / (Nat.totient d : ℝ))) := by
  classical
  let Q := actualSmallRoughModuli (P false) N cap w z
  let ρ := actualSmallRoughRho (P false) N cap w z L
  let T := weightedPrimeMass N D W
  have h := original_smooth_primitive_recentered_same_rho
    P N D cap w z L W hN
  change originalSmoothLiteral P N D cap w z L W -
    T * (∑ d ∈ Q, ρ d / (Nat.totient d : ℝ)) =
    (∑ d ∈ Q, ρ d *
      finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d) -
    (∑ d ∈ Q, ρ d *
      (weightedModulusPrimeMass N D d W / (Nat.totient d : ℝ))) at h
  have hmain :
      (∑ d ∈ Q, ρ d * (X d / (Nat.totient d : ℝ))) =
      T * (∑ d ∈ Q, ρ d / (Nat.totient d : ℝ)) -
      (∑ d ∈ Q, ρ d * ((T - X d) / (Nat.totient d : ℝ))) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  change originalSmoothLiteral P N D cap w z L W -
    (∑ d ∈ Q, ρ d * (X d / (Nat.totient d : ℝ))) =
    (∑ d ∈ Q, ρ d *
      finitePrimitiveDiscrepancy (chenPrimePrefix (N + D)) W N d) -
    (∑ d ∈ Q, ρ d *
      (weightedModulusPrimeMass N D d W / (Nat.totient d : ℝ))) +
    (∑ d ∈ Q, ρ d * ((T - X d) / (Nat.totient d : ℝ)))
  rw [hmain]
  linarith

end
end ImbalancedChen.P4AOriginalFull87WeightedModulusMeanBridge
