import ImbalancedChen.P1Full87TrueDUnitBound
import Mathlib.Tactic

/-!
P1.4 SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The previous real small-d delta has a pointwise bound of one, but that
bound alone does not identify the location or SIGN of the density change.
Here we use the existing exact physical-density and true-d test identities
to prove that the entire RAW/LICENSED density difference is carried by
the symmetric difference of their ORIGINAL fixed rough supports.

The common Rosser beta-plus/minus densities are kept unchanged. The
summands on old-only and fresh-only rough carriers have opposite signs;
overlapping rough support cancels exactly, even though the integer
moduli themselves have the full small/rough attachment. No new mask is
attached to an inherited branch, and no analytic distribution or H_N
bound is imported. The policy difference is NOT certified as a permitted
single causal PP coefficient by this finite equality.
-/

namespace ImbalancedChen.P1Full87TrueDRoughSymmDiffDensity

noncomputable section
open Classical
open scoped BigOperators
open P1Full87TrueDPolicyDelta (trueDDeltaSupport trueDDeltaRho trueDDeltaRho_test)

/-- The SAME small beta densities and Mobius sign for every rough modulus,
independent of whether its causal policy retains it. This is an algebraic
density contribution, not a new coefficient or an external sieve bound. -/
def commonRoughDensityTerm (N cap : ℕ) (w L : ℝ) (b : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius b : ℝ) / (Nat.totient b : ℝ)) *
    (if 0 ≤ (ArithmeticFunction.moebius b : ℝ) then
      reciprocalTotientDensity (actualSmallRosserSupport N cap w)
        (actualSmallRosserPlus N cap w L)
    else
      reciprocalTotientDensity (actualSmallRosserSupport N cap w)
        (actualSmallRosserMinus N cap w L))

/-- Exact density of a single ACTUAL finite coefficient on its own original
rough carrier. The sign-dependent beta choice is not suppressed. -/
private theorem actual_density_eq_common_rough_terms
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    physicalDensitySum
      (actualSmallRoughModuli retainOdd N cap w z)
      (actualSmallRoughRho retainOdd N cap w z L) =
      ∑ b ∈ fixedRoughSupport retainOdd N cap w z,
        commonRoughDensityTerm N cap w L b := by
  rw [actualSmallRoughRho_density_eq retainOdd N cap w z L]
  unfold signSensitiveReciprocalTotientDensity
  apply Finset.sum_congr rfl
  intro b hb
  have hmem :
      b ∈ oddFirstExitRetainedModuli retainOdd (fun _ => 1)
        (roughPrimeUniverse N cap w z) := by
    simpa only [fixedRoughSupport] using hb
  have hc :
      fixedRoughCoefficient retainOdd N cap w z b =
        (ArithmeticFunction.moebius b : ℝ) := by
    simp [fixedRoughCoefficient, oddFirstExitRetainedCoefficient, hmem]
  rw [hc]
  rfl

/-- The genuine true-d coefficient difference has an exact density
difference of the two original finite physical coefficient densities.
Crucially this is one exact same-rho FINITE test, not subtraction of
unrelated upper/lower asymptotic sieve estimates. -/
private theorem actual_delta_density_eq_difference
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    physicalDensitySum (trueDDeltaSupport old fresh N cap w z)
        (trueDDeltaRho old fresh N cap w z L) =
      physicalDensitySum
        (actualSmallRoughModuli fresh N cap w z)
        (actualSmallRoughRho fresh N cap w z L) -
      physicalDensitySum
        (actualSmallRoughModuli old N cap w z)
        (actualSmallRoughRho old N cap w z L) := by
  simpa only [physicalDensitySum, div_eq_mul_inv] using
    (trueDDeltaRho_test old fresh N cap w z L
      (fun d => (Nat.totient d : ℝ)⁻¹))

/-- For a SINGLE identical function f, the common portion of two
finite carriers cancels before either absolute value is taken. -/
private theorem finite_sum_sub_eq_symmetric_difference
    (S T : Finset ℕ) (f : ℕ → ℝ) :
    (∑ x ∈ S, f x) - (∑ x ∈ T, f x) =
      (∑ x ∈ (S \ T), f x) - (∑ x ∈ (T \ S), f x) := by
  classical
  have hS : (S \ T) ∪ (S ∩ T) = S := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hT : (T \ S) ∪ (S ∩ T) = T := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hDisS : Disjoint (S \ T) (S ∩ T) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxi
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mp hxi).2
  have hDisT : Disjoint (T \ S) (S ∩ T) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxi
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mp hxi).1
  have hSumS :
      (∑ x ∈ S, f x) =
        (∑ x ∈ (S \ T), f x) + (∑ x ∈ (S ∩ T), f x) := by
    calc
      (∑ x ∈ S, f x) =
        ∑ x ∈ (S \ T) ∪ (S ∩ T), f x := by rw [hS]
      _ = _ := Finset.sum_union hDisS
  have hSumT :
      (∑ x ∈ T, f x) =
        (∑ x ∈ (T \ S), f x) + (∑ x ∈ (S ∩ T), f x) := by
    calc
      (∑ x ∈ T, f x) =
        ∑ x ∈ (T \ S) ∪ (S ∩ T), f x := by rw [hT]
      _ = _ := Finset.sum_union hDisT
  rw [hSumS, hSumT]
  ring

/-- Exact non-overlap invoice for the difference of REAL physical
densities. It uses only the original retained rough sets and the ONE
common sign-sensitive small beta pair. It has no artificial mask and no
duplicate charge for the intersection. -/
theorem trueDDeltaRho_density_eq_changed_rough
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    physicalDensitySum (trueDDeltaSupport old fresh N cap w z)
        (trueDDeltaRho old fresh N cap w z L) =
      (∑ b ∈ (fixedRoughSupport fresh N cap w z \
               fixedRoughSupport old N cap w z),
          commonRoughDensityTerm N cap w L b) -
      (∑ b ∈ (fixedRoughSupport old N cap w z \
               fixedRoughSupport fresh N cap w z),
          commonRoughDensityTerm N cap w L b) := by
  calc
    _ = (∑ b ∈ fixedRoughSupport fresh N cap w z,
            commonRoughDensityTerm N cap w L b) -
        (∑ b ∈ fixedRoughSupport old N cap w z,
            commonRoughDensityTerm N cap w L b) := by
          rw [actual_delta_density_eq_difference,
            actual_density_eq_common_rough_terms,
            actual_density_eq_common_rough_terms]
    _ = _ := finite_sum_sub_eq_symmetric_difference _ _ _

/-- Install the SAME rough-carrier cancellation in the actual RAW and
LICENSED full-87 policy producers, not in a generic fifth-policy fresh
placeholder. Original fifth/sixth parent and each policy remain unchanged. -/
theorem actual_full87_true_d_density_eq_changed_rough
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    let F := fixedRoughSupport (S false) N cap w z
    let O := fixedRoughSupport (R false) N cap w z
    physicalDensitySum
      (trueDDeltaSupport (R false) (S false) N cap w z)
      (trueDDeltaRho (R false) (S false) N cap w z L) =
      (∑ b ∈ (F \ O), commonRoughDensityTerm N cap w L b) -
      (∑ b ∈ (O \ F), commonRoughDensityTerm N cap w L b) := by
  dsimp only
  exact trueDDeltaRho_density_eq_changed_rough
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ) false)
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om
      (N : ℝ) false) N cap w z L

end
end ImbalancedChen.P1Full87TrueDRoughSymmDiffDensity
