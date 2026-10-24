import ImbalancedChen.RealPhysicalUpperWeightBridge
import ImbalancedChen.Part3DistributionTargets
import ImbalancedChen.ActualUpperCountingInputs

/-!
# P4B finite payment of the actual signed upper error

SOURCE-ONLY / YELLOW / UNCOMPILED, 2026-10-24.

The triangle inequality is applied after forming the exact physical signed
error. Its price is displayed explicitly, first with |rho|, then using the
proved one-bound of the actual attached coefficient. Zero coefficients are
removed before requesting any progression estimates. The coprime mean is
never replaced by total mass. No Part 3 distribution theorem is asserted:
the remaining analytic input bounds actual primitive discrepancies.
-/

namespace ImbalancedChen.P4B

noncomputable section

open scoped BigOperators
open Filter Topology

/-- The primitive discrepancy of the actual real source is exactly the
progression error occurring in its physical signed functional. -/
theorem realSource_primitiveDiscrepancy_eq
    (b : ℝ) (N : ℕ) (T : ℝ) (d : ℕ) :
    finitePrimitiveDiscrepancy (realHalfProductSource b N T) (fun _ => 1) N d =
      realHalfProductCongruenceMass b N T d -
        realHalfProductCoprimeMass b N T d / (Nat.totient d : ℝ) := by
  simp [finitePrimitiveDiscrepancy, finiteCongruenceMass, finiteCoprimeMass,
    realHalfProductCongruenceMass, realHalfProductCoprimeMass]

/-- Exact finite signed error, with precisely its coefficient-weighted
absolute progression-error payment. No positivity of rho is required. -/
theorem abs_realPhysicalDistributionError_le_weighted_progression_sum
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    |realPhysicalDistributionError b N T Q rho| ≤
      ∑ d ∈ Q, |rho d| *
        |finitePrimitiveDiscrepancy (realHalfProductSource b N T) (fun _ => 1) N d| := by
  unfold realPhysicalDistributionError
  calc
    |∑ d ∈ Q, rho d * (realHalfProductCongruenceMass b N T d -
        realHalfProductCoprimeMass b N T d / (Nat.totient d : ℝ))| ≤
        ∑ d ∈ Q, |rho d * (realHalfProductCongruenceMass b N T d -
          realHalfProductCoprimeMass b N T d / (Nat.totient d : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [abs_mul, realSource_primitiveDiscrepancy_eq]

/-- Displayed moduli with zero coefficient do not contribute to the
physical error, including when the displayed carrier is enlarged. -/
theorem realPhysicalDistributionError_eq_active
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    realPhysicalDistributionError b N T Q rho =
      realPhysicalDistributionError b N T (Q.filter (fun d => rho d ≠ 0)) rho := by
  classical
  unfold realPhysicalDistributionError
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _hd
  by_cases hrho : rho d = 0 <;> simp [hrho]

/-- Only the actual active support needs an absolute progression budget. -/
theorem abs_realPhysicalDistributionError_le_active_weighted_progression_sum
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    |realPhysicalDistributionError b N T Q rho| ≤
      ∑ d ∈ Q.filter (fun d => rho d ≠ 0), |rho d| *
        |finitePrimitiveDiscrepancy (realHalfProductSource b N T) (fun _ => 1) N d| := by
  classical
  rw [realPhysicalDistributionError_eq_active b N T Q rho]
  exact abs_realPhysicalDistributionError_le_weighted_progression_sum b N T _ rho

/-- Support-specific carrier of the literal coefficient. In particular,
displayed Rosser moduli above the small level need no analytic payment. -/
def actualActiveModuli (retainOdd : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) : Finset ℕ := by
  classical
  exact (actualSmallRoughModuli retainOdd N cap w z).filter
    (fun d => actualSmallRoughRho retainOdd N cap w z L d ≠ 0)

/-- Active moduli retain the real source's actual small/rough factors;
the small factor is strictly below L and the rough coefficient is nonzero. -/
theorem actualActiveModuli_factors
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) {d : ℕ}
    (hd : d ∈ actualActiveModuli retainOdd N cap w z L) :
    ∃ a ∈ actualSmallRosserSupport N cap w,
      ∃ c ∈ fixedRoughSupport retainOdd N cap w z,
        d = a * c ∧ (a : ℝ) < L ∧
          fixedRoughCoefficient retainOdd N cap w z c ≠ 0 := by
  classical
  exact actualSmallRoughRho_ne_zero_factors retainOdd N cap w z L
    (Finset.mem_filter.mp hd).2

/-- The actual coefficient's proved absolute one-bound removes the
coefficient from the payment, with no factorization multiplicity loss. -/
theorem abs_actualSmallRough_distribution_le_active_progression_sum
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L b T : ℝ) :
    |realPhysicalDistributionError b N T
      (actualSmallRoughModuli retainOdd N cap w z)
      (actualSmallRoughRho retainOdd N cap w z L)| ≤
        ∑ d ∈ actualActiveModuli retainOdd N cap w z L,
          |finitePrimitiveDiscrepancy (realHalfProductSource b N T) (fun _ => 1) N d| := by
  classical
  calc
    _ ≤ ∑ d ∈ actualActiveModuli retainOdd N cap w z L,
        |actualSmallRoughRho retainOdd N cap w z L d| *
          |finitePrimitiveDiscrepancy (realHalfProductSource b N T) (fun _ => 1) N d| :=
      abs_realPhysicalDistributionError_le_active_weighted_progression_sum
        b N T _ _
    _ ≤ _ := Finset.sum_le_sum fun d _hd => by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right
          (actualSmallRoughRho_abs_le_one retainOdd N cap w z L d)
          (abs_nonneg (finitePrimitiveDiscrepancy
            (realHalfProductSource b N T) (fun _ => 1) N d))

/-- Pointwise primitive discrepancies can be paid by any supplied budget.
No bound for the physical distribution functional is a hypothesis. -/
theorem actualSmallRough_distribution_paid
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L b T E : ℝ)
    (payment : ℕ → ℝ)
    (hprimitive : ∀ d ∈ actualActiveModuli retainOdd N cap w z L,
      |finitePrimitiveDiscrepancy (realHalfProductSource b N T) (fun _ => 1) N d| ≤
        payment d)
    (hpaid : (∑ d ∈ actualActiveModuli retainOdd N cap w z L, payment d) ≤ E) :
    |realPhysicalDistributionError b N T
      (actualSmallRoughModuli retainOdd N cap w z)
      (actualSmallRoughRho retainOdd N cap w z L)| ≤ E := by
  exact (abs_actualSmallRough_distribution_le_active_progression_sum
    retainOdd N cap w z L b T).trans
      ((Finset.sum_le_sum hprimitive).trans hpaid)

/-- Conversion to the exact eventual distribution input used by
ActualUpperCountingInputs. The analytic premise concerns actual primitive
progression discrepancies on active moduli, and is stronger than a signed
Part 3 estimate. This finite conversion does not claim that premise. -/
theorem eventually_attachedUpper_distribution_paid
    (b kappa nu r epsilon delta : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (hprimitive : ∀ᶠ N : ℕ in atTop, Even N →
      (∑ d ∈ actualActiveModuli (retain N) N (cap N)
          ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))
          ((N : ℝ) ^ (nu * epsilon)),
        |finitePrimitiveDiscrepancy
          (realHalfProductSource b N (manuscriptHalfProductCutoff kappa N))
          (fun _ => 1) N d|) ≤ delta * singularNormalization N) :
    ∀ᶠ N : ℕ in atTop, Even N →
      |realPhysicalDistributionError b N (manuscriptHalfProductCutoff kappa N)
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N)| ≤
          delta * singularNormalization N := by
  filter_upwards [hprimitive] with N hN
  intro hEven
  exact (abs_actualSmallRough_distribution_le_active_progression_sum
    (retain N) N (cap N) _ _ _ b (manuscriptHalfProductCutoff kappa N)).trans
      (hN hEven)

end

end ImbalancedChen.P4B
