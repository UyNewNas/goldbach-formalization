import ImbalancedChen.P1Full87LowPhysicalDelta
import ImbalancedChen.P1Full87TrueDUnitBound
import ImbalancedChen.RealPhysicalUpperWeightBridge
import Mathlib.Tactic

/-!
P1.4 SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Actual RAW/LICENSED full87 physical coefficient difference, not a surrogate
test family.  A preceding source-only candidate proves that this difference
vanishes for physical d < w^5.  Here that exact arithmetic zero is carried
through the literal real half-product source, its primitive residue error,
its exact coprime correction and its SAME reciprocal-totient density.

Only the upper physical modulus carrier is filtered, because the actual
coefficient is provably zero on its complement.  Neither RAW nor LICENSED
is separately filtered.  The shifted receiver source, occurrence histories,
Möbius signs, Rosser beta attachment and all original endpoint conventions
remain unchanged.  The signed delta is NOT asserted to majorize anything.
The finite absolute estimate below is NOT an H_N or asymptotic estimate.
-/

namespace ImbalancedChen.P1Full87RealPrimitiveTail

noncomputable section
open Classical
open scoped BigOperators
open P1Full87TrueDPolicyDelta (trueDDeltaRho)

/-- Reindex a finite signed invoice when its ORIGINAL coefficient vanishes
on the strict low-modulus part.  No assertion about the two summands
producing the difference is made. -/
private theorem sum_eq_high_of_low_zero
    (Q : Finset ℕ) (rho F : ℕ → ℝ) (w : ℝ)
    (hlow : ∀ d : ℕ, (d : ℝ) < w ^ 5 → rho d = 0) :
    (∑ d ∈ Q, rho d * F d) =
      ∑ d ∈ Q.filter (fun d => w ^ 5 ≤ (d : ℝ)), rho d * F d := by
  classical
  have hbottom :
      (∑ d ∈ Q.filter (fun d => ¬w ^ 5 ≤ (d : ℝ)),
        rho d * F d) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    have hlt : (d : ℝ) < w ^ 5 :=
      lt_of_not_ge (Finset.mem_filter.mp hd).2
    rw [hlow d hlt, zero_mul]
  calc
    (∑ d ∈ Q, rho d * F d) =
        (∑ d ∈ Q.filter (fun d => w ^ 5 ≤ (d : ℝ)), rho d * F d) +
          (∑ d ∈ Q.filter (fun d => ¬w ^ 5 ≤ (d : ℝ)), rho d * F d) :=
      (Finset.sum_filter_add_sum_filter_not Q
        (fun d : ℕ => w ^ 5 ≤ (d : ℝ))
        (fun d => rho d * F d)).symm
    _ = _ := by rw [hbottom, add_zero]

/-- All three EXACT real prime-product books for the SAME original
physical delta have zero low-d terms.  Moreover the primitive signed
distribution error costs at most ONE absolute primitive discrepancy for
each active physical d.  This uses the true unit coefficient bound, not
the old two-bound and not two independent RAW/LICENSED absolute estimates.

The full H_N payment, the causal PP coefficient licence, and the actual
fixed full87 epsilon remain separate obligations. -/
theorem actual_full87_real_primitive_three_books_high_only
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (b : ℝ) (N cap : ℕ) (w z L T : ℝ) (hw : 1 ≤ w) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
    let Q := actualSmallRoughModuli (S false) N cap w z ∪
      actualSmallRoughModuli (R false) N cap w z
    let high := Q.filter (fun d => w ^ 5 ≤ (d : ℝ))
    let rho := trueDDeltaRho (R false) (S false) N cap w z L
    physicalDensitySum Q rho = physicalDensitySum high rho ∧
    realPhysicalCoprimeCorrection b N T Q rho =
      realPhysicalCoprimeCorrection b N T high rho ∧
    realPhysicalDistributionError b N T Q rho =
      realPhysicalDistributionError b N T high rho ∧
    |realPhysicalDistributionError b N T Q rho| ≤
      ∑ d ∈ high,
        |realHalfProductCongruenceMass b N T d -
          realHalfProductCoprimeMass b N T d / (Nat.totient d : ℝ)| := by
  dsimp only
  classical
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
  let Q := actualSmallRoughModuli (S false) N cap w z ∪
    actualSmallRoughModuli (R false) N cap w z
  let high := Q.filter (fun d => w ^ 5 ≤ (d : ℝ))
  let rho := trueDDeltaRho (R false) (S false) N cap w z L
  let D : ℕ → ℝ := fun d =>
    realHalfProductCongruenceMass b N T d -
      realHalfProductCoprimeMass b N T d / (Nat.totient d : ℝ)
  have hlow (d : ℕ) (hd : (d : ℝ) < w ^ 5) : rho d = 0 := by
    exact P1Full87LowPhysicalDelta.actual_full87_true_d_delta_zero_below_fifth
      delta n e q om N cap d w z L hw hd
  have hdensity :
      physicalDensitySum Q rho = physicalDensitySum high rho := by
    simpa only [physicalDensitySum, div_eq_mul_inv, high] using
      (sum_eq_high_of_low_zero Q rho
        (fun d => (Nat.totient d : ℝ)⁻¹) w hlow)
  have hcoprime :
      realPhysicalCoprimeCorrection b N T Q rho =
        realPhysicalCoprimeCorrection b N T high rho := by
    simpa only [realPhysicalCoprimeCorrection, high] using
      (sum_eq_high_of_low_zero Q rho
        (fun d =>
          (realHalfProductCoprimeMass b N T d -
            ((realHalfProductSource b N T).card : ℝ)) /
              (Nat.totient d : ℝ)) w hlow)
  have hdistribution :
      realPhysicalDistributionError b N T Q rho =
        realPhysicalDistributionError b N T high rho := by
    simpa only [realPhysicalDistributionError, D, high] using
      (sum_eq_high_of_low_zero Q rho D w hlow)
  have habsolute :
      |∑ d ∈ high, rho d * D d| ≤ ∑ d ∈ high, |D d| := by
    calc
      |∑ d ∈ high, rho d * D d| ≤
          ∑ d ∈ high, |rho d * D d| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ high, |D d| := by
        apply Finset.sum_le_sum
        intro d hd
        have hunit : |rho d| ≤ (1 : ℝ) :=
          P1Full87TrueDUnitBound.trueDDeltaRho_abs_le_one
            (R false) (S false) N cap d w z L
        rw [abs_mul]
        calc
          |rho d| * |D d| ≤ 1 * |D d| :=
            mul_le_mul_of_nonneg_right hunit (abs_nonneg _)
          _ = |D d| := one_mul _
  refine ⟨hdensity, hcoprime, hdistribution, ?_⟩
  rw [hdistribution]
  change |∑ d ∈ high, rho d * D d| ≤ ∑ d ∈ high, |D d|
  exact habsolute

/-- The literal real HALF-PRODUCT RECEIVER sum of the same RAW/LICENSED
physical delta has an exact three-book expansion supported only at
d >= w^5.  The original complete shifted source remains untouched.
This is an equality, not a positive sieve majorant nor a PP estimate.
It does not pay any primitive discrepancy or coprime correction twice. -/
theorem actual_full87_real_receiver_high_three_books
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (b : ℝ) (N cap : ℕ) (w z L T : ℝ) (hw : 1 ≤ w) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
    let Q := actualSmallRoughModuli (S false) N cap w z ∪
      actualSmallRoughModuli (R false) N cap w z
    let high := Q.filter (fun d => w ^ 5 ≤ (d : ℝ))
    let rho := trueDDeltaRho (R false) (S false) N cap w z L
    (∑ m ∈ realHalfProductSource b N T,
      physicalDivisorSum Q rho (N - m)) =
      ((realHalfProductSource b N T).card : ℝ) *
        physicalDensitySum high rho +
      realPhysicalCoprimeCorrection b N T high rho +
      realPhysicalDistributionError b N T high rho := by
  dsimp only
  classical
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
  let Q := actualSmallRoughModuli (S false) N cap w z ∪
    actualSmallRoughModuli (R false) N cap w z
  let high := Q.filter (fun d => w ^ 5 ≤ (d : ℝ))
  let rho := trueDDeltaRho (R false) (S false) N cap w z L
  have hlow (d : ℕ) (hd : (d : ℝ) < w ^ 5) : rho d = 0 := by
    exact P1Full87LowPhysicalDelta.actual_full87_true_d_delta_zero_below_fifth
      delta n e q om N cap d w z L hw hd
  calc
    (∑ m ∈ realHalfProductSource b N T,
      physicalDivisorSum Q rho (N - m)) =
        ∑ d ∈ Q, rho d * realHalfProductCongruenceMass b N T d :=
      sum_physicalDivisorSum_realHalfProductSource b N T Q rho
    _ = ∑ d ∈ high, rho d * realHalfProductCongruenceMass b N T d :=
      sum_eq_high_of_low_zero Q rho
        (fun d => realHalfProductCongruenceMass b N T d) w hlow
    _ = ((realHalfProductSource b N T).card : ℝ) *
          physicalDensitySum high rho +
        realPhysicalCoprimeCorrection b N T high rho +
        realPhysicalDistributionError b N T high rho :=
      sum_rho_mul_realHalfProductCongruenceMass_eq b N T high rho

end
end ImbalancedChen.P1Full87RealPrimitiveTail
