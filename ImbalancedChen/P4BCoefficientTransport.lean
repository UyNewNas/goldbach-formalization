import ImbalancedChen.ActualUpperPolicyDensity
import ImbalancedChen.ActualUpperCountingInputs
import ImbalancedChen.RealPhysicalUpperWeightBridge

/-!
# Finite transport for the original physical upper coefficient

SOURCE-ONLY DRAFT: yellow / uncompiled. This file makes no analytic claim.
FiniteUpperCarrierCore already proves all four transports for its specific
raw rough-carrier enlargement; those proofs are not repeated here.
The missing interface here is arbitrary coefficient extensionality on finite
carriers, allowing zero coefficients to be inserted or deleted. Equality of
densities alone is deliberately insufficient: the hypotheses identify the
original coefficient before any kernel or source is selected.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Equality on the intersection and zero values on both exclusive parts
preserve every signed linear functional. No positivity is required. -/
theorem p4b_sum_mul_transport_of_common_zero
    (Q R : Finset ℕ) (rho sigma F : ℕ → ℝ)
    (hcommon : ∀ d ∈ Q ∩ R, rho d = sigma d)
    (hleft : ∀ d ∈ Q, d ∉ R → rho d = 0)
    (hright : ∀ d ∈ R, d ∉ Q → sigma d = 0) :
    (∑ d ∈ Q, rho d * F d) = ∑ d ∈ R, sigma d * F d := by
  classical
  calc
    (∑ d ∈ Q, rho d * F d) = ∑ d ∈ Q ∩ R, rho d * F d := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro d hd hnot
      have hdR : d ∉ R := fun hr => hnot (Finset.mem_inter.mpr ⟨hd, hr⟩)
      rw [hleft d hd hdR, zero_mul]
    _ = ∑ d ∈ Q ∩ R, sigma d * F d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [hcommon d hd]
    _ = ∑ d ∈ R, sigma d * F d := by
      apply Finset.sum_subset Finset.inter_subset_right
      intro d hd hnot
      have hdQ : d ∉ Q := fun hq => hnot (Finset.mem_inter.mpr ⟨hq, hd⟩)
      rw [hright d hd hdQ, zero_mul]

/-- All four physical uses transfer together. The signed error remains one
sum before absolute values; totient zero and modulus zero need no exceptions. -/
theorem p4b_physical_transport_of_common_zero
    (b : ℝ) (N : ℕ) (T : ℝ) (Q R : Finset ℕ) (rho sigma : ℕ → ℝ)
    (hcommon : ∀ d ∈ Q ∩ R, rho d = sigma d)
    (hleft : ∀ d ∈ Q, d ∉ R → rho d = 0)
    (hright : ∀ d ∈ R, d ∉ Q → sigma d = 0) :
    physicalDensitySum Q rho = physicalDensitySum R sigma ∧
      (∀ n : ℕ, physicalDivisorSum Q rho n = physicalDivisorSum R sigma n) ∧
      realPhysicalCoprimeCorrection b N T Q rho =
        realPhysicalCoprimeCorrection b N T R sigma ∧
      realPhysicalDistributionError b N T Q rho =
        realPhysicalDistributionError b N T R sigma := by
  classical
  have hsum := p4b_sum_mul_transport_of_common_zero Q R rho sigma
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [physicalDensitySum, div_eq_mul_inv] using
      hsum (fun d => (Nat.totient d : ℝ)⁻¹) hcommon hleft hright
  · intro n
    simpa only [physicalDivisorSum, mul_ite, mul_one, mul_zero] using
      hsum (fun d => if d ∣ n then 1 else 0) hcommon hleft hright
  · exact hsum (fun d =>
      (realHalfProductCoprimeMass b N T d -
        ((realHalfProductSource b N T).card : ℝ)) / (Nat.totient d : ℝ))
      hcommon hleft hright
  · exact hsum (fun d => realHalfProductCongruenceMass b N T d -
      realHalfProductCoprimeMass b N T d / (Nat.totient d : ℝ))
      hcommon hleft hright

/-- On a fixed displayed carrier, equality only on that carrier suffices;
no global function equality or support assumptions are necessary. -/
theorem p4b_physical_transport_of_eq_on
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho sigma : ℕ → ℝ)
    (hcoeff : ∀ d ∈ Q, rho d = sigma d) :
    physicalDensitySum Q rho = physicalDensitySum Q sigma ∧
      (∀ n : ℕ, physicalDivisorSum Q rho n = physicalDivisorSum Q sigma n) ∧
      realPhysicalCoprimeCorrection b N T Q rho =
        realPhysicalCoprimeCorrection b N T Q sigma ∧
      realPhysicalDistributionError b N T Q rho =
        realPhysicalDistributionError b N T Q sigma := by
  apply p4b_physical_transport_of_common_zero b N T Q Q rho sigma
  · intro d hd
    exact hcoeff d (Finset.mem_inter.mp hd).1
  · intro d hd hnot
    exact (hnot hd).elim
  · intro d hd hnot
    exact (hnot hd).elim

/-- Pointwise agreement on the union, with each function zero outside its
own carrier on that union, is an alternative compiler-facing interface. -/
theorem p4b_physical_transport_of_union
    (b : ℝ) (N : ℕ) (T : ℝ) (Q R : Finset ℕ) (rho sigma : ℕ → ℝ)
    (hcoeff : ∀ d ∈ Q ∪ R, rho d = sigma d)
    (hrho : ∀ d ∈ R, d ∉ Q → rho d = 0)
    (hsigma : ∀ d ∈ Q, d ∉ R → sigma d = 0) :
    physicalDensitySum Q rho = physicalDensitySum R sigma ∧
      (∀ n : ℕ, physicalDivisorSum Q rho n = physicalDivisorSum R sigma n) ∧
      realPhysicalCoprimeCorrection b N T Q rho =
        realPhysicalCoprimeCorrection b N T R sigma ∧
      realPhysicalDistributionError b N T Q rho =
        realPhysicalDistributionError b N T R sigma := by
  apply p4b_physical_transport_of_common_zero b N T Q R rho sigma
  · intro d hd
    exact hcoeff d (Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hd).1))
  · intro d hd hnot
    rw [hcoeff d (Finset.mem_union.mpr (Or.inl hd))]
    exact hsigma d hd hnot
  · intro d hd hnot
    rw [← hcoeff d (Finset.mem_union.mpr (Or.inr hd))]
    exact hrho d hd hnot

/-- Exact policy adapter at the actual counting parameters. The retained
policy is globally even-retaining; no density bound is a hypothesis. -/
theorem p4b_attachedUpperModuli_eq_firstExitAttachment
    (nu r epsilon : ℝ) (retained : ℕ → Bool → List ℕ → Bool)
    (heven : ∀ N pre, retained N true pre = true) (cap : ℕ → ℕ) (N : ℕ) :
    attachedUpperModuli nu r epsilon (fun N => retained N false) cap N =
      smallRoughModuli
        (actualSmallRosserSupport N (cap N) ((N : ℝ) ^ (nu * epsilon ^ 2)))
        (firstExitRetainedModuli (retained N)
          (roughPrimeUniverse N (cap N)
            ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r)))) := by
  exact actualSmallRoughModuli_eq_firstExitAttachment (retained N) (heven N)
    N (cap N) ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))

/-- The adapter identifies the original arithmetic function at every
modulus, before a density kernel, test integer or source is supplied. -/
theorem p4b_attachedUpperCoefficient_eq_firstExitAttachment
    (nu r epsilon : ℝ) (retained : ℕ → Bool → List ℕ → Bool)
    (heven : ∀ N pre, retained N true pre = true) (cap : ℕ → ℕ) (N : ℕ) :
    attachedUpperCoefficient nu r epsilon (fun N => retained N false) cap N =
      smallRoughRho
        (actualSmallRosserSupport N (cap N) ((N : ℝ) ^ (nu * epsilon ^ 2)))
        (firstExitRetainedModuli (retained N)
          (roughPrimeUniverse N (cap N)
            ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))))
        (fun d => (firstExitRetainedCoefficient (retained N)
          (roughPrimeUniverse N (cap N)
            ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))) d : ℝ))
        (actualSmallRosserMinus N (cap N) ((N : ℝ) ^ (nu * epsilon ^ 2))
          ((N : ℝ) ^ (nu * epsilon)))
        (actualSmallRosserPlus N (cap N) ((N : ℝ) ^ (nu * epsilon ^ 2))
          ((N : ℝ) ^ (nu * epsilon))) := by
  exact actualSmallRoughRho_eq_firstExitAttachment (retained N) (heven N)
    N (cap N) ((N : ℝ) ^ (nu * epsilon ^ 2)) ((N : ℝ) ^ (nu * r))
    ((N : ℝ) ^ (nu * epsilon))

/-- The literal attached coefficient is zero outside its displayed carrier.
This is a finite support fact, with no exponent or analytic conditions. -/
theorem p4b_attachedUpperCoefficient_eq_zero_of_not_mem
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (N d : ℕ) (hd : d ∉ attachedUpperModuli nu r epsilon retain cap N) :
    attachedUpperCoefficient nu r epsilon retain cap N d = 0 := by
  exact smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hd

/-- A computed coefficient on any finite carrier transfers to the original
attached coefficient from a pointwise check on the union and coverage of
the original active support. Displayed zero terms may be added or deleted.
The density and signed error conclusions are proved here, not assumptions. -/
theorem p4b_attachedUpper_transport_of_union
    (b : ℝ) (N : ℕ) (T nu r epsilon : ℝ)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hcoeff : ∀ d ∈ Q ∪ attachedUpperModuli nu r epsilon retain cap N,
      rho d = attachedUpperCoefficient nu r epsilon retain cap N d)
    (hactive : ∀ d ∈ attachedUpperModuli nu r epsilon retain cap N,
      attachedUpperCoefficient nu r epsilon retain cap N d ≠ 0 → d ∈ Q) :
    physicalDensitySum Q rho =
        physicalDensitySum (attachedUpperModuli nu r epsilon retain cap N)
          (attachedUpperCoefficient nu r epsilon retain cap N) ∧
      (∀ n : ℕ, physicalDivisorSum Q rho n =
        physicalDivisorSum (attachedUpperModuli nu r epsilon retain cap N)
          (attachedUpperCoefficient nu r epsilon retain cap N) n) ∧
      realPhysicalCoprimeCorrection b N T Q rho =
        realPhysicalCoprimeCorrection b N T
          (attachedUpperModuli nu r epsilon retain cap N)
          (attachedUpperCoefficient nu r epsilon retain cap N) ∧
      realPhysicalDistributionError b N T Q rho =
        realPhysicalDistributionError b N T
          (attachedUpperModuli nu r epsilon retain cap N)
          (attachedUpperCoefficient nu r epsilon retain cap N) := by
  classical
  apply p4b_physical_transport_of_common_zero b N T Q
    (attachedUpperModuli nu r epsilon retain cap N) rho
    (attachedUpperCoefficient nu r epsilon retain cap N)
  · intro d hd
    exact hcoeff d (Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hd).1))
  · intro d hd hnot
    rw [hcoeff d (Finset.mem_union.mpr (Or.inl hd))]
    exact p4b_attachedUpperCoefficient_eq_zero_of_not_mem nu r epsilon retain cap N d hnot
  · intro d hd hnot
    by_contra hne
    exact hnot (hactive d hd hne)

end

end ImbalancedChen
