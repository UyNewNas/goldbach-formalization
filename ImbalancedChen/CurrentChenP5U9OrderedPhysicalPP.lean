import ImbalancedChen.CurrentChenP5U9OrderedBranches

/-!
# Literal physical PP coefficients for the three actual U9 branches

SOURCE ONLY / UNCOMPILED. The preceding source-only candidate is the first
import. A fixed inverse permutation reconstructs the ORIGINAL marked label
from a physical ordered tuple in each branch. Thus each branch has a
modulus-independent zero-one coefficient on the literal Part3 three-prime
carrier, with exact finite reindexing before the one signed PP norm.

The branch index remains part of the family; overlapping sorted physical
tuples from different original branch labels are not deduplicated. Repeated
prime coordinates remain in the physical carrier. No distribution estimate
or adopted-K bound is a hypothesis or conclusion of this module.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Classical

/-- Recover the original (p₁,p₂,q) slots from the fixed branch permutation. -/
def p5z_u9_physicalInverse {N : ℕ} (j : Fin 3)
    (u : Fin 3 → Fin (N + 1)) : P5zU9Triple :=
  ![(⟨((u 1).val, (u 2).val), (u 0).val⟩ : P5zU9Triple),
    (⟨((u 0).val, (u 2).val), (u 1).val⟩ : P5zU9Triple),
    (⟨((u 0).val, (u 1).val), (u 2).val⟩ : P5zU9Triple)] j

theorem p5z_u9_orderedNat_physicalInverse {N : ℕ} (j : Fin 3)
    (u : Fin 3 → Fin (N + 1)) (i : Fin 3) :
    p5z_u9_orderedNat j (p5z_u9_physicalInverse j u) i = (u i).val := by
  fin_cases j <;> fin_cases i <;> simp [p5z_u9_physicalInverse, p5z_u9_orderedNat]

theorem p5z_u9_physicalInverse_product {N : ℕ} (j : Fin 3)
    (u : Fin 3 → Fin (N + 1)) :
    p5z_u9_product (p5z_u9_physicalInverse j u) = Part3.labelledProduct u := by
  calc
    _ = ∏ i : Fin 3, p5z_u9_orderedNat j (p5z_u9_physicalInverse j u) i :=
      (p5z_u9_orderedNat_product j _).symm
    _ = ∏ i : Fin 3, (u i).val := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact p5z_u9_orderedNat_physicalInverse j u i
    _ = _ := rfl

/-- Actual source membership is the sole coefficient gate. There is no
modulus argument and no primality filter on the receiver N-product. -/
def p5z_u9_orderedPhysicalWeight (j : Fin 3) (N : ℕ)
    (u : Fin 3 → Fin (N + 1)) : ℝ :=
  if p5z_u9_physicalInverse j u ∈ p5z_u9_orderBranch j N then 1 else 0

theorem p5z_u9_orderedPhysicalWeight_nonneg (j : Fin 3) (N : ℕ)
    (u : Fin 3 → Fin (N + 1)) : 0 ≤ p5z_u9_orderedPhysicalWeight j N u := by
  unfold p5z_u9_orderedPhysicalWeight
  split_ifs <;> norm_num

theorem p5z_u9_orderedPhysicalWeight_abs_le_one (j : Fin 3) (N : ℕ)
    (u : Fin 3 → Fin (N + 1)) : |p5z_u9_orderedPhysicalWeight j N u| ≤ 1 := by
  unfold p5z_u9_orderedPhysicalWeight
  split_ifs <;> norm_num

theorem p5z_u9_orderedPhysicalWeight_support {N : ℕ} {j : Fin 3}
    {u : Fin 3 → Fin (N + 1)} (hu : p5z_u9_orderedPhysicalWeight j N u ≠ 0) :
    p5z_u9_physicalInverse j u ∈ p5z_u9_orderBranch j N := by
  by_contra hn
  exact hu (by simp only [p5z_u9_orderedPhysicalWeight, if_neg hn])

/-- The nonzero coefficient has concrete sorted physical support and the
original positive prime-power gate. Receiver primality is still absent. -/
theorem p5z_u9_orderedPhysicalWeight_support_data {N : ℕ} {j : Fin 3}
    {u : Fin 3 → Fin (N + 1)} (hN : (1 : ℝ) ≤ N)
    (hu : p5z_u9_orderedPhysicalWeight j N u ≠ 0) :
    (u 0).val ≤ (u 1).val ∧ (u 1).val ≤ (u 2).val ∧
      Part3.labelledProduct u < N ∧ Nat.Coprime (Part3.labelledProduct u) N ∧
      Nat.Coprime (N - Part3.labelledProduct u) N ∧
      ∀ i : Fin 3, (N : ℝ) ^ (19 / 125 : ℝ) ≤ ((u i).val : ℝ) := by
  have ht := p5z_u9_orderedPhysicalWeight_support hu
  have hs := (Finset.mem_filter.mp ht).1
  have hsorted := p5z_u9_orderedNat_sorted ht
  have hp := p5z_u9_physicalInverse_product j u
  have hlower := p5z_u9_orderedNat_lower_power j hN hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [p5z_u9_orderedNat_physicalInverse] using hsorted.1
  · simpa only [p5z_u9_orderedNat_physicalInverse] using hsorted.2
  · simpa only [hp] using p5z_u9_switchedLabels_product_lt hs
  · simpa only [hp] using p5z_u9_order_product_coprime hs
  · simpa only [hp] using (p5z_u9_order_source_data hs).2.2.2.2.2
  · intro i
    simpa only [p5z_u9_orderedNat_physicalInverse] using hlower i

/-- Actual finite bijection to the physical source, with the original
branch label and all factor multiplicities retained. -/
theorem p5z_u9_orderedPhysicalWeight_sum (j : Fin 3) (N : ℕ) (G : ℕ → ℝ) :
    (∑ t ∈ p5z_u9_orderBranch j N, G (p5z_u9_product t)) =
      ∑ u ∈ Part3.labelledPrimeTuples 3 N,
        p5z_u9_orderedPhysicalWeight j N u * G (Part3.labelledProduct u) := by
  let encode : (t : P5zU9Triple) → t ∈ p5z_u9_orderBranch j N →
      (Fin 3 → Fin (N + 1)) := fun t ht i =>
    ⟨p5z_u9_orderedNat j t i,
      Nat.lt_succ_of_le (p5z_u9_orderedNat_prime_coprime_cap j
        (Finset.mem_filter.mp ht).1 i).2.2⟩
  have hencode_inverse (t : P5zU9Triple) (ht : t ∈ p5z_u9_orderBranch j N) :
      p5z_u9_physicalInverse j (encode t ht) = t := by
    apply p5z_u9_orderedNat_injective j
    funext i
    exact p5z_u9_orderedNat_physicalInverse j (encode t ht) i
  let T := (Part3.labelledPrimeTuples 3 N).filter
    (fun u => p5z_u9_physicalInverse j u ∈ p5z_u9_orderBranch j N)
  have hbij : (∑ t ∈ p5z_u9_orderBranch j N, G (p5z_u9_product t)) =
      ∑ u ∈ T, G (Part3.labelledProduct u) := by
    refine Finset.sum_bij encode ?_ ?_ ?_ ?_
    · intro t ht
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, fun i =>
          (p5z_u9_orderedNat_prime_coprime_cap j (Finset.mem_filter.mp ht).1 i).1⟩
      · rw [hencode_inverse t ht]
        exact ht
    · intro t ht v hv heq
      apply p5z_u9_orderedNat_injective j
      funext i
      exact congrArg (fun w : Fin 3 → Fin (N + 1) => (w i).val) heq
    · intro u hu
      have hinverse := (Finset.mem_filter.mp hu).2
      refine ⟨p5z_u9_physicalInverse j u, hinverse, ?_⟩
      funext i
      apply Fin.ext
      exact p5z_u9_orderedNat_physicalInverse j u i
    · intro t ht
      have hp : Part3.labelledProduct (encode t ht) = p5z_u9_product t :=
        p5z_u9_orderedNat_product j t
      exact congrArg G hp.symm
  calc
    _ = ∑ u ∈ T, G (Part3.labelledProduct u) := hbij
    _ = _ := by
      dsimp only [T]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u _hu
      by_cases hs : p5z_u9_physicalInverse j u ∈ p5z_u9_orderBranch j N <;>
        simp only [p5z_u9_orderedPhysicalWeight, hs, if_true, if_false, one_mul, zero_mul]

theorem p5z_u9_orderedPhysical_congruenceMass (j : Fin 3) (N ell : ℕ) :
    p5z_labelledCongruenceMass (p5z_u9_orderBranch j N) p5z_u9_product (fun _ => 1) N ell =
      p5z_labelledCongruenceMass (Part3.labelledPrimeTuples 3 N) Part3.labelledProduct
        (p5z_u9_orderedPhysicalWeight j N) N ell := by
  have h := p5z_u9_orderedPhysicalWeight_sum j N
    (fun m => if Nat.ModEq ell m N then 1 else 0)
  simpa only [p5z_labelledCongruenceMass, mul_ite, mul_one, mul_zero] using h

theorem p5z_u9_orderedPhysical_coprimeMass (j : Fin 3) (N ell : ℕ) :
    p5z_labelledCoprimeMass (p5z_u9_orderBranch j N) p5z_u9_product (fun _ => 1) ell =
      p5z_labelledCoprimeMass (Part3.labelledPrimeTuples 3 N) Part3.labelledProduct
        (p5z_u9_orderedPhysicalWeight j N) ell := by
  have h := p5z_u9_orderedPhysicalWeight_sum j N
    (fun m => if Nat.Coprime m ell then 1 else 0)
  simpa only [p5z_labelledCoprimeMass, mul_ite, mul_one, mul_zero] using h

/-- The original branch error is literally the Part3 physical PP error
with this concrete original coefficient, not an assumed target estimate. -/
theorem p5z_u9_orderBranch_distribution_eq_physicalPP
    (j : Fin 3) (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (p5z_u9_orderBranch j N) p5z_u9_product
        (fun _ => 1) N Q rho =
      Part3.primeProductSignedError 3 N N Q rho (p5z_u9_orderedPhysicalWeight j N) := by
  calc
    _ = p5z_labelledDistributionError (Part3.labelledPrimeTuples 3 N) Part3.labelledProduct
        (p5z_u9_orderedPhysicalWeight j N) N Q rho := by
      unfold p5z_labelledDistributionError
      simp_rw [p5z_u9_orderedPhysical_congruenceMass, p5z_u9_orderedPhysical_coprimeMass]
    _ = _ := p5z_labelledDistributionError_eq_primeProductSignedError
      3 N N Q rho (p5z_u9_orderedPhysicalWeight j N)

/-- Exact physical-PP decomposition of the whole actual switched source,
retaining the same rho and one original signed error until after summation. -/
theorem p5z_u9_orderedPhysicalPP_decomposition (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (p5z_u9_switchedLabels N) p5z_u9_product
        (fun _ => 1) N Q rho =
      Part3.primeProductSignedError 3 N N Q rho (p5z_u9_orderedPhysicalWeight 0 N) +
      Part3.primeProductSignedError 3 N N Q rho (p5z_u9_orderedPhysicalWeight 1 N) +
      Part3.primeProductSignedError 3 N N Q rho (p5z_u9_orderedPhysicalWeight 2 N) := by
  rw [p5z_u9_orderBranches_distribution]
  simp only [p5z_u9_orderBranch_distribution_eq_physicalPP]

end

end ImbalancedChen
