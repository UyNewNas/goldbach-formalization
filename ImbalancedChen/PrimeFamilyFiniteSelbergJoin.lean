import ImbalancedChen.ActualSelbergMain
import ImbalancedChen.P5zMarkedPrimeFamilyMultiplicity

/-!
# The actual finite Selberg weights on labelled positive prime families

SOURCE ONLY / UNCOMPILED. The finite weights, their level, their allowed
prime product and their reciprocal-totient density are fixed before the
labelled family is introduced. The family may have repeated products.
The exact optimized main term is evaluated, and the actual primitive AP
remainder and coprime correction are retained on the same coefficient.

This is a finite joining theorem. It supplies neither the original currentK
density nor the manuscript's strong prime-product distribution estimate.
In particular ordinary BV at level one half is not used as such a supplier.
-/

namespace ImbalancedChen

noncomputable section
open scoped BigOperators

/-- A normalized upper-Moebius coefficient gives a pointwise physical
majorant, including at zero. A singleton instance of the genuine sieve
theorem avoids any injectivity assumption on a later product family. -/
private theorem primeFamily_upperMoebius_majorant
    (s : BoundingSieve) (rho : ℕ → ℝ)
    (hrho : BoundingSieve.IsUpperMoebius rho) (n : ℕ) :
    (if Nat.Coprime n s.prodPrimes then (1 : ℝ) else 0) ≤
      physicalDivisorSum s.prodPrimes.divisors rho n := by
  classical
  let t : BoundingSieve := { s with
    support := {n}
    weights := fun _ => 1
    weights_nonneg := fun _ => zero_le_one }
  have h := BoundingSieve.siftedSum_le_sum_of_upperMoebius
    (s := t) rho hrho
  simpa only [BoundingSieve.siftedSum, BoundingSieve.multSum, t,
    Finset.sum_singleton, mul_ite, mul_one, mul_zero,
    physicalDivisorSum, Nat.coprime_comm] using h

/-- The same actual finite coefficient is used in the pointwise majorant,
the main term and both arithmetic errors. No family data enter its choice. -/
def primeFamilyFiniteSelbergRho
    (num den N : ℕ) (T : ℝ) (z L : ℕ) (hN : Even N) : ℕ → ℝ :=
  BoundingSieve.lambdaSquared
    (finiteSelbergWeight (halfProductBoundingSieve num den N T z hN) L)

/-- The literal finite normalizer, with its strict prime cap and inclusive
coefficient level. This is the common reciprocal-phi Euler system. -/
def primeFamilyFiniteSelbergG (N z L : ℕ) : ℝ :=
  ∑ d ∈ (sieveProduct N z).divisors with d ≤ L,
    ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 2)

theorem primeFamilyFiniteSelbergRho_majorant
    (num den N : ℕ) (T : ℝ) (z L : ℕ) (hN : Even N) (hL : 1 ≤ L)
    (n : ℕ) :
    (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
      physicalDivisorSum (sieveProduct N z).divisors
        (primeFamilyFiniteSelbergRho num den N T z L hN) n :=
  primeFamily_upperMoebius_majorant
    (halfProductBoundingSieve num den N T z hN) _
    (upperMoebius_finiteSelbergWeight _ hL) n

/-- The density is proved from the evaluated finite Selberg main form,
not supplied as an upper-density assumption. -/
theorem primeFamilyFiniteSelbergRho_density
    (num den N : ℕ) (T : ℝ) (z L : ℕ) (hN : Even N) (hL : 1 ≤ L) :
    physicalDensitySum (sieveProduct N z).divisors
        (primeFamilyFiniteSelbergRho num den N T z L hN) =
      1 / primeFamilyFiniteSelbergG N z L := by
  have h := mainSum_lambdaSquared_finiteSelbergWeight
    (halfProductBoundingSieve num den N T z hN) hL
  rw [halfProductBoundingSieve_mainSum, halfProduct_finiteSelbergNormalizer] at h
  exact h

/-- Only moduli at most L squared can occur, proved from the actual
finite weight formula. The AP remainder itself need not vanish above L squared. -/
theorem primeFamilyFiniteSelbergRho_eq_zero_of_level
    (num den N : ℕ) (T : ℝ) (z L : ℕ) (hN : Even N)
    (d : ℕ) (hd : L * L < d) :
    primeFamilyFiniteSelbergRho num den N T z L hN d = 0 :=
  lambdaSquared_eq_zero_of_level _ L
    (fun n hn => finiteSelbergWeight_eq_zero_of_level _ L n hn) d hd

private theorem primeFamily_finiteSelberg_sum_truncated
    (num den N : ℕ) (T : ℝ) (z L : ℕ) (hN : Even N) (F : ℕ → ℝ) :
    (∑ d ∈ (sieveProduct N z).divisors,
      primeFamilyFiniteSelbergRho num den N T z L hN d * F d) =
      ∑ d ∈ (sieveProduct N z).divisors with d ≤ L * L,
        primeFamilyFiniteSelbergRho num den N T z L hN d * F d := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hlevel : d ≤ L * L
  · rw [if_pos hlevel]
  · rw [if_neg hlevel,
      primeFamilyFiniteSelbergRho_eq_zero_of_level num den N T z L hN d
        (Nat.lt_of_not_ge hlevel), zero_mul]

/-- Finite positive-family upper bound at the actual optimized weights.
The full source mass is divided by the evaluated normalizer; the two
remaining sums are the exact primitive AP error and exact coprime-main
correction. Both are signed until after their full modulus sums.
The parameters N,z,L and hence the coefficient precede the family.
No upper bound for the desired prime count is a hypothesis. -/
theorem primeFamily_le_finiteSelberg_main_add_primitive_remainders
    (num den N : ℕ) (T : ℝ) (z L : ℕ) (hN : Even N) (hL : 1 ≤ L)
    {α : Type*} (S : Finset α) (f : α → ℕ) (W : α → ℝ)
    (hW : ∀ t ∈ S, 0 ≤ W t) (hSN : ∀ t ∈ S, f t ≤ N) :
    p5z_labelledPrimeMass S f W N ≤
      p5z_labelledMass S W / primeFamilyFiniteSelbergG N z L +
      (∑ d ∈ (sieveProduct N z).divisors with d ≤ L * L,
        primeFamilyFiniteSelbergRho num den N T z L hN d *
          ((p5z_labelledCoprimeMass S f W d - p5z_labelledMass S W) /
            (Nat.totient d : ℝ))) +
      (∑ d ∈ (sieveProduct N z).divisors with d ≤ L * L,
        primeFamilyFiniteSelbergRho num den N T z L hN d *
          (p5z_labelledCongruenceMass S f W N d -
            p5z_labelledCoprimeMass S f W d / (Nat.totient d : ℝ))) +
      p5z_labelledSmallPrimeMass S f W N z := by
  have h := p5z_labelledPrimeMass_le_main_add_errors S f W N z
    (sieveProduct N z).divisors
    (primeFamilyFiniteSelbergRho num den N T z L hN) hW hSN
    (primeFamilyFiniteSelbergRho_majorant num den N T z L hN hL)
  rw [primeFamilyFiniteSelbergRho_density num den N T z L hN hL] at h
  unfold p5z_labelledCoprimeCorrection p5z_labelledDistributionError at h
  rw [primeFamily_finiteSelberg_sum_truncated,
    primeFamily_finiteSelberg_sum_truncated] at h
  simpa only [div_eq_mul_inv, one_mul] using h

/-- At bounded prime rank the remaining small-partner term has an explicit
finite payment, retaining all tuple labels and all repeated products.
The coefficients are fixed before S,W; there is no family-dependent
choice of sieve level or a final U-star assumption. -/
theorem markedPrimeFamily_le_finiteSelberg_main_add_primitive_remainders
    (num den N : ℕ) (T : ℝ) (z L : ℕ) (hN : Even N) (hL : 1 ≤ L)
    (rank : ℕ) (S : Finset (Fin rank → Fin (N + 1)))
    (hS : S ⊆ Part3.labelledPrimeTuples rank N)
    (W : (Fin rank → Fin (N + 1)) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hW : ∀ t ∈ S, 0 ≤ W t ∧ W t ≤ B)
    (hcap : ∀ t ∈ S, Part3.labelledProduct t ≤ N) :
    p5z_labelledPrimeMass S Part3.labelledProduct W N ≤
      p5z_labelledMass S W / primeFamilyFiniteSelbergG N z L +
      (∑ d ∈ (sieveProduct N z).divisors with d ≤ L * L,
        primeFamilyFiniteSelbergRho num den N T z L hN d *
          ((p5z_labelledCoprimeMass S Part3.labelledProduct W d -
            p5z_labelledMass S W) / (Nat.totient d : ℝ))) +
      (∑ d ∈ (sieveProduct N z).divisors with d ≤ L * L,
        primeFamilyFiniteSelbergRho num den N T z L hN d *
          (p5z_labelledCongruenceMass S Part3.labelledProduct W N d -
            p5z_labelledCoprimeMass S Part3.labelledProduct W d /
              (Nat.totient d : ℝ))) +
      B * (rank ^ rank : ℕ) * (z : ℝ) := by
  exact (primeFamily_le_finiteSelberg_main_add_primitive_remainders
    num den N T z L hN hL S Part3.labelledProduct W
    (fun t ht => (hW t ht).1) hcap).trans
      (add_le_add_left
        (p5z_markedSmallPrimeMass_le S hS W B hB
          (fun t ht => (hW t ht).2) hcap z) _)

end
end ImbalancedChen
