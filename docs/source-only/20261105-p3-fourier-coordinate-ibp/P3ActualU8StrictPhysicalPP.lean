import ImbalancedChen.P3ActualU8StrictPrimePP
import ImbalancedChen.CurrentChenUpsilon8SharpKPhysicalPP
import Mathlib.Tactic

/-!
P3.6: the literal STRICT p₁<p₂<q U8 source is an actual
rank-three labelled Part3 prime-product family, not just a finite
source-level discrepancy.

This is a separate weight from the existing inclusive physicalWeight:
the repeated terminal-prime labels must not leak back into the
analytic PP term after their direct power-saving payment.

The proof reuses the ORIGINAL coordinate encoder, inverse and prime
cap. It does not replace the complete product by the pair product,
collapse equal-product labels, change a physical modulus or rho,
or assume an arithmetic distribution estimate.
SOURCE_ONLY / Lean elaboration and kernel validation pending.
-/

namespace ImbalancedChen.P3ActualU8StrictPhysicalPP

noncomputable section
open scoped BigOperators
open Filter Topology
open Classical
open ImbalancedChen.P5U8SharpKSource
open ImbalancedChen.P3ActualU8StrictPrimePP

/-- The actual strict terminal-prime source as a zero-one coefficient
on the original Part3 labelled prime tuple carrier. -/
def strictPhysicalWeight (N : ℕ) (u : Fin 3 → Fin (N + 1)) : ℝ :=
  if physicalInverse u ∈ strictTriples N then 1 else 0

theorem strictPhysicalWeight_abs_le_one (N : ℕ)
    (u : Fin 3 → Fin (N + 1)) :
    |strictPhysicalWeight N u| ≤ 1 := by
  unfold strictPhysicalWeight
  split_ifs <;> norm_num

/-- Any nonzero strict coefficient retains the genuine original
prime, target, coprimality and full-product gates, and has p₂<q
rather than the inclusive p₂≤q gate. -/
theorem strictPhysicalWeight_support_data {N : ℕ}
    {u : Fin 3 → Fin (N + 1)}
    (hu : strictPhysicalWeight N u ≠ 0) :
    (u 0).val < (u 1).val ∧ (u 1).val < (u 2).val ∧
      Part3.labelledProduct u < N ∧
      Nat.Coprime (Part3.labelledProduct u) N ∧
      Nat.Coprime (N - Part3.labelledProduct u) N := by
  have ht : physicalInverse u ∈ strictTriples N := by
    by_contra hnot
    exact hu (by simp [strictPhysicalWeight, hnot])
  have hraw : physicalInverse u ∈ arithmeticTriples N :=
    (Finset.mem_filter.mp ht).1
  have hweight : physicalWeight N u ≠ 0 := by
    simp [physicalWeight, hraw]
  have hsource := physicalWeight_support_data hweight
  have hstrict : (u 1).val < (u 2).val := by
    simpa only [physicalInverse] using (Finset.mem_filter.mp ht).2
  exact ⟨hsource.1, hstrict, hsource.2.2.1,
    hsource.2.2.2.1, hsource.2.2.2.2⟩

/-- The unchanged original 417/5000 lower-power cutoff applies to
each of the three strict labelled coordinates as well. -/
theorem strictPhysicalWeight_lower_power {N : ℕ}
    {u : Fin 3 → Fin (N + 1)}
    (hu : strictPhysicalWeight N u ≠ 0) :
    ∀ i : Fin 3, (N : ℝ) ^ (417 / 5000 : ℝ) ≤ ((u i).val : ℝ) := by
  have ht : physicalInverse u ∈ strictTriples N := by
    by_contra hnot
    exact hu (by simp [strictPhysicalWeight, hnot])
  have hraw : physicalInverse u ∈ arithmeticTriples N :=
    (Finset.mem_filter.mp ht).1
  have hweight : physicalWeight N u ≠ 0 := by
    simp [physicalWeight, hraw]
  exact physicalWeight_lower_power hweight

/-- Strict label-preserving reindexing through the native Part3
three-prime coordinate carrier. In particular this is NOT obtained
by filtering a product-value weight: the predicate p₂<q is evaluated
on the original labelled tuple before forming its full product. -/
theorem strictPhysicalWeight_sum (N : ℕ) (F : ℕ → ℝ) :
    (∑ t ∈ strictTriples N, F (product t)) =
      ∑ u ∈ Part3.labelledPrimeTuples 3 N,
        strictPhysicalWeight N u * F (Part3.labelledProduct u) := by
  let encode : (t : Triple) → t ∈ strictTriples N →
      (Fin 3 → Fin (N + 1)) :=
    fun t ht i =>
      ⟨natCoord t i,
       Nat.lt_succ_of_le
         (natCoord_prime_cap (Finset.mem_filter.mp ht).1 i).2⟩
  have hencode_inverse (t : Triple) (ht : t ∈ strictTriples N) :
      physicalInverse (encode t ht) = t := by
    apply natCoord_injective
    funext i
    exact natCoord_physicalInverse (encode t ht) i
  let T := (Part3.labelledPrimeTuples 3 N).filter
    (fun u => physicalInverse u ∈ strictTriples N)
  have hbij : (∑ t ∈ strictTriples N, F (product t)) =
      ∑ u ∈ T, F (Part3.labelledProduct u) := by
    refine Finset.sum_bij encode ?_ ?_ ?_ ?_
    · intro t ht
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,
           fun i => (natCoord_prime_cap (Finset.mem_filter.mp ht).1 i).1⟩
      · rw [hencode_inverse t ht]
        exact ht
    · intro t ht s hs heq
      apply natCoord_injective
      funext i
      exact congrArg (fun v : Fin 3 → Fin (N + 1) => (v i).val) heq
    · intro u hu
      have hi := (Finset.mem_filter.mp hu).2
      refine ⟨physicalInverse u, hi, ?_⟩
      funext i
      apply Fin.ext
      exact natCoord_physicalInverse u i
    · intro t ht
      have hp : Part3.labelledProduct (encode t ht) = product t :=
        natCoord_product t
      exact congrArg F hp.symm
  calc
    _ = ∑ u ∈ T, F (Part3.labelledProduct u) := hbij
    _ = _ := by
      dsimp only [T]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u _
      by_cases ht : physicalInverse u ∈ strictTriples N <;>
        simp only [strictPhysicalWeight, ht,
          if_true, if_false, one_mul, zero_mul]

/-- The strict ORIGINAL triple PP discrepancy has exactly the
rank-three Part3 physical meaning, with one signed Q/rho in the
congruence term and the exact primitive coprime mean. -/
theorem strict_distribution_eq_physicalPP (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (strictTriples N) product
        (fun _ => (1 : ℝ)) N Q rho =
      Part3.primeProductSignedError 3 N N Q rho
        (strictPhysicalWeight N) := by
  have hcong : ∀ ell,
      p5z_labelledCongruenceMass (strictTriples N) product
          (fun _ => (1 : ℝ)) N ell =
        p5z_labelledCongruenceMass (Part3.labelledPrimeTuples 3 N)
          Part3.labelledProduct (strictPhysicalWeight N) N ell := by
    intro ell
    simpa only [p5z_labelledCongruenceMass,
      mul_ite, mul_one, mul_zero] using
      strictPhysicalWeight_sum N
        (fun m => if Nat.ModEq ell m N then (1 : ℝ) else 0)
  have hcop : ∀ ell,
      p5z_labelledCoprimeMass (strictTriples N) product
          (fun _ => (1 : ℝ)) ell =
        p5z_labelledCoprimeMass (Part3.labelledPrimeTuples 3 N)
          Part3.labelledProduct (strictPhysicalWeight N) ell := by
    intro ell
    simpa only [p5z_labelledCoprimeMass,
      mul_ite, mul_one, mul_zero] using
      strictPhysicalWeight_sum N
        (fun m => if Nat.Coprime m ell then (1 : ℝ) else 0)
  calc
    _ = p5z_labelledDistributionError (Part3.labelledPrimeTuples 3 N)
        Part3.labelledProduct (strictPhysicalWeight N) N Q rho := by
      unfold p5z_labelledDistributionError
      simp_rw [hcong, hcop]
    _ = _ :=
      p5z_labelledDistributionError_eq_primeProductSignedError
        3 N N Q rho (strictPhysicalWeight N)

/-- The actual U8 upper counting reduction now has a genuine strict
Part3 rank-three PP weight rather than only a finite labelled-source
error expression. No smoothing admissibility or PP saving is claimed. -/
theorem actual_u8_upper_via_strict_rank_three_PP
    (N z : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hz : (z : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ))
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    currentChenUpsilon8 N ≤
      p5z_labelledMass (strictTriples N) (fun _ => (1 : ℝ)) *
        physicalDensitySum Q rho +
      p5z_labelledCoprimeCorrection (strictTriples N) product
        (fun _ => (1 : ℝ)) Q rho +
      Part3.primeProductSignedError 3 N N Q rho
        (strictPhysicalWeight N) +
      ((currentChenUpsilon8SmallGoldbachPrimeTriples N).card : ℝ) +
      ((diagonalTriples N).card : ℝ) +
      ((currentChenUpsilon8UnitFibres N).card : ℝ) := by
  rw [← strict_distribution_eq_physicalPP N Q rho]
  exact actual_u8_upper_via_strict_prime_PP N z Q rho hz hmajor

/-- Source losses are paid with one N threshold before Q and rho;
the remaining analytic obligation is precisely the native strict
rank-three physical PP error, not the inclusive terminal source. -/
theorem eventually_actual_u8_upper_via_strict_rank_three_PP
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (z : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ),
        (z : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ) →
        (∀ n : ℕ,
          (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
            physicalDivisorSum Q rho n) →
        currentChenUpsilon8 N ≤
          p5z_labelledMass (strictTriples N) (fun _ => (1 : ℝ)) *
            physicalDensitySum Q rho +
          p5z_labelledCoprimeCorrection (strictTriples N) product
            (fun _ => (1 : ℝ)) Q rho +
          Part3.primeProductSignedError 3 N N Q rho
            (strictPhysicalWeight N) +
          ε * singularNormalization N := by
  filter_upwards [
    eventually_actual_u8_upper_via_strict_prime_PP ε hε
  ] with N hN
  intro z Q rho hz hmajor
  rw [← strict_distribution_eq_physicalPP N Q rho]
  exact hN z Q rho hz hmajor

end
end ImbalancedChen.P3ActualU8StrictPhysicalPP
