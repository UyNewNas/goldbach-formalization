import ImbalancedChen.FixedEvenRoughCoefficients
import ImbalancedChen.RoughPowerParameters

/-!
# Absolute mass of the actual even-first-exit rough coefficient

The signed lower density is not an absolute mass. This file bounds the
absolute reciprocal-totient mass by the full prime Euler product, using
squarefree support and the actual unit coefficient bound. The analytic
constant is independent of the even retention policy and of the target.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

theorem fixedEvenRoughSupport_subset_primeProduct_divisors
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :
    fixedEvenRoughSupport retainEven N cap w z ⊆
      ((roughPrimeFinset N cap w z).prod id).divisors := by
  classical
  intro d hd
  have hprime : ∀ p ∈ roughPrimeFinset N cap w z, Nat.Prime p :=
    fun _ hp => (mem_roughPrimeFinset.mp hp).2.1
  have hM := (primeProduct_squarefree (roughPrimeFinset N cap w z) hprime).ne_zero
  have hsub : d.primeFactors ⊆ roughPrimeFinset N cap w z := by
    intro p hp
    have h := fixedEvenRoughSupport_primeFactors_mem retainEven N cap w z hd hp
    simpa only [roughPrimeUniverse, Finset.mem_sort] using h
  have hdiv : d ∣ (roughPrimeFinset N cap w z).prod id := by
    rw [← Nat.prod_primeFactors_of_squarefree
      (fixedEvenRoughSupport_squarefree retainEven N cap w z hd)]
    exact Finset.prod_dvd_prod_of_subset _ _ id hsub
  exact Nat.mem_divisors.mpr ⟨hdiv, hM⟩

theorem fixedEvenRoughAbsoluteDensity_le_eulerProduct
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :
    reciprocalTotientDensity (fixedEvenRoughSupport retainEven N cap w z)
        (fun d => |fixedEvenRoughCoefficient retainEven N cap w z d|) ≤
      ∏ p ∈ roughPrimeFinset N cap w z, (1 + 1 / ((p : ℝ) - 1)) := by
  classical
  have hprime : ∀ p ∈ roughPrimeFinset N cap w z, Nat.Prime p :=
    fun _ hp => (mem_roughPrimeFinset.mp hp).2.1
  have hcop : ∀ p ∈ roughPrimeFinset N cap w z, Nat.Coprime p N := by
    intro p hp
    have h := mem_roughPrimeFinset.mp hp
    exact h.2.1.coprime_iff_not_dvd.mpr h.2.2.1
  unfold reciprocalTotientDensity
  calc
    (∑ d ∈ fixedEvenRoughSupport retainEven N cap w z,
        |fixedEvenRoughCoefficient retainEven N cap w z d| / (Nat.totient d : ℝ)) ≤
        ∑ d ∈ fixedEvenRoughSupport retainEven N cap w z, 1 / (Nat.totient d : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      exact div_le_div_of_nonneg_right
        (fixedEvenRoughCoefficient_abs_le_one retainEven N cap w z d) (Nat.cast_nonneg _)
    _ ≤ ∑ d ∈ ((roughPrimeFinset N cap w z).prod id).divisors,
        1 / (Nat.totient d : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (fixedEvenRoughSupport_subset_primeProduct_divisors retainEven N cap w z)
      intro d _ _
      exact one_div_nonneg.mpr (Nat.cast_nonneg _)
    _ = _ := reciprocalTotient_sum_divisors_primeProduct N _ hprime hcop

/-- The actual lower support, including a truncated cap, has a uniform
absolute-mass envelope once the presieve cutoff is at least two. -/
theorem exists_fixedEvenRoughAbsoluteDensity_le_logRatio :
    ∃ Krough : ℝ, 1 < Krough ∧
      ∀ (retainEven : List ℕ → Bool) (N cap : ℕ), Even N →
        ∀ w z : ℝ, 2 ≤ w → w ≤ z →
          reciprocalTotientDensity (fixedEvenRoughSupport retainEven N cap w z)
              (fun d => |fixedEvenRoughCoefficient retainEven N cap w z d|) ≤
            Real.log z / Real.log w * (1 + Krough / Real.log w) := by
  obtain ⟨Krough, hKrough, hinterval⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨Krough, hKrough, ?_⟩
  intro retainEven N cap hN w z hw hwz
  exact ((fixedEvenRoughAbsoluteDensity_le_eulerProduct retainEven N cap w z).trans
    (roughPrime_eulerProduct_le_inverseProduct N cap w z hN)).trans
      (hinterval (roughPrimeFinset N cap w z)
        (fun _ hp => roughPrimeFinset_odd_of_even hN hp)
        w z hw hwz (fun _ hp => (mem_roughPrimeFinset.mp hp).2.2.2))

theorem exists_fixedEvenRoughAbsoluteDensity_le_powerParameters :
    ∃ Krough : ℝ, 1 < Krough ∧
      ∀ (retainEven : List ℕ → Bool) (N cap : ℕ), Even N →
        ∀ D epsilon r : ℝ, 1 < D → 0 < epsilon → epsilon ^ 2 ≤ r →
          2 ≤ D ^ (epsilon ^ 2) →
          reciprocalTotientDensity
              (fixedEvenRoughSupport retainEven N cap (D ^ (epsilon ^ 2)) (D ^ r))
              (fun d => |fixedEvenRoughCoefficient retainEven N cap
                (D ^ (epsilon ^ 2)) (D ^ r) d|) ≤
            (r / epsilon ^ 2) * (1 + Krough / (epsilon ^ 2 * Real.log D)) := by
  obtain ⟨Krough, hKrough, hbound⟩ := exists_fixedEvenRoughAbsoluteDensity_le_logRatio
  refine ⟨Krough, hKrough, ?_⟩
  intro retainEven N cap hN D epsilon r hD hepsilon hepsilonr hw
  have hcut := roughPower_cutoffs hD hepsilon hepsilonr
  have h := hbound retainEven N cap hN (D ^ (epsilon ^ 2)) (D ^ r) hw hcut.2
  have hDpos : 0 < D := lt_trans zero_lt_one hD
  rw [roughPower_log_ratio hDpos (ne_of_gt (Real.log_pos hD)) (ne_of_gt hepsilon),
    Real.log_rpow hDpos] at h
  exact h

end

end ImbalancedChen
