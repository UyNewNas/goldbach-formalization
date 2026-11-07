import ImbalancedChen.FixedRoughCoefficients
import ImbalancedChen.SmallRoughMainTerm
import MathlibNt.SieveTheory.LiLiuFouvryG9ProgressionDensityDimension
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Absolute reciprocal-totient mass of the actual retained rough support

Every fixed retained modulus is a squarefree divisor of the product of the
actual rough-prime carrier. Its coefficient has absolute value at most one.
The full divisor sum is evaluated by an exact multiplicative Euler product,
without estimating a signed sum by its absolute value.

For even targets, the proved Goldbach inverse-interval estimate supplies
one dimension constant for every target, finite cap, and retention policy.
The final bound holds for `1 < w ≤ z`, including the empty interval `w = z`
and the interval below two. No completeness assumption on `cap` is needed:
the estimate remains true for the actual truncated prime carrier. It does
not assert the sharp signed density of the manuscript's causal policy.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open ArithmeticFunction
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

/-- The finite Euler expansion on an actual prime product, with every
divisor coprime to the target. There is no analytic hypothesis here. -/
theorem reciprocalTotient_sum_divisors_primeProduct
    (N : ℕ) (P : Finset ℕ) (hprime : ∀ p ∈ P, Nat.Prime p)
    (hcop : ∀ p ∈ P, Nat.Coprime p N) :
    (∑ d ∈ (P.prod id).divisors, 1 / (Nat.totient d : ℝ)) =
      ∏ p ∈ P, (1 + 1 / ((p : ℝ) - 1)) := by
  classical
  have hsf : Squarefree (P.prod id) := primeProduct_squarefree P hprime
  have hMcop : (P.prod id).Coprime N := by
    rw [Nat.coprime_prod_left_iff]
    exact hcop
  have hg : (progressionDensity N).IsMultiplicative := by
    rw [← primeDensity_progressionOmega]
    exact primeDensity_isMultiplicative (progressionOmega_isMultiplicative N)
  have hζ : ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
      ArithmeticFunction ℝ).IsMultiplicative := isMultiplicative_zeta.natCast
  have heuler := hζ.prodPrimeFactors_add_of_squarefree hg hsf
  rw [prodPrimeFactors_apply hsf.ne_zero, coe_zeta_mul_apply] at heuler
  have hfac : (P.prod id).primeFactors = P := by
    simpa only [id_eq] using Nat.primeFactors_prod hprime
  calc
    (∑ d ∈ (P.prod id).divisors, 1 / (Nat.totient d : ℝ)) =
        ∑ d ∈ (P.prod id).divisors, progressionDensity N d := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdN := hMcop.of_dvd_left (Nat.mem_divisors.mp hd).1
      change 1 / (Nat.totient d : ℝ) =
        if d.Coprime N then (Nat.totient d : ℝ)⁻¹ else 0
      rw [if_pos hdN, one_div]
    _ = ∏ p ∈ (P.prod id).primeFactors,
        (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) +
          progressionDensity N) p := heuler.symm
    _ = ∏ p ∈ P, (1 + 1 / ((p : ℝ) - 1)) := by
      rw [hfac]
      apply Finset.prod_congr rfl
      intro p hp
      rw [ArithmeticFunction.add_apply, ArithmeticFunction.natCoe_apply,
        zeta_apply_ne (hprime p hp).ne_zero,
        progressionDensity_prime N (hprime p hp), if_pos (hcop p hp)]
      norm_num

/-- Every retained modulus divides the product of the actual rough primes.
This is proved from its squarefree prime-factor support. -/
theorem fixedRoughSupport_subset_primeProduct_divisors
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :
    fixedRoughSupport retainOdd N cap w z ⊆
      ((roughPrimeFinset N cap w z).prod id).divisors := by
  classical
  intro d hd
  have hprime : ∀ p ∈ roughPrimeFinset N cap w z, Nat.Prime p :=
    fun _ hp => (mem_roughPrimeFinset.mp hp).2.1
  have hM := (primeProduct_squarefree (roughPrimeFinset N cap w z) hprime).ne_zero
  have hsub : d.primeFactors ⊆ roughPrimeFinset N cap w z := by
    intro p hp
    have h := fixedRoughSupport_primeFactors_mem retainOdd N cap w z hd hp
    simpa only [roughPrimeUniverse, Finset.mem_sort] using h
  have hdiv : d ∣ (roughPrimeFinset N cap w z).prod id := by
    rw [← Nat.prod_primeFactors_of_squarefree
      (fixedRoughSupport_squarefree retainOdd N cap w z hd)]
    exact Finset.prod_dvd_prod_of_subset _ _ id hsub
  exact Nat.mem_divisors.mpr ⟨hdiv, hM⟩

/-- The actual absolute retained mass is at most the exact full finite
Euler product. The policy is arbitrary and is not reselected for a divisor. -/
theorem fixedRoughAbsoluteDensity_le_eulerProduct
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :
    reciprocalTotientDensity (fixedRoughSupport retainOdd N cap w z)
        (fun d => |fixedRoughCoefficient retainOdd N cap w z d|) ≤
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
    (∑ d ∈ fixedRoughSupport retainOdd N cap w z,
        |fixedRoughCoefficient retainOdd N cap w z d| / (Nat.totient d : ℝ)) ≤
        ∑ d ∈ fixedRoughSupport retainOdd N cap w z, 1 / (Nat.totient d : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact div_le_div_of_nonneg_right
        (fixedRoughCoefficient_abs_le_one retainOdd N cap w z d) (Nat.cast_nonneg _)
    _ ≤ ∑ d ∈ ((roughPrimeFinset N cap w z).prod id).divisors,
        1 / (Nat.totient d : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (fixedRoughSupport_subset_primeProduct_divisors retainOdd N cap w z)
      intro d hd hnot
      exact one_div_nonneg.mpr (Nat.cast_nonneg _)
    _ = _ := reciprocalTotient_sum_divisors_primeProduct N _ hprime hcop

theorem roughPrimeFinset_odd_of_even {N cap : ℕ} {w z : ℝ}
    (hN : Even N) {p : ℕ} (hp : p ∈ roughPrimeFinset N cap w z) :
    Nat.Prime p ∧ 2 < p := by
  obtain ⟨_, hprime, hnot, _, _⟩ := mem_roughPrimeFinset.mp hp
  have h2N : 2 ∣ N := by
    obtain ⟨k, hk⟩ := hN
    exact ⟨k, by omega⟩
  have hne : p ≠ 2 := by
    intro heq
    subst p
    exact hnot h2N
  exact ⟨hprime, by have := hprime.two_le; omega⟩

/-- The plus Euler factors are bounded by inverse Goldbach factors. -/
theorem roughPrime_eulerProduct_le_inverseProduct
    (N cap : ℕ) (w z : ℝ) (hN : Even N) :
    (∏ p ∈ roughPrimeFinset N cap w z, (1 + 1 / ((p : ℝ) - 1))) ≤
      ∏ p ∈ roughPrimeFinset N cap w z, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
  classical
  apply Finset.prod_le_prod
  · intro p hp
    have hp2 : (2 : ℝ) < p := by
      exact_mod_cast (roughPrimeFinset_odd_of_even hN hp).2
    exact add_nonneg zero_le_one (div_nonneg zero_le_one (by linarith))
  · intro p hp
    have hp2 : (2 : ℝ) < p := by
      exact_mod_cast (roughPrimeFinset_odd_of_even hN hp).2
    have hx : (1 : ℝ) / ((p : ℝ) - 1) < 1 :=
      (div_lt_one (by linarith)).mpr (by linarith)
    rw [← one_div]
    apply (le_div_iff₀ (sub_pos.mpr hx)).mpr
    nlinarith [sq_nonneg (1 / ((p : ℝ) - 1))]

/-- One proved analytic constant bounds the absolute mass of every actual
fixed retained support. The target, cap and policy may vary freely. The
lower endpoint is inclusive and the upper endpoint is strict; `w = z` and
`1 < w < 2` are included. A truncated enumeration only decreases the bound. -/
theorem exists_fixedRoughAbsoluteDensity_le_logRatio :
    ∃ K : ℝ, 1 < K ∧ ∀ (retainOdd : List ℕ → Bool) (N cap : ℕ),
      Even N → ∀ w z : ℝ, 1 < w → w ≤ z →
        reciprocalTotientDensity (fixedRoughSupport retainOdd N cap w z)
            (fun d => |fixedRoughCoefficient retainOdd N cap w z d|) ≤
          Real.log z / Real.log w * (1 + K / Real.log w) := by
  classical
  obtain ⟨K, hK, hinterval⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K, hK, ?_⟩
  intro retainOdd N cap hN w z hw hwz
  let P := roughPrimeFinset N cap w z
  have hP : ∀ p ∈ P, Nat.Prime p ∧ 2 < p :=
    fun _ hp => roughPrimeFinset_odd_of_even hN hp
  have hfinite := fixedRoughAbsoluteDensity_le_eulerProduct retainOdd N cap w z
  have hinverse := roughPrime_eulerProduct_le_inverseProduct N cap w z hN
  have hlogw : 0 < Real.log w := Real.log_pos hw
  have hK0 : 0 ≤ K := by linarith
  by_cases hw2 : 2 ≤ w
  · exact (hfinite.trans hinverse).trans
      (hinterval P hP w z hw2 hwz (fun p hp => (mem_roughPrimeFinset.mp hp).2.2.2))
  · have hw2le : w ≤ 2 := (lt_of_not_ge hw2).le
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlogw2 : Real.log w ≤ Real.log (2 : ℝ) :=
      Real.log_le_log (by linarith) hw2le
    by_cases hz2 : 2 ≤ z
    · have hpi : ∀ p ∈ P, (2 : ℝ) ≤ p ∧ (p : ℝ) < z := by
        intro p hp
        exact ⟨by exact_mod_cast (hP p hp).1.two_le,
          (mem_roughPrimeFinset.mp hp).2.2.2.2⟩
      have hbound := hinterval P hP 2 z (by norm_num) hz2 hpi
      have hlogz : 0 ≤ Real.log z := Real.log_nonneg (by linarith)
      have hratio : Real.log z / Real.log (2 : ℝ) ≤ Real.log z / Real.log w :=
        div_le_div_of_nonneg_left hlogz hlogw hlogw2
      have hfactor : K / Real.log (2 : ℝ) ≤ K / Real.log w :=
        div_le_div_of_nonneg_left hK0 hlogw hlogw2
      exact ((hfinite.trans hinverse).trans hbound).trans
        (mul_le_mul hratio (add_le_add le_rfl hfactor)
          (by positivity) (div_nonneg hlogz hlogw.le))
    · have hempty : P = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).1.two_le
        have hpz := (mem_roughPrimeFinset.mp hp).2.2.2.2
        linarith
      have hmass : reciprocalTotientDensity (fixedRoughSupport retainOdd N cap w z)
          (fun d => |fixedRoughCoefficient retainOdd N cap w z d|) ≤ 1 := by
        change _ ≤ ∏ p ∈ P, (1 + 1 / ((p : ℝ) - 1)) at hfinite
        simpa only [hempty, Finset.prod_empty] using hfinite
      have hlogwz : Real.log w ≤ Real.log z :=
        Real.log_le_log (by linarith) hwz
      have hratio : 1 ≤ Real.log z / Real.log w :=
        (le_div_iff₀ hlogw).mpr (by simpa using hlogwz)
      have hfactor : 1 ≤ 1 + K / Real.log w :=
        le_add_of_nonneg_right (div_nonneg hK0 hlogw.le)
      have hproduct := mul_le_mul hratio hfactor (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith : 0 ≤ Real.log z / Real.log w)
      exact hmass.trans (by simpa only [one_mul] using hproduct)

end

end ImbalancedChen
