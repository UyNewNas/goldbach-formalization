import ImbalancedChen.Part3RoughThinEulerFactors
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The finite weighted-prime input for the actual thin-left Euler product.
The only prime-distribution input is the proved primary mathlib theorem
`Chebyshev.theta_le_log4_mul_x`. Abel summation is applied to that theta
function, not to the all-integer harmonic sum. The carrier is exactly
`range (floor z + 1)` filtered by primality, including a prime at z.
No zero-free, SW, prime-number-theorem, or desired prime-sum bound is assumed.
-/

namespace ImbalancedChen.Part3.RoughWeightedPrimeMass20261026b
noncomputable section
open Classical Finset Real MeasureTheory
open RoughSlotCharacterLift20261026b RoughThinEulerFactors20261026b
open scoped BigOperators

private def thetaCoeff (n : ℕ) : ℝ := if n.Prime then log n else 0

private theorem thetaCoeff_sum (t : ℝ) :
    (∑ n ∈ Finset.Icc 0 (Nat.floor t), thetaCoeff n) = Chebyshev.theta t := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rfl

private theorem inverseSquare_continuous (z : ℝ) :
    ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc 1 z) := by
  exact (continuousOn_id.pow 2).inv₀ (fun t ht => pow_ne_zero 2 (by linarith [ht.1]))

/-- Exact finite Abel identity for Joint's literal inclusive prime carrier. -/
theorem logPrimeMass_eq_theta_abel {z : ℝ} (hz : 1 ≤ z) :
    logPrimeMass z = Chebyshev.theta z / z +
      ∫ t in 1..z, Chebyshev.theta t / t ^ 2 := by
  have hsum : logPrimeMass z =
      ∑ n ∈ Finset.Icc 0 (Nat.floor z), (n : ℝ)⁻¹ * thetaCoeff n := by
    unfold logPrimeMass smallPrimes
    rw [Nat.range_succ_eq_Icc_zero, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hp : n.Prime <;> simp [thetaCoeff, hp, div_eq_mul_inv, mul_comm]
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) z,
      DifferentiableAt ℝ (fun u : ℝ => u⁻¹) t := by
    intro t ht
    exact (hasDerivAt_inv (by linarith [ht.1])).differentiableAt
  have hderiv : IntegrableOn (deriv (fun u : ℝ => u⁻¹)) (Set.Icc 1 z) := by
    simpa only [deriv_inv] using
      (inverseSquare_continuous z).neg.integrableOn_Icc
  have hAbel := sum_mul_eq_sub_integral_mul₀ thetaCoeff
    (by simp [thetaCoeff]) z hdiff hderiv
  rw [← hsum, thetaCoeff_sum, ← intervalIntegral.integral_of_le hz] at hAbel
  simp_rw [thetaCoeff_sum, deriv_inv] at hAbel
  rw [hAbel, sub_eq_add_neg, ← intervalIntegral.integral_neg]
  congr 1
  · ring
  · apply intervalIntegral.integral_congr
    intro t ht
    ring

private theorem theta_inverseSquare_integrable {z : ℝ} (hz : 1 ≤ z) :
    IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / t ^ 2) volume 1 z := by
  have h := integrableOn_mul_sum_Icc thetaCoeff (by norm_num : (0 : ℝ) ≤ 1)
    (inverseSquare_continuous z).integrableOn_Icc
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hz]
  simpa only [thetaCoeff_sum, div_eq_mul_inv, mul_comm] using h

/-- Chebyshev and Abel give a logarithmic bound, without a PNT input. -/
theorem logPrimeMass_le_log4_mul_one_add_log {z : ℝ} (hz : 1 ≤ z) :
    logPrimeMass z ≤ log 4 * (1 + log z) := by
  have hzpos : 0 < z := by linarith
  have hendpoint : Chebyshev.theta z / z ≤ log 4 := by
    exact (div_le_iff₀ hzpos).mpr (Chebyshev.theta_le_log4_mul_x hzpos.le)
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 z := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hz]
    exact continuousOn_id.inv₀ (fun t ht => by linarith [ht.1])
  have hint : (∫ t in 1..z, Chebyshev.theta t / t ^ 2) ≤ log 4 * log z := by
    calc
      _ ≤ ∫ t in 1..z, log 4 * t⁻¹ := by
        apply intervalIntegral.integral_mono_on hz
          (theta_inverseSquare_integrable hz) (hinv.const_mul (log 4))
        intro t ht
        have htpos : 0 < t := by linarith [ht.1]
        calc
          Chebyshev.theta t / t ^ 2 ≤ (log 4 * t) / t ^ 2 :=
            div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x htpos.le)
              (sq_nonneg t)
          _ = log 4 * t⁻¹ := by field_simp [htpos.ne']; ring
      _ = log 4 * log z := by
        rw [intervalIntegral.integral_const_mul,
          integral_inv_of_pos (by norm_num : (0 : ℝ) < 1) hzpos]
        simp
  rw [logPrimeMass_eq_theta_abel hz]
  nlinarith

/-- One explicit positive constant works uniformly before the real cutoff. -/
def primeMassConstant : ℝ := log 4 / log 2 + log 4

theorem primeMassConstant_pos : 0 < primeMassConstant := by
  unfold primeMassConstant
  have h2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  have h4 : 0 < log (4 : ℝ) := Real.log_pos (by norm_num)
  positivity

/-- The scalar input for the thin-left Euler logarithmic derivative. -/
theorem logPrimeMass_le {z : ℝ} (hz : 2 ≤ z) :
    logPrimeMass z ≤ primeMassConstant * log (max 2 z) := by
  have h2 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  have h4 : 0 ≤ log (4 : ℝ) := (Real.log_pos (by norm_num : (1 : ℝ) < 4)).le
  have hlog : log (2 : ℝ) ≤ log z := Real.log_le_log (by norm_num) hz
  have hconst : log 4 ≤ (log 4 / log 2) * log z := by
    calc
      log 4 = (log 4 / log 2) * log 2 := by field_simp [h2.ne']
      _ ≤ (log 4 / log 2) * log z := mul_le_mul_of_nonneg_left hlog (div_nonneg h4 h2.le)
  rw [max_eq_right hz]
  have h := logPrimeMass_le_log4_mul_one_add_log (by linarith : 1 ≤ z)
  unfold primeMassConstant
  nlinarith

theorem exists_logPrimeMass_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 2 ≤ z →
      (∑ p ∈ (Finset.range (Nat.floor z + 1)).filter Nat.Prime,
        log (p : ℝ) / (p : ℝ)) ≤ C * log (max 2 z) := by
  exact ⟨primeMassConstant, primeMassConstant_pos, fun z hz => logPrimeMass_le hz⟩

/-- The denominator p-1 costs at most a factor two, including p=2. -/
theorem prime_log_div_pred_sum_le {z : ℝ} (hz : 2 ≤ z) :
    (∑ p ∈ smallPrimes z, log (p : ℝ) / ((p : ℝ) - 1)) ≤
      (2 * primeMassConstant) * log (max 2 z) := by
  have hterm : (∑ p ∈ smallPrimes z, log (p : ℝ) / ((p : ℝ) - 1)) ≤
      2 * logPrimeMass z := by
    rw [logPrimeMass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (smallPrimes_prime hp).two_le
    have hppos : (0 : ℝ) < p := by linarith
    have hpred : 0 < (p : ℝ) - 1 := by linarith
    have hlog : 0 ≤ log (p : ℝ) := Real.log_nonneg (by linarith)
    apply (div_le_iff₀ hpred).mpr
    have hhalf : (p : ℝ) ≤ 2 * ((p : ℝ) - 1) := by linarith
    have hh := mul_le_mul_of_nonneg_left hhalf (div_nonneg hlog hppos.le)
    have hcancel : log (p : ℝ) / (p : ℝ) * (p : ℝ) = log (p : ℝ) :=
      div_mul_cancel₀ _ hppos.ne'
    nlinarith
  calc
    _ ≤ 2 * logPrimeMass z := hterm
    _ ≤ 2 * (primeMassConstant * log (max 2 z)) :=
      mul_le_mul_of_nonneg_left (logPrimeMass_le hz) (by norm_num)
    _ = _ := by ring

end
end ImbalancedChen.Part3.RoughWeightedPrimeMass20261026b
