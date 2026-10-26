import ImbalancedChen.Part3EisensteinPrimePowerSplitBound
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Actual local Euler convergence on the critical line. The proved
prime-power amplitude bound pays absolute convergence. The genuine Cauchy
product of two absolutely convergent geometric series evaluates the sum;
the quadratic denominator is proved nonzero before its inverse is used.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Complex Finset
open scoped BigOperators
open ImbalancedChen.Part3.NormalizedEisensteinPrimeAmplitude20261026b
open ImbalancedChen.Part3.EisensteinPrimePowerSplitBound20261026b

namespace ImbalancedChen.Part3.ActualCriticalPrimeEulerSeries20261026b

def criticalPrimeScalar (p : ℕ) (t : ℝ) : ℂ :=
  (p : ℂ) ^ ((1 / 2 + (t : ℂ) * Complex.I) - 1 / 2) +
    (p : ℂ) ^ (1 / 2 - (1 / 2 + (t : ℂ) * Complex.I))

def actualCriticalLocalEulerSeries (p : ℕ) (t : ℝ) (X : ℂ) : ℂ :=
  ∑' k : ℕ, normalizedDivisorAmplitude (p ^ k) (1 / 2 + (t : ℂ) * Complex.I) * X ^ k

/-- Absolute convergence is proved from actual amplitudes, not supplied
as a hypothesis to a Cauchy-product theorem. -/
theorem actualCriticalLocalEuler_norm_summable {p : ℕ} (hp : p.Prime)
    (t : ℝ) {X : ℂ} (hX : ‖X‖ < 1) :
    Summable (fun k : ℕ =>
      ‖normalizedDivisorAmplitude (p ^ k) (1 / 2 + (t : ℂ) * Complex.I) * X ^ k‖) := by
  have hr : ‖(‖X‖ : ℝ)‖ < 1 := by simpa only [Real.norm_eq_abs, abs_norm] using hX
  have hnat : Summable (fun k : ℕ => (k : ℝ) * ‖X‖ ^ k) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable
  have hgeom : Summable (fun k : ℕ => ‖X‖ ^ k) := summable_geometric_of_norm_lt_one hr
  have hmajor : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * ‖X‖ ^ k) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hnat.add hgeom
  apply hmajor.of_nonneg_of_le (fun k => norm_nonneg _) ?_
  intro k
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right
    (normalizedAmplitude_prime_power_critical_norm hp k t) (pow_nonneg (norm_nonneg X) k)

/-- A genuine convergent local Euler factor, uniformly valid for every
prime and real t on the full disk |X|<1, including the central double root. -/
theorem actualCriticalLocalEuler_eq_inverse {p : ℕ} (hp : p.Prime)
    (t : ℝ) {X : ℂ} (hX : ‖X‖ < 1) :
    1 - criticalPrimeScalar p t * X + X ^ 2 ≠ 0 ∧
      actualCriticalLocalEulerSeries p t X =
        (1 - criticalPrimeScalar p t * X + X ^ 2)⁻¹ := by
  let a : ℂ := (p : ℂ) ^ ((1 / 2 + (t : ℂ) * Complex.I) - 1 / 2)
  let b : ℂ := (p : ℂ) ^ (1 / 2 - (1 / 2 + (t : ℂ) * Complex.I))
  have ha : ‖a‖ = 1 := by
    dsimp [a]
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    simp [Complex.mul_re]
  have hb : ‖b‖ = 1 := by
    dsimp [b]
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    simp [Complex.mul_re]
  have haX : ‖a * X‖ < 1 := by simpa only [norm_mul, ha, one_mul] using hX
  have hbX : ‖b * X‖ < 1 := by simpa only [norm_mul, hb, one_mul] using hX
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hab : a * b = 1 := by
    dsimp [a, b]
    rw [← Complex.cpow_add _ _ hp0,
      show ((1 / 2 + (t : ℂ) * Complex.I) - 1 / 2) +
        (1 / 2 - (1 / 2 + (t : ℂ) * Complex.I)) = 0 by ring, Complex.cpow_zero]
  have hdeneq : (1 - a * X) * (1 - b * X) =
      1 - criticalPrimeScalar p t * X + X ^ 2 := by
    change (1 - a * X) * (1 - b * X) = 1 - (a + b) * X + X ^ 2
    calc
      _ = 1 - (a + b) * X + (a * b) * X ^ 2 := by ring
      _ = _ := by rw [hab, one_mul]
  have hna : 1 - a * X ≠ 0 := by
    intro he
    have h : a * X = 1 := (sub_eq_zero.mp he).symm
    simpa only [h, norm_one, lt_self_iff_false] using haX
  have hnb : 1 - b * X ≠ 0 := by
    intro he
    have h : b * X = 1 := (sub_eq_zero.mp he).symm
    simpa only [h, norm_one, lt_self_iff_false] using hbX
  refine ⟨?_, ?_⟩
  · rw [← hdeneq]
    exact mul_ne_zero hna hnb
  · have hterm (k : ℕ) :
        (∑ j ∈ range (k + 1), (b * X) ^ j * (a * X) ^ (k - j)) =
          normalizedDivisorAmplitude (p ^ k) (1 / 2 + (t : ℂ) * Complex.I) * X ^ k := by
      rw [normalizedAmplitude_prime_power_split hp, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      have hjle : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      change (b * X) ^ j * (a * X) ^ (k - j) = (a ^ (k - j) * b ^ j) * X ^ k
      calc
        _ = (a ^ (k - j) * b ^ j) * (X ^ (k - j) * X ^ j) := by
          simp only [mul_pow]
          ring
        _ = _ := by rw [← pow_add, Nat.sub_add_cancel hjle]
    have hprod := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
      (summable_norm_geometric_of_norm_lt_one hbX)
      (summable_norm_geometric_of_norm_lt_one haX)
    simp_rw [hterm] at hprod
    rw [tsum_geometric_of_norm_lt_one hbX, tsum_geometric_of_norm_lt_one haX] at hprod
    change (∑' k : ℕ,
      normalizedDivisorAmplitude (p ^ k) (1 / 2 + (t : ℂ) * Complex.I) * X ^ k) = _
    rw [← hprod, ← hdeneq, mul_inv_rev]

end ImbalancedChen.Part3.ActualCriticalPrimeEulerSeries20261026b
