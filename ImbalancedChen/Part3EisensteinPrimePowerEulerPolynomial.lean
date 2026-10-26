import ImbalancedChen.Part3EntireEisensteinPrimeAmplitude

/-! Exact prime-power arithmetic and its finite Euler denominator.
The actual entire normalized Eisenstein amplitudes are identified with
the uniquely determined prime recurrence polynomial. A finite generating
identity retains both boundary terms, so no infinite-series convergence
or Euler product is assumed. SOURCE ONLY / UNCOMPILED / ZERO CREDIT. -/

noncomputable section
open Finset Complex
open scoped BigOperators
open ImbalancedChen.Part3ActualRamanujanDirichletSeries
open ImbalancedChen.Part3.NormalizedEisensteinPrimeAmplitude20261026b
open ImbalancedChen.Part3.EntireEisensteinPrimeAmplitude20261026b

namespace ImbalancedChen.Part3.EisensteinPrimePowerEulerPolynomial20261026b

def primeHeckePolynomial : ℕ → ℂ → ℂ
  | 0, _ => 1
  | 1, z => z
  | k + 2, z => z * primeHeckePolynomial (k + 1) z - primeHeckePolynomial k z

private theorem normalizedAmplitude_one (s : ℂ) : normalizedDivisorAmplitude 1 s = 1 := by
  simp [normalizedDivisorAmplitude, divisorFactor]

/-- Actual prime powers, including repeated prime exponents, are the
canonical recurrence polynomials at the genuine symmetric prime scalar. -/
theorem normalizedAmplitude_prime_power {p : ℕ} (hp : p.Prime) (k : ℕ) (s : ℂ) :
    normalizedDivisorAmplitude (p ^ k) s =
      primeHeckePolynomial k ((p : ℂ) ^ (s - 1 / 2) + (p : ℂ) ^ (1 / 2 - s)) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [primeHeckePolynomial, normalizedAmplitude_one]
  | one =>
      have hd : ¬p ∣ 1 := hp.not_dvd_one
      have h := normalizedDivisorAmplitude_prime_hecke_entire hp 1 (by norm_num) s
      simpa only [mul_one, if_neg hd, add_zero, normalizedAmplitude_one,
        primeHeckePolynomial, pow_one] using h
  | more k ih ih1 =>
      have hd : p ∣ p ^ (k + 1) := ⟨p ^ k, pow_succ' p k⟩
      have hupper : p * p ^ (k + 1) = p ^ (k + 2) := by
        rw [show k + 2 = (k + 1) + 1 by omega, pow_succ']
      have hquot : p ^ (k + 1) / p = p ^ k := by
        rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
      have h := normalizedDivisorAmplitude_prime_hecke_entire hp
        (p ^ (k + 1)) (pow_pos hp.pos _) s
      rw [if_pos hd, hupper, hquot, ih, ih1] at h
      change normalizedDivisorAmplitude (p ^ (k + 2)) s =
        _ * primeHeckePolynomial (k + 1) _ - primeHeckePolynomial k _
      exact (eq_sub_iff_add_eq).mpr h

/-- Finite generating identity with the exact quadratic Euler denominator.
Both terminal errors are kept; this statement makes no convergence claim. -/
theorem primeHeckePolynomial_finite_euler (M : ℕ) (z X : ℂ) :
    (1 - z * X + X ^ 2) * (∑ k ∈ range (M + 1), primeHeckePolynomial k z * X ^ k) =
      1 - primeHeckePolynomial (M + 1) z * X ^ (M + 1) +
        primeHeckePolynomial M z * X ^ (M + 2) := by
  induction M with
  | zero => simp [primeHeckePolynomial]
  | succ M ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      simp only [primeHeckePolynomial, pow_succ]
      ring

/-- The same exact finite Euler identity for the actual amplitudes at
every complex parameter, including the central spectral parameter. -/
theorem normalizedAmplitude_prime_power_finite_euler {p : ℕ} (hp : p.Prime)
    (M : ℕ) (s X : ℂ) :
    (1 - ((p : ℂ) ^ (s - 1 / 2) + (p : ℂ) ^ (1 / 2 - s)) * X + X ^ 2) *
      (∑ k ∈ range (M + 1), normalizedDivisorAmplitude (p ^ k) s * X ^ k) =
        1 - normalizedDivisorAmplitude (p ^ (M + 1)) s * X ^ (M + 1) +
          normalizedDivisorAmplitude (p ^ M) s * X ^ (M + 2) := by
  simp_rw [normalizedAmplitude_prime_power hp]
  exact primeHeckePolynomial_finite_euler M _ X

end ImbalancedChen.Part3.EisensteinPrimePowerEulerPolynomial20261026b
