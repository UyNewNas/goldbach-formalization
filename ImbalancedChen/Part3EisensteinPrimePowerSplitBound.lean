import ImbalancedChen.Part3EisensteinPrimePowerEulerPolynomial

/-! Division-free split-root prime-power amplitudes and an actual uniform
critical-line bound. The finite sum handles coincident roots at s=1/2;
there is no quotient by their difference. SOURCE ONLY / UNCOMPILED / ZERO CREDIT. -/

noncomputable section
open Complex Finset
open scoped BigOperators
open ImbalancedChen.Part3.NormalizedEisensteinPrimeAmplitude20261026b
open ImbalancedChen.Part3.EisensteinPrimePowerEulerPolynomial20261026b

namespace ImbalancedChen.Part3.EisensteinPrimePowerSplitBound20261026b

def splitSum (k : ℕ) (a b : ℂ) : ℂ := ∑ j ∈ range (k + 1), a ^ (k - j) * b ^ j

private theorem splitSum_shift (k : ℕ) (a b : ℂ) :
    splitSum (k + 1) a b = a * splitSum k a b + b ^ (k + 1) := by
  unfold splitSum
  rw [Finset.sum_range_succ, Finset.mul_sum]
  simp only [Nat.sub_self, pow_zero, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ]
  ring

/-- Exact split-root identity, valid also at a=b. -/
theorem primeHeckePolynomial_split (k : ℕ) (a b : ℂ) (hab : a * b = 1) :
    primeHeckePolynomial k (a + b) = splitSum k a b := by
  induction k using Nat.twoStepInduction with
  | zero => simp [primeHeckePolynomial, splitSum]
  | one => simp [primeHeckePolynomial, splitSum, Finset.sum_range_succ]
  | more k ih ih1 =>
      rw [primeHeckePolynomial, ih1, ih]
      have hS := splitSum_shift (k + 1) a b
      have hT := splitSum_shift k a b
      simp only [pow_succ] at hS hT
      linear_combination -hS + b * hT + splitSum k a b * hab

/-- Literal principal-power roots give every actual prime-power amplitude
as a finite sum. No discriminant or central cancellation is assumed. -/
theorem normalizedAmplitude_prime_power_split {p : ℕ} (hp : p.Prime)
    (k : ℕ) (s : ℂ) :
    normalizedDivisorAmplitude (p ^ k) s =
      ∑ j ∈ range (k + 1), ((p : ℂ) ^ (s - 1 / 2)) ^ (k - j) *
        ((p : ℂ) ^ (1 / 2 - s)) ^ j := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hab : (p : ℂ) ^ (s - 1 / 2) * (p : ℂ) ^ (1 / 2 - s) = 1 := by
    rw [← Complex.cpow_add _ _ hp0,
      show (s - 1 / 2) + (1 / 2 - s) = 0 by ring, Complex.cpow_zero]
  rw [normalizedAmplitude_prime_power hp]
  exact primeHeckePolynomial_split k _ _ hab

/-- Genuine uniform bound for all real t and all prime powers, including
the repeated central root. This pays the finite Euler boundary errors. -/
theorem normalizedAmplitude_prime_power_critical_norm {p : ℕ} (hp : p.Prime)
    (k : ℕ) (t : ℝ) :
    ‖normalizedDivisorAmplitude (p ^ k) (1 / 2 + (t : ℂ) * Complex.I)‖ ≤
      ((k + 1 : ℕ) : ℝ) := by
  have ha : ‖(p : ℂ) ^ ((1 / 2 + (t : ℂ) * Complex.I) - 1 / 2)‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    simp [Complex.mul_re]
  have hb : ‖(p : ℂ) ^ (1 / 2 - (1 / 2 + (t : ℂ) * Complex.I))‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    simp [Complex.mul_re]
  rw [normalizedAmplitude_prime_power_split hp]
  calc
    _ ≤ ∑ j ∈ range (k + 1),
        ‖((p : ℂ) ^ ((1 / 2 + (t : ℂ) * Complex.I) - 1 / 2)) ^ (k - j) *
          ((p : ℂ) ^ (1 / 2 - (1 / 2 + (t : ℂ) * Complex.I))) ^ j‖ :=
      norm_sum_le _ _
    _ = _ := by simp [norm_mul, norm_pow, ha, hb]

end ImbalancedChen.Part3.EisensteinPrimePowerSplitBound20261026b
