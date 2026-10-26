import ImbalancedChen.Part3RamanujanDivisorPrimeHecke

/-! Exact arithmetic normalization of the genuine Eisenstein divisor
coefficient. Positive-base complex powers turn the actual divisor Hecke
recurrence into its symmetric p^(s-1/2)+p^(1/2-s) form. This is independent
of every held physical Fourier coefficient theorem.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Complex
open ImbalancedChen.Part3ActualRamanujanDirichletSeries
open ImbalancedChen.Part3.RamanujanDivisorPrimeHecke20261026b

namespace ImbalancedChen.Part3.NormalizedEisensteinPrimeAmplitude20261026b

def normalizedDivisorAmplitude (n : ℕ) (s : ℂ) : ℂ :=
  (n : ℂ) ^ (s - 1 / 2) * divisorFactor n (2 * s)

private theorem prime_power_normalization {p : ℕ} (hp : p.Prime) (s : ℂ) :
    (p : ℂ) ^ (s - 1 / 2) * ((p : ℂ) * (p : ℂ) ^ (-(2 * s))) =
        (p : ℂ) ^ (1 / 2 - s) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpow : (p : ℂ) * (p : ℂ) ^ (-(2 * s)) = (p : ℂ) ^ (1 - 2 * s) := by
    calc
      _ = (p : ℂ) ^ (1 : ℂ) * (p : ℂ) ^ (-(2 * s)) := by rw [Complex.cpow_one]
      _ = (p : ℂ) ^ (1 + -(2 * s)) := (Complex.cpow_add _ _ hp0).symm
      _ = _ := by congr 1; ring
  rw [hpow, ← Complex.cpow_add _ _ hp0]
  congr 1
  ring

private theorem prime_power_inverse {p : ℕ} (hp : p.Prime) (s : ℂ) :
    (p : ℂ) ^ (s - 1 / 2) * (p : ℂ) ^ (1 / 2 - s) = 1 := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  rw [← Complex.cpow_add _ _ hp0, show (s - 1 / 2) + (1 / 2 - s) = 0 by ring]
  exact Complex.cpow_zero _

/-- Exact symmetric prime-frequency recurrence of the actual finite
normalized divisor amplitudes, retaining the ordinary frequency gate. -/
theorem normalizedDivisorAmplitude_prime_hecke {p : ℕ} (hp : p.Prime)
    (n : ℕ) (hn : 0 < n) (s : ℂ) (hs : 1 / 2 < s.re) :
    normalizedDivisorAmplitude (p * n) s +
      (if p ∣ n then normalizedDivisorAmplitude (n / p) s else 0) =
        ((p : ℂ) ^ (s - 1 / 2) + (p : ℂ) ^ (1 / 2 - s)) *
          normalizedDivisorAmplitude n s := by
  classical
  have hD := divisorFactor_prime_hecke hp (n : ℤ)
    (by exact_mod_cast hn.ne') (2 * s) (by simp; linarith)
  simp only [Int.natAbs_mul, Int.natAbs_natCast, Int.natCast_dvd_natCast,
    ← Int.natCast_div] at hD
  have hm : ((p * n : ℕ) : ℂ) ^ (s - 1 / 2) =
      (p : ℂ) ^ (s - 1 / 2) * (n : ℂ) ^ (s - 1 / 2) := by
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  have hc : (p : ℂ) ^ (s - 1 / 2) * (1 + (p : ℂ) * (p : ℂ) ^ (-(2 * s))) =
      (p : ℂ) ^ (s - 1 / 2) + (p : ℂ) ^ (1 / 2 - s) := by
    rw [mul_add, mul_one, prime_power_normalization hp s]
  unfold normalizedDivisorAmplitude
  rw [hm, hD]
  by_cases hd : p ∣ n
  · simp only [if_pos hd]
    have hproduct : ((n : ℕ) : ℂ) ^ (s - 1 / 2) =
        (p : ℂ) ^ (s - 1 / 2) * ((n / p : ℕ) : ℂ) ^ (s - 1 / 2) := by
      calc
        _ = (((p * (n / p) : ℕ) : ℂ) ^ (s - 1 / 2)) :=
          congrArg (fun k : ℕ => (k : ℂ) ^ (s - 1 / 2)) (Nat.mul_div_cancel' hd).symm
        _ = _ := by rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    have hcancel : (p : ℂ) ^ (s - 1 / 2) * (n : ℂ) ^ (s - 1 / 2) *
        ((p : ℂ) * (p : ℂ) ^ (-(2 * s))) = ((n / p : ℕ) : ℂ) ^ (s - 1 / 2) := by
      calc
        _ = ((p : ℂ) ^ (s - 1 / 2) * ((p : ℂ) * (p : ℂ) ^ (-(2 * s)))) *
            (n : ℂ) ^ (s - 1 / 2) := by ring
        _ = (p : ℂ) ^ (1 / 2 - s) *
            ((p : ℂ) ^ (s - 1 / 2) * ((n / p : ℕ) : ℂ) ^ (s - 1 / 2)) := by
          rw [prime_power_normalization hp s, hproduct]
        _ = ((p : ℂ) ^ (s - 1 / 2) * (p : ℂ) ^ (1 / 2 - s)) *
            ((n / p : ℕ) : ℂ) ^ (s - 1 / 2) := by ring
        _ = _ := by rw [prime_power_inverse hp s, one_mul]
    linear_combination ((n : ℂ) ^ (s - 1 / 2) * divisorFactor n (2 * s)) * hc -
      divisorFactor (n / p) (2 * s) * hcancel
  · simp only [if_neg hd]
    linear_combination ((n : ℂ) ^ (s - 1 / 2) * divisorFactor n (2 * s)) * hc

end ImbalancedChen.Part3.NormalizedEisensteinPrimeAmplitude20261026b
