import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Exponential

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The all-orders factorial heat bound follows from the actual exponential
series term bound. No heat estimate or spectral supplier is assumed.
-/

namespace ImbalancedChen.Part3.HeatFactorialScalarBound20261025a
noncomputable section

theorem pow_mul_exp_neg_mul_le_factorial_div_pow
    {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) (n : ℕ) :
    x ^ n * Real.exp (-s * x) ≤ (n.factorial : ℝ) / s ^ n := by
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hterm := Real.pow_div_factorial_le_exp (mul_nonneg hs.le hx) n
  have hpow : (s * x) ^ n ≤ (n.factorial : ℝ) * Real.exp (s * x) := by
    have h := (div_le_iff₀ hfac).1 hterm
    simpa only [mul_comm] using h
  have hmul := mul_le_mul_of_nonneg_right hpow (Real.exp_pos (-(s * x))).le
  have hexp : Real.exp (s * x) * Real.exp (-(s * x)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [mul_assoc, hexp, mul_one] at hmul
  apply (le_div_iff₀ (pow_pos hs n)).2
  calc
    _ = (s * x) ^ n * Real.exp (-(s * x)) := by
      rw [mul_pow, show -(s * x) = -s * x by ring]
      ring
    _ ≤ _ := hmul

end
end ImbalancedChen.Part3.HeatFactorialScalarBound20261025a
