import ImbalancedChen.P2Winner9FiniteMomentKernel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Normalize the factorial measure and the signed integer vertex scales in
one degree-one mixed moment. -/

namespace ImbalancedChen.P2Winner9MomentNormalization

open scoped BigOperators
open ImbalancedChen.P2Winner9FiniteMomentKernel (kernel)

private theorem sum_div {R : Type*} [Field R] {n : ℕ} (f : Fin n → R) (x : R) :
    (∑ i, f i) / x = ∑ i, f i / x := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

/-- Recover the signed certificate numerator after moving the common factors
out of the measured fourth-degree finite sum. -/
theorem from_weighted_sum {R : Type*} [Field R] [CharZero R]
    (g y : Fin 9 → ℕ) (z : Fin 9 → ℤ) (G U L : ℕ) (numerator : ℤ)
    (hNum : (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, ∑ e : Fin 9,
      (g a : ℤ) * (y b : ℤ) * z c * z e * kernel a b c e) = numerator) :
    (((9 : ℕ).factorial : R) / (G : R)) *
      (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, ∑ e : Fin 9,
        (((g a : R) * ((y b : R) / U) * ((z c : R) / L) * ((z e : R) / L)) *
          ((kernel a b c e : R) / ((12 : ℕ).factorial : R)))) =
      (numerator : R) / ((G : R) * U * L ^ 2 * (10 * 11 * 12)) := by
  have hscale (a b c e : Fin 9) :
      (((g a : R) * ((y b : R) / U) * ((z c : R) / L) * ((z e : R) / L)) *
        ((kernel a b c e : R) / ((12 : ℕ).factorial : R))) =
      (((g a : ℤ) * (y b : ℤ) * z c * z e * kernel a b c e : ℤ) : R) /
        ((U : R) * L ^ 2 * ((12 : ℕ).factorial : R)) := by
    simp only [Int.cast_mul, Int.cast_natCast, div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [hscale, ← sum_div]
  have hCast : (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, ∑ e : Fin 9,
      (((g a : ℤ) * (y b : ℤ) * z c * z e * kernel a b c e : ℤ) : R)) =
        (numerator : R) := by
    exact_mod_cast hNum
  rw [hCast]
  norm_num [Nat.factorial_succ]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end ImbalancedChen.P2Winner9MomentNormalization
