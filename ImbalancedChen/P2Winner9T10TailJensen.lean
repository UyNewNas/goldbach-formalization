import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Degree-ten negative-binomial Jensen gap

The remainder after the degree-ten truncation of `(1 - y)⁻¹⁰` is convex on
`[0, q]` for `q < 1`. Its second derivative is 110 times a nonnegative
negative-binomial remainder of order twelve and degree eight. Applying
Jensen's inequality to the degree-ten remainder gives the moment correction.
-/

namespace ImbalancedChen.P2Winner9T10TailJensen

noncomputable section

open Set MeasureTheory
open scoped BigOperators

def binomial10 (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 11, ((9 + k).choose k : ℝ) * y^k

def binomial10RemainderNumerator (y : ℝ) : ℝ :=
  y^11 * ∑ j ∈ Finset.range 10, ((10 + j).choose j : ℝ) * (1 - y)^j

/-- Exact finite negative-binomial tail identity, proved algebraically. -/
theorem binomial10_remainder_identity (y : ℝ) :
    (1 - y)^10 * binomial10 y + binomial10RemainderNumerator y = 1 := by
  simp only [binomial10, binomial10RemainderNumerator, Finset.sum_range_succ]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  ring

theorem binomial10_remainder_nonneg {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ binomial10RemainderNumerator y := by
  apply mul_nonneg (pow_nonneg hy _)
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sub_nonneg.mpr hy1) _)

/-- The degree-ten truncation is a pointwise lower bound on `[0, 1)`. -/
theorem binomial10_pointwise {y : ℝ} (hy : 0 ≤ y) (hy1 : y < 1) :
    binomial10 y ≤ 1 / (1 - y)^10 := by
  have hd : 0 < (1 - y)^10 := by positivity
  apply (le_div_iff₀ hd).2
  have h := binomial10_remainder_identity y
  have hr := binomial10_remainder_nonneg hy hy1.le
  nlinarith

def binomialPolynomial : Polynomial ℝ :=
  ∑ k ∈ Finset.range 11, Polynomial.C ((9 + k).choose k : ℝ) * Polynomial.X^k

theorem binomialPolynomial_eval (y : ℝ) :
    binomialPolynomial.eval y = binomial10 y := by
  simp only [binomialPolynomial, binomial10, Polynomial.eval_finsetSum,
    Polynomial.eval_C_mul, Polynomial.eval_X_pow]

def tail (y : ℝ) : ℝ := 1 / (1 - y)^10 - binomialPolynomial.eval y

def tailFirst (y : ℝ) : ℝ := 10 / (1 - y)^11 - binomialPolynomial.derivative.eval y

def tailSecond (y : ℝ) : ℝ :=
  110 / (1 - y)^12 - binomialPolynomial.derivative.derivative.eval y

def secondTruncation (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 9, ((11 + k).choose k : ℝ) * y^k

def secondTailNumerator (y : ℝ) : ℝ :=
  y^9 * ∑ j ∈ Finset.range 12, ((8 + j).choose j : ℝ) * (1 - y)^j

theorem secondTail_identity (y : ℝ) :
    (1 - y)^12 * secondTruncation y + secondTailNumerator y = 1 := by
  simp only [secondTruncation, secondTailNumerator, Finset.sum_range_succ]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  ring

theorem secondTail_nonneg {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ secondTailNumerator y := by
  apply mul_nonneg (pow_nonneg hy _)
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sub_nonneg.mpr hy1) _)

theorem secondTruncation_le {y : ℝ} (hy : 0 ≤ y) (hy1 : y < 1) :
    secondTruncation y ≤ 1 / (1 - y)^12 := by
  have hd : 0 < (1 - y)^12 := by positivity
  apply (le_div_iff₀ hd).2
  have h := secondTail_identity y
  have hr := secondTail_nonneg hy hy1.le
  nlinarith

theorem binomial_second_derivative (y : ℝ) :
    binomialPolynomial.derivative.derivative.eval y = 110 * secondTruncation y := by
  simp only [binomialPolynomial, secondTruncation, Polynomial.derivative_sum,
    Polynomial.derivative_C_mul_X_pow, Polynomial.eval_finsetSum, Polynomial.eval_C_mul,
    Polynomial.eval_X_pow]
  simp only [Finset.sum_range_succ]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
  ring

theorem tail_hasDerivAt {y : ℝ} (hy : y < 1) : HasDerivAt tail (tailFirst y) y := by
  have hd : 1 - y ≠ 0 := ne_of_gt (sub_pos.mpr hy)
  have hi := (((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).inv hd).pow 10
  have h := hi.sub (binomialPolynomial.hasDerivAt y)
  convert! h using 1
  · funext x
    simp only [tail, Pi.sub_apply, Pi.pow_apply, Pi.inv_apply, id_eq, one_div, inv_pow]
  · dsimp [tailFirst]
    field_simp [hd]
    ring

theorem tailFirst_hasDerivAt {y : ℝ} (hy : y < 1) :
    HasDerivAt tailFirst (tailSecond y) y := by
  have hd : 1 - y ≠ 0 := ne_of_gt (sub_pos.mpr hy)
  have hi := ((((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).inv hd).pow 11).const_mul 10
  have h := hi.sub (binomialPolynomial.derivative.hasDerivAt y)
  convert! h using 1
  · funext x
    simp only [tailFirst, Pi.sub_apply, Pi.pow_apply, Pi.inv_apply, id_eq, inv_pow, div_eq_mul_inv]
  · dsimp [tailSecond]
    field_simp [hd]
    ring

theorem tailSecond_nonneg {y : ℝ} (hy : 0 ≤ y) (hy1 : y < 1) :
    0 ≤ tailSecond y := by
  rw [tailSecond, binomial_second_derivative]
  have h := mul_le_mul_of_nonneg_left (secondTruncation_le hy hy1)
    (show (0 : ℝ) ≤ 110 by norm_num)
  simpa only [mul_div, mul_one] using sub_nonneg.mpr h

theorem tail_continuousOn {q : ℝ} (hq : q < 1) : ContinuousOn tail (Icc (0 : ℝ) q) := by
  intro y hy
  exact (tail_hasDerivAt (lt_of_le_of_lt hy.2 hq)).continuousAt.continuousWithinAt

/-- The degree-ten remainder is convex on every closed interval `[0, q]`
lying below the pole at `1`. -/
theorem tail_convexOn {q : ℝ} (hq : q < 1) : ConvexOn ℝ (Icc (0 : ℝ) q) tail := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 q) (tail_continuousOn hq)
    (f' := tailFirst) (f'' := tailSecond)
  · intro y hy
    exact (tail_hasDerivAt (lt_of_le_of_lt (interior_subset hy).2 hq)).hasDerivWithinAt
  · intro y hy
    exact (tailFirst_hasDerivAt (lt_of_le_of_lt (interior_subset hy).2 hq)).hasDerivWithinAt
  · intro y hy
    exact tailSecond_nonneg (interior_subset hy).1
      (lt_of_le_of_lt (interior_subset hy).2 hq)

/-- The integral of `(1 - Y)⁻¹⁰` exceeds its value at the mean by at least
the corresponding gap of the degree-ten truncation. -/
theorem probability_T10_gap {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (Y : α → ℝ) {q : ℝ} (hq : q < 1)
    (hYrange : ∀ᵐ x ∂ν, Y x ∈ Icc (0 : ℝ) q)
    (hY : Integrable Y ν)
    (hf : Integrable (fun x => 1 / (1 - Y x)^10) ν)
    (hPow : ∀ k ∈ Finset.range 11, Integrable (fun x => (Y x)^k) ν) :
    1 / (1 - ∫ x, Y x ∂ν)^10 +
      (∑ k ∈ Finset.range 11, ((9 + k).choose k : ℝ) *
        ((∫ x, (Y x)^k ∂ν) - (∫ x, Y x ∂ν)^k)) ≤
      ∫ x, 1 / (1 - Y x)^10 ∂ν := by
  have hB : Integrable (fun x => binomialPolynomial.eval (Y x)) ν := by
    simp only [binomialPolynomial_eval, binomial10]
    exact integrable_finsetSum (Finset.range 11)
      (fun k hk => (hPow k hk).const_mul _)
  have hTail : Integrable (fun x => tail (Y x)) ν := hf.sub hB
  have hJ := (tail_convexOn hq).map_integral_le (tail_continuousOn hq)
    isClosed_Icc hYrange hY hTail
  have hBI : (∫ x, binomialPolynomial.eval (Y x) ∂ν) =
      ∑ k ∈ Finset.range 11, ((9 + k).choose k : ℝ) *
        (∫ x, (Y x)^k ∂ν) := by
    simp only [binomialPolynomial_eval, binomial10]
    rw [integral_finsetSum (Finset.range 11)
      (fun k hk => (hPow k hk).const_mul _)]
    simp only [integral_const_mul]
  change tail (∫ x, Y x ∂ν) ≤ ∫ x, tail (Y x) ∂ν at hJ
  simp only [tail] at hJ
  rw [integral_sub hf hB, hBI, binomialPolynomial_eval, binomial10] at hJ
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith

end

end ImbalancedChen.P2Winner9T10TailJensen
