import ImbalancedChen.P2Winner9SelectedAnalyticRemainders
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The degree10 tail is convex on every [0,q], q<1. Its second derivative
is 110 times a genuine positive negative-binomial tail of order12/degree8.
Jensen is applied to that tail, rather than inferring the Jensen-gap bound
from a pointwise minorant alone. No target-shaped analytic bound is assumed.
-/

namespace ImbalancedChen.P2Winner9T10TailJensen

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2Winner9SelectedAnalyticRemainders

def binomialPolynomial : Polynomial ℝ :=
  ∑ k ∈ Finset.range 11, Polynomial.C ((9 + k).choose k : ℝ) * Polynomial.X^k

theorem binomialPolynomial_eval (y : ℝ) :
    binomialPolynomial.eval y = binomial10 y := by
  simp [binomialPolynomial, binomial10]

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
  norm_num [secondTruncation, secondTailNumerator, Finset.sum_range_succ]
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
  norm_num [binomialPolynomial, secondTruncation, Finset.sum_range_succ]
  ring

theorem tail_hasDerivAt {y : ℝ} (hy : y < 1) : HasDerivAt tail (tailFirst y) y := by
  have hd : 1 - y ≠ 0 := ne_of_gt (sub_pos.mpr hy)
  have hi := (((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).inv hd).pow 10
  have h := hi.sub (binomialPolynomial.hasDerivAt y)
  convert h using 1
  · ext x
    simp only [tail, one_div, inv_pow]
  · dsimp [tailFirst]
    field_simp [hd] <;> ring

theorem tailFirst_hasDerivAt {y : ℝ} (hy : y < 1) :
    HasDerivAt tailFirst (tailSecond y) y := by
  have hd : 1 - y ≠ 0 := ne_of_gt (sub_pos.mpr hy)
  have hi := ((((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).inv hd).pow 11).const_mul 10
  have h := hi.sub (binomialPolynomial.derivative.hasDerivAt y)
  convert h using 1
  · ext x
    simp only [tailFirst, one_div, inv_pow, div_eq_mul_inv]
  · dsimp [tailSecond]
    field_simp [hd] <;> ring

theorem tailSecond_nonneg {y : ℝ} (hy : 0 ≤ y) (hy1 : y < 1) :
    0 ≤ tailSecond y := by
  rw [tailSecond, binomial_second_derivative]
  have h := secondTruncation_le hy hy1
  nlinarith

theorem tail_continuousOn {q : ℝ} (hq : q < 1) : ContinuousOn tail (Icc (0 : ℝ) q) := by
  intro y hy
  exact (tail_hasDerivAt (lt_of_le_of_lt hy.2 hq)).continuousAt.continuousWithinAt

/-- The missing Jensen-GAP tail convexity, including the closed lower
endpoint0. The interior derivative theorem avoids any unproved extension
past the pole at1. -/
theorem tail_convexOn {q : ℝ} (hq : q < 1) : ConvexOn ℝ (Icc (0 : ℝ) q) tail := by
  apply convexOn_of_hasDerivWithinAt2_nonneg convex_Icc (tail_continuousOn hq)
    (f' := tailFirst) (f'' := tailSecond)
  · intro y hy
    exact (tail_hasDerivAt (lt_of_le_of_lt (interior_subset hy).2 hq)).hasDerivWithinAt
  · intro y hy
    exact (tailFirst_hasDerivAt (lt_of_le_of_lt (interior_subset hy).2 hq)).hasDerivWithinAt
  · intro y hy
    exact tailSecond_nonneg (interior_subset hy).1
      (lt_of_le_of_lt (interior_subset hy).2 hq)

/-- Jensen on the ACTUAL tail yields the degree10 gap, not just a lower
polynomial for the reciprocal. Integrability hypotheses are genuine
measure-theory conditions, supplied by the compact physical row caller. -/
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
