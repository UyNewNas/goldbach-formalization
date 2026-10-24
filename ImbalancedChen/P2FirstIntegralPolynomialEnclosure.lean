import ImbalancedChen.P2FirstIntegralSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / NOT ELABORATED / no numerical producer or endpoint replay.
Prospective import staging: sibling P2FirstIntegralSeries.lean must be installed
as ImbalancedChen/P2FirstIntegralSeries.lean for a future authorized build.

Closed polynomial evaluation route for the full original first integral.
After the exact translation x=s-2, the domain is [0,51/2375].  Approximate
log(1+x) by its signed Taylor polynomial and 1/(2+x) by a finite geometric
polynomial.  The product has explicitly rational coefficients.  Every monomial
integral is evaluated by Mathlib's proved `intervalIntegral.integral_pow`.

The uniform remainder is derived from the actual logarithm Taylor remainder
and an exact finite-geometric identity.  It is not an endpoint assumption.
The final center and radius are explicit rationals; the order-16 instance
has a source-level exact arithmetic proof of radius <= 2^(-80).

OPEN GAP: the finite rational center has not been numerically evaluated or
compared with the unavailable selected U1 frozen decimal payload.  This file
does not claim a local successful elaboration or the original hUpper result.
-/

namespace ImbalancedChen.P2FirstIntegralPolynomialEnclosureSourceOnly

noncomputable section

open Set MeasureTheory
open P2FirstIntegralSeriesSourceOnly

def d : ℝ := 51 / 2375

def dQ : ℚ := 51 / 2375

theorem d_nonneg : 0 ≤ d := by norm_num [d]

theorem d_lt_one : d < 1 := by norm_num [d]

def transformedKernel (x : ℝ) : ℝ := Real.log (1 + x) / (2 + x)

def logCoeff (i : ℕ) : ℝ := -((-1 : ℝ) ^ (i + 1)) / ((i : ℝ) + 1)

def reciprocalCoeff (j : ℕ) : ℝ := (1 / 2 : ℝ) * (-1 / 2 : ℝ) ^ j

def logPolynomial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, logCoeff i * x ^ (i + 1)

def reciprocalPolynomial (m : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, reciprocalCoeff j * x ^ j

def degree (i j : ℕ) : ℕ := i + j + 1

def coefficient (i j : ℕ) : ℝ := logCoeff i * reciprocalCoeff j

def approximant (n m : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, coefficient i j * x ^ degree i j

def logError (n : ℕ) : ℝ := d ^ (n + 1) / (1 - d)

def reciprocalError (m : ℕ) : ℝ := (d / 2) ^ m / 2

def uniformError (n m : ℕ) : ℝ :=
  logError n / 2 + (d + logError n) * reciprocalError m

def center (n m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
    coefficient i j * (d ^ (degree i j + 1) / ((degree i j : ℝ) + 1))

theorem logPolynomial_eq (n : ℕ) (x : ℝ) :
    logPolynomial n x = -(∑ i ∈ Finset.range n, (-x) ^ (i + 1) / ((i : ℝ) + 1)) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hp : (-x) ^ (i + 1) = (-1 : ℝ) ^ (i + 1) * x ^ (i + 1) := by
    rw [← mul_pow]
    congr 1
    ring
  rw [hp]
  dsimp [logCoeff]
  ring

theorem reciprocalPolynomial_eq (m : ℕ) (x : ℝ) :
    reciprocalPolynomial m x = (1 / 2 : ℝ) * ∑ j ∈ Finset.range m, (-x / 2) ^ j := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hp : (-x / 2) ^ j = (-1 / 2 : ℝ) ^ j * x ^ j := by
    rw [← mul_pow]
    congr 1
    ring
  rw [hp]
  dsimp [reciprocalCoeff]
  ring

theorem reciprocalPolynomial_succ (m : ℕ) (x : ℝ) :
    reciprocalPolynomial (m + 1) x =
      reciprocalPolynomial m x + (1 / 2 : ℝ) * (-x / 2) ^ m := by
  simp only [reciprocalPolynomial_eq, Finset.sum_range_succ]
  ring

/-- Exact identity for the finite geometric polynomial, not a truncation claim. -/
theorem reciprocal_remainder_exact (m : ℕ) {x : ℝ} (hx : 2 + x ≠ 0) :
    1 / (2 + x) - reciprocalPolynomial m x = (-x / 2) ^ m / (2 + x) := by
  induction m with
  | zero => simp [reciprocalPolynomial]
  | succ m ih =>
      rw [reciprocalPolynomial_succ]
      calc
        _ = (1 / (2 + x) - reciprocalPolynomial m x) -
            (1 / 2 : ℝ) * (-x / 2) ^ m := by ring
        _ = (-x / 2) ^ m / (2 + x) - (1 / 2 : ℝ) * (-x / 2) ^ m := by rw [ih]
        _ = (-x / 2) ^ (m + 1) / (2 + x) := by
          rw [pow_succ]
          field_simp [hx] <;> ring

theorem approximant_eq_product (n m : ℕ) (x : ℝ) :
    approximant n m x = logPolynomial n x * reciprocalPolynomial m x := by
  simp only [approximant, logPolynomial, reciprocalPolynomial,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show degree i j = (i + 1) + j by dsimp [degree]; omega, pow_add]
  dsimp [coefficient]
  ring

theorem logError_nonneg (n : ℕ) : 0 ≤ logError n := by
  exact div_nonneg (pow_nonneg d_nonneg _) (sub_nonneg.mpr d_lt_one.le)

theorem reciprocalError_nonneg (m : ℕ) : 0 ≤ reciprocalError m := by
  exact div_nonneg (pow_nonneg (div_nonneg d_nonneg (by norm_num)) _) (by norm_num)

theorem logPolynomial_error (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) d) :
    |Real.log (1 + x) - logPolynomial n x| ≤ logError n := by
  have hx1 : x < 1 := lt_of_le_of_lt hx.2 d_lt_one
  have ha : |-x| < 1 := by simpa only [abs_neg, abs_of_nonneg hx.1] using hx1
  have h := Real.abs_log_sub_add_sum_range_le ha n
  have hs : (∑ i ∈ Finset.range n, (-x) ^ (i + 1) / ((i : ℝ) + 1)) =
      -logPolynomial n x := by rw [logPolynomial_eq]; ring
  have hlocal : |Real.log (1 + x) - logPolynomial n x| ≤ x ^ (n + 1) / (1 - x) := by
    have he : Real.log (1 + x) - logPolynomial n x =
        -logPolynomial n x + Real.log (1 + x) := by ring
    simpa only [Nat.cast_add, Nat.cast_one, hs, sub_neg_eq_add, abs_neg, abs_of_nonneg hx.1,
      he] using h
  have hp : x ^ (n + 1) ≤ d ^ (n + 1) := pow_le_pow_left₀ hx.1 hx.2 _
  exact hlocal.trans ((div_le_div_of_nonneg_right hp (by linarith : 0 ≤ 1 - x)).trans
    (div_le_div_of_nonneg_left (pow_nonneg d_nonneg _)
      (by linarith [d_lt_one] : 0 < 1 - d) (by linarith [hx.2])))

theorem reciprocalPolynomial_error (m : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) d) :
    |1 / (2 + x) - reciprocalPolynomial m x| ≤ reciprocalError m := by
  have hx2 : 0 < 2 + x := by linarith [hx.1]
  rw [reciprocal_remainder_exact m hx2.ne', abs_div, abs_pow, abs_div, abs_neg,
    abs_of_nonneg hx.1, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hx2]
  have hp : (x / 2) ^ m ≤ (d / 2) ^ m :=
    pow_le_pow_left₀ (div_nonneg hx.1 (by norm_num)) (by linarith [hx.2]) _
  exact (div_le_div_of_nonneg_right hp hx2.le).trans
    (div_le_div_of_nonneg_left (pow_nonneg (div_nonneg d_nonneg (by norm_num)) _)
      (by norm_num) (by linarith [hx.1]))

theorem logPolynomial_abs_bound (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) d) :
    |logPolynomial n x| ≤ d + logError n := by
  have hl0 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith [hx.1])
  have hld : Real.log (1 + x) ≤ d :=
    (Real.log_le_sub_one_of_pos (by linarith [hx.1] : 0 < 1 + x)).trans (by linarith [hx.2])
  calc
    _ = |Real.log (1 + x) + (logPolynomial n x - Real.log (1 + x))| := by
      congr 1
      ring
    _ ≤ |Real.log (1 + x)| + |logPolynomial n x - Real.log (1 + x)| := abs_add _ _
    _ ≤ d + logError n := add_le_add (by simpa only [abs_of_nonneg hl0] using hld)
      (by simpa only [abs_sub_comm] using logPolynomial_error n hx)

/-- Actual analytic error of the polynomial product on the entire domain. -/
theorem transformedKernel_polynomial_error (n m : ℕ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) d) :
    |transformedKernel x - approximant n m x| ≤ uniformError n m := by
  have hx2 : 0 < 2 + x := by linarith [hx.1]
  rw [approximant_eq_product]
  have he : transformedKernel x - logPolynomial n x * reciprocalPolynomial m x =
      (Real.log (1 + x) - logPolynomial n x) / (2 + x) +
        logPolynomial n x * (1 / (2 + x) - reciprocalPolynomial m x) := by
    dsimp [transformedKernel]
    ring
  rw [he]
  apply (abs_add _ _).trans
  apply add_le_add
  · rw [abs_div, abs_of_pos hx2]
    exact (div_le_div_of_nonneg_right (logPolynomial_error n hx) hx2.le).trans
      (div_le_div_of_nonneg_left (logError_nonneg n) (by norm_num) (by linarith [hx.1]))
  · rw [abs_mul]
    exact mul_le_mul (logPolynomial_abs_bound n hx) (reciprocalPolynomial_error m hx)
      (abs_nonneg _) (add_nonneg d_nonneg (logError_nonneg n))

theorem continuous_approximant (n m : ℕ) : Continuous (approximant n m) := by
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  exact continuous_const.mul (continuous_id.pow _)

/-- Exact evaluation of all polynomial monomials. -/
theorem integral_approximant (n m : ℕ) :
    (∫ x in (0 : ℝ)..d, approximant n m x) = center n m := by
  unfold approximant center
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_pow]
      simp only [zero_pow (Nat.succ_ne_zero _), sub_zero]
    · intro j hj
      exact (continuous_const.mul (continuous_id.pow _)).intervalIntegrable 0 d
  · intro i hi
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul (continuous_id.pow _)

theorem intervalIntegrable_transformedKernel :
    IntervalIntegrable transformedKernel volume 0 d := by
  apply ContinuousOn.intervalIntegrable_of_Icc d_nonneg
  apply ((continuousOn_const.add continuousOn_id).log ?_).div
    (continuousOn_const.add continuousOn_id) ?_
  · intro x hx
    have h : 0 < 1 + x := by linarith [hx.1]
    exact h.ne'
  · intro x hx
    have h : 0 < 2 + x := by linarith [hx.1]
    exact h.ne'

theorem translated_integral_polynomial_error (n m : ℕ) :
    |(∫ x in (0 : ℝ)..d, transformedKernel x) - center n m| ≤ uniformError n m * d := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := d) (f := fun x => transformedKernel x - approximant n m x)
    (fun x hx => by
      rw [Set.uIoc_of_le d_nonneg] at hx
      simpa only [Real.norm_eq_abs] using
        transformedKernel_polynomial_error n m ⟨hx.1.le, hx.2⟩)
  rw [intervalIntegral.integral_sub intervalIntegrable_transformedKernel
    ((continuous_approximant n m).intervalIntegrable 0 d), integral_approximant,
    Real.norm_eq_abs] at h
  simpa only [sub_zero, abs_of_nonneg d_nonneg] using h

/-! Rational center and radius, including all normalization factors. -/

def coefficientQ (i j : ℕ) : ℚ :=
  (-((-1 : ℚ) ^ (i + 1)) / ((i : ℚ) + 1)) * ((1 / 2 : ℚ) * (-1 / 2 : ℚ) ^ j)

def centerQ (n m : ℕ) : ℚ :=
  (2000 / 299) * ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m,
    coefficientQ i j * (dQ ^ (degree i j + 1) / ((degree i j : ℚ) + 1))

def errorQ (n m : ℕ) : ℚ :=
  (dQ ^ (n + 1) / (1 - dQ)) / 2 +
    (dQ + dQ ^ (n + 1) / (1 - dQ)) * ((dQ / 2) ^ m / 2)

def radiusQ (n m : ℕ) : ℚ := (2000 / 299) * (errorQ n m * dQ)

theorem centerQ_cast (n m : ℕ) : (centerQ n m : ℝ) = (4 / theta) * center n m := by
  simp [centerQ, center, coefficientQ, coefficient, logCoeff, reciprocalCoeff, dQ, d, theta] <;> ring

theorem radiusQ_cast (n m : ℕ) :
    (radiusQ n m : ℝ) = (4 / theta) * (uniformError n m * d) := by
  simp [radiusQ, errorQ, dQ, uniformError, logError, reciprocalError, d, theta] <;> ring

/-- Fully rational enclosure of the actual first integral at every pair of
orders, with no finite rational-function integral left to evaluate. -/
theorem originalFirstIntegral_polynomial_enclosure (n m : ℕ) :
    ((centerQ n m - radiusQ n m : ℚ) : ℝ) ≤ originalFirstIntegral ∧
      originalFirstIntegral ≤ ((centerQ n m + radiusQ n m : ℚ) : ℝ) := by
  have h := abs_le.mp (translated_integral_polynomial_error n m)
  have hlo := mul_le_mul_of_nonneg_left h.1 prefactor_pos.le
  have hhi := mul_le_mul_of_nonneg_left h.2 prefactor_pos.le
  have he : originalFirstIntegral =
      (4 / theta) * ∫ x in (0 : ℝ)..d, transformedKernel x := by
    simpa only [width_eq, d, transformedKernel] using originalFirstIntegral_translate
  simp only [he]
  push_cast
  simp only [centerQ_cast, radiusQ_cast]
  constructor <;> nlinarith

/-- Only exact rational arithmetic is requested by this proof body.  This is
written source, not a claim that a local numeric producer or Lean was run. -/
theorem radiusQ_sixteen_le_Q80 : radiusQ 16 16 ≤ (1 / 2 ^ 80 : ℚ) := by
  norm_num [radiusQ, errorQ, dQ]

theorem originalFirstIntegral_Q80_polynomial_enclosure :
    ((centerQ 16 16 : ℝ) - (1 / 2 ^ 80 : ℝ)) ≤ originalFirstIntegral ∧
      originalFirstIntegral ≤ (centerQ 16 16 : ℝ) + (1 / 2 ^ 80 : ℝ) := by
  have h := originalFirstIntegral_polynomial_enclosure 16 16
  have hr : (radiusQ 16 16 : ℝ) ≤ (1 / 2 ^ 80 : ℝ) := by
    exact_mod_cast radiusQ_sixteen_le_Q80
  push_cast at h
  constructor <;> linarith [h.1, h.2]

end

end ImbalancedChen.P2FirstIntegralPolynomialEnclosureSourceOnly
