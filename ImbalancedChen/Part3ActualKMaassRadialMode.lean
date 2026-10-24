import ImbalancedChen.Part3ImaginaryOrderKSecondQDerivative
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED / no acceptance credit, 2026-10-24.
Only the ordinary chain and product rules are used here. The input is the
actual imaginary-order K integral, its two proved q derivatives, and its
actual modified-Bessel ODE. No spectral or quotient assertion occurs.
-/

namespace ImbalancedChen.Part3.ActualKMaassRadialMode20261024z

noncomputable section

open Set Filter
open scoped Topology
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKQDerivativeSourceOnly
open ImaginaryOrderKSecondQDerivativeSourceOnly

/-- The actual radial K mode, with order `2 i t` and positive frequency `a`. -/
def radialK (t a y : ℝ) : ℝ :=
  Real.sqrt y * imaginaryOrderK t (a * y)

/-- Product-rule formula for the first derivative on `y > 0`. -/
def radialKFirst (t a y : ℝ) : ℝ :=
  ((1 / 2 : ℝ) * y ^ (-(1 / 2 : ℝ))) * imaginaryOrderK t (a * y) +
    y ^ (1 / 2 : ℝ) * (a * qDerivative t (a * y))

/-- Product-rule formula for the second derivative on `y > 0`. -/
def radialKSecond (t a y : ℝ) : ℝ :=
  (-(1 / 4 : ℝ) * y ^ (-(3 / 2 : ℝ))) * imaginaryOrderK t (a * y) +
    (a * y ^ (-(1 / 2 : ℝ))) * qDerivative t (a * y) +
      (y ^ (1 / 2 : ℝ) * a ^ 2) * qSecond t (a * y)

private theorem linear_hasDerivAt (a y : ℝ) :
    HasDerivAt (fun r : ℝ => a * r) a y := by
  simpa only [mul_one] using (hasDerivAt_id y).const_mul a

private theorem composedK_hasDerivAt (t a : ℝ) {y : ℝ}
    (ha : 0 < a) (hy : 0 < y) :
    HasDerivAt (fun r => imaginaryOrderK t (a * r))
      (a * qDerivative t (a * y)) y := by
  have hq : 0 < a * y := mul_pos ha hy
  convert (imaginaryOrderK_hasDerivAt_q_integral t hq).comp y
    (linear_hasDerivAt a y) using 1 <;> simp [Function.comp_def, mul_comm]

private theorem composedQDerivative_hasDerivAt (t a : ℝ) {y : ℝ}
    (ha : 0 < a) (hy : 0 < y) :
    HasDerivAt (fun r => a * qDerivative t (a * r))
      (a ^ 2 * qSecond t (a * y)) y := by
  have hq : 0 < a * y := mul_pos ha hy
  have h := (qDerivative_hasDerivAt_qSecond t hq).comp y
    (linear_hasDerivAt a y)
  convert h.const_mul a using 1 <;> simp [Function.comp_def] <;> ring

/-- The actual first radial derivative, including the square-root factor. -/
theorem radialK_hasDerivAt (t a : ℝ) {y : ℝ}
    (ha : 0 < a) (hy : 0 < y) :
    HasDerivAt (radialK t a) (radialKFirst t a y) y := by
  have hp : HasDerivAt (fun r : ℝ => r ^ (1 / 2 : ℝ))
      ((1 / 2 : ℝ) * y ^ (-(1 / 2 : ℝ))) y := by
    convert Real.hasDerivAt_rpow_const (x := y) (p := (1 / 2 : ℝ))
      (Or.inl hy.ne') using 1 <;> norm_num
  have h := hp.mul (composedK_hasDerivAt t a ha hy)
  simpa only [radialK, radialKFirst, Real.sqrt_eq_rpow] using h

private theorem radialKFirst_hasDerivAt (t a : ℝ) {y : ℝ}
    (ha : 0 < a) (hy : 0 < y) :
    HasDerivAt (radialKFirst t a) (radialKSecond t a y) y := by
  have hA : HasDerivAt
      (fun r : ℝ => (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ)))
      (-(1 / 4 : ℝ) * y ^ (-(3 / 2 : ℝ))) y := by
    convert (Real.hasDerivAt_rpow_const (x := y) (p := (-(1 / 2 : ℝ)))
      (Or.inl hy.ne')).const_mul (1 / 2 : ℝ) using 1 <;> norm_num
  have hB : HasDerivAt (fun r : ℝ => r ^ (1 / 2 : ℝ))
      ((1 / 2 : ℝ) * y ^ (-(1 / 2 : ℝ))) y := by
    convert Real.hasDerivAt_rpow_const (x := y) (p := (1 / 2 : ℝ))
      (Or.inl hy.ne') using 1 <;> norm_num
  have h := (hA.mul (composedK_hasDerivAt t a ha hy)).add
    (hB.mul (composedQDerivative_hasDerivAt t a ha hy))
  convert h using 1
  · funext r
    simp only [radialKFirst]
  · simp only [radialKSecond]
    ring

theorem radialK_deriv (t a : ℝ) {y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    deriv (radialK t a) y = radialKFirst t a y :=
  (radialK_hasDerivAt t a ha hy).deriv

/-- The second ordinary derivative is the chain/product-rule expression. -/
theorem radialK_second_deriv (t a : ℝ) {y : ℝ}
    (ha : 0 < a) (hy : 0 < y) :
    deriv (deriv (radialK t a)) y = radialKSecond t a y := by
  have h := radialKFirst_hasDerivAt t a ha hy
  have hevent : (fun r => deriv (radialK t a) r) =ᶠ[𝓝 y] radialKFirst t a := by
    filter_upwards [Ioi_mem_nhds hy] with r hr
    exact radialK_deriv t a ha hr
  exact (h.congr_of_eventuallyEq hevent.symm).deriv

/-- The actual K ODE becomes the weight-zero Maass radial eigen-equation.
The sign is fixed by the imaginary order `2 i t`: eigenvalue `1/4+4t²`. -/
theorem radialK_eigen_equation (t a : ℝ) {y : ℝ}
    (ha : 0 < a) (hy : 0 < y) :
    -(y ^ 2) *
      (deriv (deriv (radialK t a)) y - a ^ 2 * radialK t a y) =
        ((1 / 4 : ℝ) + 4 * t ^ 2) * radialK t a y := by
  have hq : 0 < a * y := mul_pos ha hy
  have hODE := actual_K_modifiedBessel_equation t hq
  rw [(deriv_imaginaryOrderK_hasDerivAt_qSecond t hq).deriv,
    (imaginaryOrderK_hasDerivAt_q_integral t hq).deriv] at hODE
  let s : ℝ := y ^ (1 / 2 : ℝ)
  have hspos : 0 < s := Real.rpow_pos_of_pos hy _
  have hs : s ≠ 0 := hspos.ne'
  have hs2 : s ^ 2 = y := by
    dsimp [s]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
    norm_num
  have hneg1 : y ^ (-(1 / 2 : ℝ)) = s⁻¹ := by
    dsimp [s]
    rw [Real.rpow_neg hy.le]
  have hpow3 : y ^ (3 / 2 : ℝ) = s ^ 3 := by
    dsimp [s]
    rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) * 3 by ring,
      Real.rpow_mul hy.le, Real.rpow_natCast]
  have hneg3 : y ^ (-(3 / 2 : ℝ)) = (s ^ 3)⁻¹ := by
    rw [Real.rpow_neg hy.le, hpow3]
  have hODEs : s *
      ((a * y) ^ 2 * qSecond t (a * y) +
        (a * y) * qDerivative t (a * y) -
        ((a * y) ^ 2 - 4 * t ^ 2) * imaginaryOrderK t (a * y)) = 0 := by
    rw [hODE, mul_zero]
  rw [radialK_second_deriv t a ha hy]
  simp only [radialK, radialKSecond, Real.sqrt_eq_rpow]
  change -(y ^ 2) *
      ((-(1 / 4 : ℝ) * y ^ (-(3 / 2 : ℝ))) * imaginaryOrderK t (a * y) +
        (a * y ^ (-(1 / 2 : ℝ))) * qDerivative t (a * y) +
        (y ^ (1 / 2 : ℝ) * a ^ 2) * qSecond t (a * y) -
          a ^ 2 * (s * imaginaryOrderK t (a * y))) =
      ((1 / 4 : ℝ) + 4 * t ^ 2) *
        (s * imaginaryOrderK t (a * y))
  rw [hneg1, hneg3]
  rw [← hs2] at hODEs ⊢
  have hODEscaled : -(s ^ 3) *
      (s * ((a * s ^ 2) ^ 2 * qSecond t (a * s ^ 2) +
        (a * s ^ 2) * qDerivative t (a * s ^ 2) -
        ((a * s ^ 2) ^ 2 - 4 * t ^ 2) *
          imaginaryOrderK t (a * s ^ 2))) = 0 := by
    rw [hODEs, mul_zero]
  field_simp [hs]
  nlinarith [hODEscaled]

/-- The classical nonzero Fourier frequency `a = 2π|n|`. -/
def maassFrequency (n : ℤ) : ℝ := 2 * Real.pi * |(n : ℝ)|

theorem maassFrequency_pos {n : ℤ} (hn : n ≠ 0) :
    0 < maassFrequency n := by
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  unfold maassFrequency
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (abs_pos.mpr hnreal)

/-- Specialized nonzero Fourier-mode radial equation, with exact `2π|n|`. -/
theorem maassFrequency_radial_eigen_equation (t : ℝ) {n : ℤ} (hn : n ≠ 0)
    {y : ℝ} (hy : 0 < y) :
    -(y ^ 2) *
      (deriv (deriv (radialK t (maassFrequency n))) y -
        maassFrequency n ^ 2 * radialK t (maassFrequency n) y) =
      ((1 / 4 : ℝ) + 4 * t ^ 2) * radialK t (maassFrequency n) y :=
  radialK_eigen_equation t (maassFrequency n) (maassFrequency_pos hn) hy

end
end ImbalancedChen.Part3.ActualKMaassRadialMode20261024z
