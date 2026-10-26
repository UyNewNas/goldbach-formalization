import ImbalancedChen.Part3ActualKUnequalPositiveShear
import ImbalancedChen.Part3ComplexOrderKShiftDerivative
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

The positive double-integral shear is evaluated for opposite orders.
At fixed r>0 its two damping coefficients are A=x+y*r, B=x+y/r.
The actual positive scaling t=(sqrt(A*B)/A)*w has A*t+B/t
equal to sqrt(A*B)*(w+1/w), and its Jacobian cancels dt/t.
This yields an actual K_0 distance product formula with independently
positive x and y. Absolute convergence is inherited from the jointly
integrable sheared actual Laplace product, not assumed for the K_0 kernel.

The different Macdonald transform DLMF 10.32.18 remains OPEN, including
its printed complex-argument domain. No Weber or product identity is an
input. The stopped unfrozen unequal-product draft is not a supplier.
-/

namespace ImbalancedChen.Part3.ActualKUnequalKZeroRatio20261026b

noncomputable section
open Set MeasureTheory Filter
open ComplexOrderKBridgeSourceOnly ComplexOrderKPositiveLaplace20261025a
open ActualKUnequalPositiveShear20261026b
open ComplexOrderKShiftDerivativeSourceOnly (actual_K_even_order)

def forwardRadial (x y r : ℝ) : ℝ := x + y * r
def backwardRadial (x y r : ℝ) : ℝ := x + y / r
def radialDistance (x y r : ℝ) : ℝ :=
  Real.sqrt (forwardRadial x y r * backwardRadial x y r)
def radialScale (x y r : ℝ) : ℝ := radialDistance x y r / forwardRadial x y r

theorem forwardRadial_pos {x y r : ℝ} (hx : 0 < x) (hy : 0 < y) (hr : 0 < r) :
    0 < forwardRadial x y r := add_pos hx (mul_pos hy hr)

theorem backwardRadial_pos {x y r : ℝ} (hx : 0 < x) (hy : 0 < y) (hr : 0 < r) :
    0 < backwardRadial x y r := add_pos hx (div_pos hy hr)

theorem radialDistance_pos {x y r : ℝ} (hx : 0 < x) (hy : 0 < y) (hr : 0 < r) :
    0 < radialDistance x y r :=
  Real.sqrt_pos.mpr (mul_pos (forwardRadial_pos hx hy hr) (backwardRadial_pos hx hy hr))

theorem radialDistance_sq {x y r : ℝ} (hx : 0 < x) (hy : 0 < y) (hr : 0 < r) :
    radialDistance x y r ^ 2 = forwardRadial x y r * backwardRadial x y r :=
  Real.sq_sqrt (mul_pos (forwardRadial_pos hx hy hr) (backwardRadial_pos hx hy hr)).le

theorem radialScale_pos {x y r : ℝ} (hx : 0 < x) (hy : 0 < y) (hr : 0 < r) :
    0 < radialScale x y r := div_pos (radialDistance_pos hx hy hr) (forwardRadial_pos hx hy hr)

theorem radialScale_forward {x y r : ℝ} (hx : 0 < x) (hy : 0 < y) (hr : 0 < r) :
    forwardRadial x y r * radialScale x y r = radialDistance x y r := by
  unfold radialScale
  field_simp [(forwardRadial_pos hx hy hr).ne'] <;> ring

theorem radialScale_backward {x y r : ℝ} (hx : 0 < x) (hy : 0 < y) (hr : 0 < r) :
    backwardRadial x y r * (radialScale x y r)⁻¹ = radialDistance x y r := by
  have ha := (forwardRadial_pos hx hy hr).ne'
  have hd := (radialDistance_pos hx hy hr).ne'
  have hs := radialDistance_sq hx hy hr
  unfold radialScale
  field_simp [ha, hd] <;> nlinarith [hs]

/-- The displayed argument is the real positive square-root distance. -/
theorem radialDistance_eq_sqrt (x y : ℝ) {r : ℝ} (hr : 0 < r) :
    radialDistance x y r = Real.sqrt (x ^ 2 + y ^ 2 + x * y * (r + r⁻¹)) := by
  unfold radialDistance forwardRadial backwardRadial
  congr 1
  field_simp [hr.ne'] <;> ring

private theorem damping_coefficients (x y : ℝ) {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    x * (t + t⁻¹) + y * (t * r + (t * r)⁻¹) =
      forwardRadial x y r * t + backwardRadial x y r * t⁻¹ := by
  unfold forwardRadial backwardRadial
  field_simp [ht.ne', hr.ne'] <;> ring

/-- The genuine nonlinear positive fiber scaling, with both unequal
coefficients retained. It is an equality of real damping exponents. -/
theorem damping_scaled {x y r w : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hr : 0 < r) (hw : 0 < w) :
    -(x / 2) * (radialScale x y r * w + (radialScale x y r * w)⁻¹) +
      (-(y / 2) * (radialScale x y r * w * r +
        (radialScale x y r * w * r)⁻¹)) =
      -(radialDistance x y r / 2) * (w + w⁻¹) := by
  have hs := radialScale_pos hx hy hr
  have hdamp := damping_coefficients x y (mul_pos hs hw) hr
  have hlinear : forwardRadial x y r * (radialScale x y r * w) +
      backwardRadial x y r * (radialScale x y r * w)⁻¹ =
        radialDistance x y r * (w + w⁻¹) := by
    rw [mul_inv_rev]
    calc
      _ = (forwardRadial x y r * radialScale x y r) * w +
          (backwardRadial x y r * (radialScale x y r)⁻¹) * w⁻¹ := by ring
      _ = _ := by rw [radialScale_forward hx hy hr, radialScale_backward hx hy hr]; ring
  rw [hlinear] at hdamp
  linear_combination (-1 / 2 : ℝ) * hdamp

private theorem opposite_power_cancellation (nu : ℂ) {t r : ℝ}
    (ht : 0 < t) (hr : 0 < r) :
    (t : ℂ) * (t : ℂ) ^ (nu - 1) * ((t * r : ℝ) : ℂ) ^ (-nu - 1) =
      (r : ℂ) ^ (-nu - 1) * (t : ℂ)⁻¹ := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hsum : (nu - 1) + (-nu - 1) = (-2 : ℂ) := by ring
  have hpair : (t : ℂ) ^ (nu - 1) * (t : ℂ) ^ (-nu - 1) = (t : ℂ) ^ (-2 : ℂ) := by
    rw [← Complex.cpow_add _ _ htC, hsum]
  have hlast : (t : ℂ) * (t : ℂ) ^ (-2 : ℂ) = (t : ℂ)⁻¹ := by
    calc
      _ = (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-2 : ℂ) := by rw [Complex.cpow_one]
      _ = (t : ℂ) ^ ((1 : ℂ) + (-2 : ℂ)) := (Complex.cpow_add _ _ htC).symm
      _ = _ := by norm_num [Complex.cpow_neg_one]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ht.le hr.le]
  calc
    _ = (r : ℂ) ^ (-nu - 1) *
        ((t : ℂ) * ((t : ℂ) ^ (nu - 1) * (t : ℂ) ^ (-nu - 1))) := by ring
    _ = _ := by rw [hpair, hlast]

/-- The exact scaled integrand, including its positive real Jacobian. -/
theorem opposite_shear_scaled (nu : ℂ) {x y r w : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hr : 0 < r) (hw : 0 < w) :
    (radialScale x y r : ℂ) *
        shearDensity nu (-nu) x y (radialScale x y r * w) r =
      (r : ℂ) ^ (-nu - 1) * laplaceDensity 0 (radialDistance x y r) w := by
  have hs := radialScale_pos hx hy hr
  have hpow := opposite_power_cancellation nu (mul_pos hs hw) hr
  have hcancel : (radialScale x y r : ℂ) *
      ((radialScale x y r * w : ℝ) : ℂ)⁻¹ = (w : ℂ)⁻¹ := by
    rw [Complex.ofReal_mul]
    field_simp [Complex.ofReal_ne_zero.mpr hs.ne', Complex.ofReal_ne_zero.mpr hw.ne'] <;> ring
  have hexp : (Real.exp (-(x / 2) * (radialScale x y r * w +
      (radialScale x y r * w)⁻¹)) : ℂ) *
      (Real.exp (-(y / 2) * (radialScale x y r * w * r +
        (radialScale x y r * w * r)⁻¹)) : ℂ) =
      (Real.exp (-(radialDistance x y r / 2) * (w + w⁻¹)) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, damping_scaled hx hy hr hw]
  unfold shearDensity laplaceDensity
  simp only [zero_sub, Complex.cpow_neg_one]
  calc
    _ = (((radialScale x y r * w : ℝ) : ℂ) *
          ((radialScale x y r * w : ℝ) : ℂ) ^ (nu - 1) *
          ((radialScale x y r * w * r : ℝ) : ℂ) ^ (-nu - 1)) *
        (radialScale x y r : ℂ) *
        ((Real.exp (-(x / 2) * (radialScale x y r * w +
            (radialScale x y r * w)⁻¹)) : ℂ) *
          (Real.exp (-(y / 2) * (radialScale x y r * w * r +
            (radialScale x y r * w * r)⁻¹)) : ℂ)) := by ring
    _ = (r : ℂ) ^ (-nu - 1) *
        ((radialScale x y r : ℂ) * ((radialScale x y r * w : ℝ) : ℂ)⁻¹) *
        (Real.exp (-(radialDistance x y r / 2) * (w + w⁻¹)) : ℂ) := by
      rw [hpow, hexp]
      ring
    _ = _ := by rw [hcancel]

/-- The surviving positive K_0 ratio kernel. -/
def ratioKernel (nu : ℂ) (x y r : ℝ) : ℂ :=
  (r : ℂ) ^ (-nu - 1) * complexOrderK 0 (radialDistance x y r)

/-- The radial fiber is a literal K_0 Schlaefli integral after a real
positive scaling, not a complex contour change. -/
theorem opposite_shear_fiber (nu : ℂ) {x y r : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hr : 0 < r) :
    (∫ t in Ioi (0 : ℝ), shearDensity nu (-nu) x y t r) =
      2 * ratioKernel nu x y r := by
  have hscale := integral_comp_mul_left_Ioi'
    (fun t => shearDensity nu (-nu) x y t r) 0 (radialScale_pos hx hy hr)
  rw [mul_zero, Complex.real_smul] at hscale
  rw [← hscale, ← integral_const_mul]
  have hpoint : (∫ w in Ioi (0 : ℝ), (radialScale x y r : ℂ) *
      shearDensity nu (-nu) x y (radialScale x y r * w) r) =
        ∫ w in Ioi (0 : ℝ), (r : ℂ) ^ (-nu - 1) *
          laplaceDensity 0 (radialDistance x y r) w := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro w hw
    exact opposite_shear_scaled nu hx hy hr hw
  rw [hpoint, integral_const_mul, laplaceDensity_integral 0 (radialDistance_pos hx hy hr)]
  unfold ratioKernel
  ring

/-- Actual absolute convergence of the unequal-argument K_0 kernel. -/
theorem ratioKernel_integrable (nu : ℂ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Integrable (ratioKernel nu x y) positiveMeasure := by
  have h := (shearDensity_integrable nu (-nu) hx hy).integral_prod_right
  apply (h.const_mul (1 / 2 : ℂ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [opposite_shear_fiber nu hx hy hr]
  ring

/-- An actual unequal-argument single-integral product theorem. The
arguments vary independently and the complex order is unrestricted. -/
theorem actual_K_unequal_KZero_ratio (nu : ℂ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    complexOrderK nu x * complexOrderK nu y =
      (1 / 2 : ℂ) * ∫ r in Ioi (0 : ℝ),
        (r : ℂ) ^ (-nu - 1) *
          complexOrderK 0 (Real.sqrt (x ^ 2 + y ^ 2 + x * y * (r + r⁻¹))) := by
  have hproduct := actual_K_unequal_positive_double_integral nu (-nu) hx hy
  rw [actual_K_even_order] at hproduct
  have hpoint : (∫ r in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ),
      shearDensity nu (-nu) x y t r) =
        2 * ∫ r in Ioi (0 : ℝ), ratioKernel nu x y r := by
    calc
      _ = ∫ r in Ioi (0 : ℝ), 2 * ratioKernel nu x y r := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        exact opposite_shear_fiber nu hx hy hr
      _ = _ := integral_const_mul _ _
  rw [hpoint] at hproduct
  calc
    _ = (1 / 2 : ℂ) * ∫ r in Ioi (0 : ℝ), ratioKernel nu x y r := by
      rw [hproduct]
      ring
    _ = _ := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      simp only [ratioKernel, radialDistance_eq_sqrt x y hr]

end
end ImbalancedChen.Part3.ActualKUnequalKZeroRatio20261026b
