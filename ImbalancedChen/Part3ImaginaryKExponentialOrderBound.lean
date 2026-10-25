import ImbalancedChen.Part3ImaginaryKContourRectangle
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# Exponential imaginary-order bound for the actual K integral

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The actual finite Cauchy rectangles and proved vertical-edge limits give
the whole-line shift. Absolute integrability follows from the actual
zero-order cosh-Laplace density. The shifted horizontal norm retains the
factor exp(-tau*height); choosing the sign of the height gives
  norm K_(i*tau)(q) <= exp(-theta*abs(tau)) K_0(q*cos(theta)).
The actual whole-line density equals twice the actual K integral by the
already proved positive-Laplace representation. No contour formula or
distribution estimate is assumed. Canonical KL measure and P3 remain OPEN.
-/

namespace ImbalancedChen.Part3.ImaginaryKExponentialOrderBound20261025a

noncomputable section
open Complex Set MeasureTheory Filter Topology
open ImaginaryKContourRectangle20261025a
open ComplexOrderKBridgeSourceOnly ComplexOrderKPositiveLaplace20261025a
open RealOrderKExceptionalSourceOnly ImaginaryOrderKBesselSourceOnly

/-- Exact shifted modulus, with its order saving outside the density. -/
theorem norm_horizontal_eq_zero_order_density (q tau height x : ℝ) :
    ‖horizontal q tau height x‖ = Real.exp (-tau * height) *
      RealOrderKPositiveLaplace.tiltedCoshDensity 0 (q * Real.cos height) x := by
  rw [norm_horizontal, RealOrderKPositiveLaplace.tiltedCoshDensity, ← Real.exp_add]
  congr 1
  ring

theorem horizontal_integrable {q : ℝ} (hq : 0 < q) (tau height : ℝ)
    (hheight : |height| < Real.pi / 2) : Integrable (horizontal q tau height) := by
  have hc : 0 < Real.cos height := Real.cos_pos_of_mem_Ioo (abs_lt.mp hheight)
  have hmajor := (RealOrderKPositiveLaplace.tiltedCoshDensity_integrable 0
    (mul_pos hq hc)).const_mul (Real.exp (-tau * height))
  have hcont : Continuous (horizontal q tau height) := by
    unfold horizontal contourKernel
    fun_prop
  apply hmajor.mono' hcont.aestronglyMeasurable
  exact Eventually.of_forall fun x => (norm_horizontal_eq_zero_order_density q tau height x).le

/-- The whole-line contour shift follows from the actual finite rectangle
and both vanishing vertical edges, with no shift-identity premise. -/
theorem horizontal_integral_eq_shift {q : ℝ} (hq : 0 < q) (tau height : ℝ)
    (hheight : |height| < Real.pi / 2) :
    (∫ x : ℝ, horizontal q tau 0 x) = ∫ x : ℝ, horizontal q tau height x := by
  have hbase := horizontal_integrable hq tau 0 (by simpa using half_pos Real.pi_pos)
  have hshift := horizontal_integrable hq tau height hheight
  have h0 := intervalIntegral_tendsto_integral hbase tendsto_neg_atTop_atBot tendsto_id
  have hh := intervalIntegral_tendsto_integral hshift tendsto_neg_atTop_atBot tendsto_id
  have hr := (tendsto_right_verticalEdge_zero hq tau height hheight).const_mul I
  have hl := (tendsto_left_verticalEdge_zero hq tau height hheight).const_mul I
  have hlim := ((h0.sub hh).add hr).sub hl
  have hz : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop
      (𝓝 ((∫ x : ℝ, horizontal q tau 0 x) - ∫ x : ℝ, horizontal q tau height x)) := by
    simpa only [finite_rectangle_identity, mul_zero, add_zero, sub_zero] using hlim
  exact sub_eq_zero.mp (tendsto_nhds_unique hz tendsto_const_nhds)

/-- The unshifted whole-line kernel is the actual K integral, including
the factor two from combining the two half-lines. -/
theorem horizontal_zero_integral {q : ℝ} (hq : 0 < q) (tau : ℝ) :
    (∫ x : ℝ, horizontal q tau 0 x) = 2 * complexOrderK ((tau : ℂ) * I) q := by
  have heq : horizontal q tau 0 = tiltedDensity ((tau : ℂ) * I) q := by
    funext x
    simp only [horizontal, contourKernel, tiltedDensity, Complex.ofReal_zero,
      zero_mul, add_zero, ← Complex.ofReal_cosh, Complex.ofReal_mul, Complex.ofReal_neg]
  rw [heq]
  exact tiltedDensity_integral ((tau : ℂ) * I) hq

theorem norm_shifted_horizontal_integral_le {q : ℝ} (hq : 0 < q) (tau height : ℝ)
    (hheight : |height| < Real.pi / 2) :
    ‖∫ x : ℝ, horizontal q tau height x‖ ≤
      Real.exp (-tau * height) * (2 * realOrderK 0 (q * Real.cos height)) := by
  have hc : 0 < Real.cos height := Real.cos_pos_of_mem_Ioo (abs_lt.mp hheight)
  calc
    _ ≤ ∫ x : ℝ, ‖horizontal q tau height x‖ := norm_integral_le_integral_norm _
    _ = _ := by
      simp_rw [norm_horizontal_eq_zero_order_density]
      rw [integral_const_mul,
        RealOrderKPositiveLaplace.tiltedCoshDensity_integral 0 (mul_pos hq hc)]

/-- A signed contour height gives its exact exponential order factor. -/
theorem complexOrderK_imaginary_norm_le_shift {q : ℝ} (hq : 0 < q) (tau height : ℝ)
    (hheight : |height| < Real.pi / 2) :
    ‖complexOrderK ((tau : ℂ) * I) q‖ ≤
      Real.exp (-tau * height) * realOrderK 0 (q * Real.cos height) := by
  have hbound := norm_shifted_horizontal_integral_le hq tau height hheight
  rw [← horizontal_integral_eq_shift hq tau height hheight,
    horizontal_zero_integral hq tau, norm_mul] at hbound
  norm_num only [Complex.norm_ofNat] at hbound
  nlinarith only [hbound]

/-- The desired genuine exponential imaginary-order estimate. The contour
is shifted in the sign of tau, so no exponential saving is discarded. -/
theorem complexOrderK_imaginary_norm_le_exp_abs {q theta : ℝ}
    (hq : 0 < q) (htheta : 0 < theta) (hthetaPi : theta < Real.pi / 2) (tau : ℝ) :
    ‖complexOrderK ((tau : ℂ) * I) q‖ ≤
      Real.exp (-theta * |tau|) * realOrderK 0 (q * Real.cos theta) := by
  by_cases htau : 0 ≤ tau
  · have hh : |theta| < Real.pi / 2 := by simpa only [abs_of_pos htheta] using hthetaPi
    have he : -tau * theta = -theta * |tau| := by rw [abs_of_nonneg htau]; ring
    simpa only [he] using complexOrderK_imaginary_norm_le_shift hq tau theta hh
  · have htauNeg : tau < 0 := lt_of_not_ge htau
    have hh : |-theta| < Real.pi / 2 := by
      simpa only [abs_neg, abs_of_pos htheta] using hthetaPi
    have he : -tau * (-theta) = -theta * |tau| := by rw [abs_of_neg htauNeg]; ring
    simpa only [Real.cos_neg, he] using complexOrderK_imaginary_norm_le_shift hq tau (-theta) hh

/-- Literal original K_(2*i*t) version: the saving is exp(-2*theta*abs(t)). -/
theorem imaginaryOrderK_abs_le_exp_two_abs {q theta : ℝ}
    (hq : 0 < q) (htheta : 0 < theta) (hthetaPi : theta < Real.pi / 2) (t : ℝ) :
    |imaginaryOrderK t q| ≤
      Real.exp (-(2 * theta) * |t|) * realOrderK 0 (q * Real.cos theta) := by
  have h := complexOrderK_imaginary_norm_le_exp_abs hq htheta hthetaPi (2 * t)
  rw [complexOrderK_imaginary, Complex.norm_real, Real.norm_eq_abs] at h
  have he : -theta * |2 * t| = -(2 * theta) * |t| := by
    rw [abs_mul]
    norm_num
    ring
  simpa only [he] using h

end
end ImbalancedChen.Part3.ImaginaryKExponentialOrderBound20261025a
