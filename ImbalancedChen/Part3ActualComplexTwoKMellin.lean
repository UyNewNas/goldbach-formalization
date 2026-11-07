import ImbalancedChen.Part3ComplexTwoKSchwingerProduct
import ImbalancedChen.Part3ActualImaginaryTwoKMellin
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Literal actual complex-order two-K Mellin integral on the complete strip
Re(s)>abs(Re(nu))+abs(Re(mu)). Genuine product absolute integrability,
Schwinger Fubini and Gamma-Beta evaluation are supplied by the new complex
modules. Only the real squared-coordinate Jacobian is reused from the
imaginary-order module. No integrability or Mellin formula is assumed.
-/

namespace ImbalancedChen.Part3.ActualComplexTwoKMellin20261025a
noncomputable section
open Set MeasureTheory Filter Complex
open ComplexOrderKBridgeSourceOnly
open ComplexTwoKSchwingerAbsolute20261025a ComplexTwoKSchwingerProduct20261025a
open ActualImaginaryTwoKMellin20261025a
  (squaredCoordinate squaredCoordinate_hasDerivAt squaredCoordinate_injOn squaredCoordinate_image)

def actualTwoKMellinDensity (nu mu s : ℂ) (q : ℝ) : ℂ :=
  (q : ℂ) ^ (s - 1) * complexOrderK nu q * complexOrderK mu q
theorem actualSchwingerProduct_at_squaredCoordinate (nu mu s : ℂ)
    {q : ℝ} (hq : 0 < q) :
    actualSchwingerProduct nu mu s (squaredCoordinate q) =
      4 * ((q / 2 : ℝ) : ℂ) ^ (s - 2) *
        complexOrderK (nu) q * complexOrderK (mu) q := by
  have hc : 0 < q / 2 := half_pos hq
  have hcC : ((q / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hx : squaredCoordinate q = (q / 2) * (q / 2) := by unfold squaredCoordinate; ring
  have hsqrt : Real.sqrt (squaredCoordinate q) = q / 2 := by
    rw [show squaredCoordinate q = (q / 2) ^ 2 by unfold squaredCoordinate; ring,
      Real.sqrt_sq_eq_abs, abs_of_pos hc]
  have harg : 2 * Real.sqrt (squaredCoordinate q) = q := by rw [hsqrt]; ring
  have hp : ((squaredCoordinate q : ℝ) : ℂ) ^ (mellinParameter nu mu s - 1) *
      ((q / 2 : ℝ) : ℂ) ^ (nu) *
      ((q / 2 : ℝ) : ℂ) ^ (mu) =
      ((q / 2 : ℝ) : ℂ) ^ (s - 2) := by
    rw [hx, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le hc.le,
      ← Complex.cpow_add _ _ hcC, ← Complex.cpow_add _ _ hcC,
      ← Complex.cpow_add _ _ hcC]
    congr 1
    unfold mellinParameter
    ring
  unfold actualSchwingerProduct
  rw [harg, hsqrt]
  calc
    _ = 4 *
        (((squaredCoordinate q : ℝ) : ℂ) ^ (mellinParameter nu mu s - 1) *
          ((q / 2 : ℝ) : ℂ) ^ (nu) *
          ((q / 2 : ℝ) : ℂ) ^ (mu)) *
        complexOrderK (nu) q * complexOrderK (mu) q := by ring
    _ = _ := by rw [hp]

/-- Exact Jacobian normalization. Multiplying by q/2 turns the squared
Mellin coordinate into 2^(3-s) times the literal q-Mellin density. -/
theorem actualSchwingerProduct_jacobian (nu mu s : ℂ) {q : ℝ} (hq : 0 < q) :
    |q / 2| • actualSchwingerProduct nu mu s (squaredCoordinate q) =
      (2 : ℂ) ^ (3 - s) * actualTwoKMellinDensity nu mu s q := by
  have hc : 0 < q / 2 := half_pos hq
  have hcC : ((q / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hcP : ((q / 2 : ℝ) : ℂ) * ((q / 2 : ℝ) : ℂ) ^ (s - 2) =
      ((q / 2 : ℝ) : ℂ) ^ (s - 1) := by
    rw [← Complex.cpow_one ((q / 2 : ℝ) : ℂ), ← Complex.cpow_add _ _ hcC]
    congr 1
    ring
  have hqsplit : (q : ℂ) ^ (s - 1) =
      (2 : ℂ) ^ (s - 1) * ((q / 2 : ℝ) : ℂ) ^ (s - 1) := by
    have he : q = 2 * (q / 2) := by ring
    conv_lhs => rw [he]
    rw [Complex.ofReal_mul]
    simpa only [Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc.le (s - 1)
  have htwo : (2 : ℂ) ^ (3 - s) * (2 : ℂ) ^ (s - 1) = 4 := by
    rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    have he : (3 : ℂ) - s + (s - 1) = 2 := by ring
    rw [he, Complex.cpow_two]
    norm_num
  rw [Complex.real_smul, abs_of_pos hc, actualSchwingerProduct_at_squaredCoordinate nu mu s hq]
  unfold actualTwoKMellinDensity
  rw [hqsplit]
  calc
    _ = 4 * (((q / 2 : ℝ) : ℂ) * ((q / 2 : ℝ) : ℂ) ^ (s - 2)) *
        complexOrderK (nu) q * complexOrderK (mu) q := by ring
    _ = 4 * ((q / 2 : ℝ) : ℂ) ^ (s - 1) *
        complexOrderK (nu) q * complexOrderK (mu) q := by rw [hcP]
    _ = _ := by rw [← htwo]; ring

theorem mellinScale_cancel (s : ℂ) :
    (2 : ℂ) ^ (s - 3) * (2 : ℂ) ^ (3 - s) = 1 := by
  rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
  have he : (s - 3) + (3 - s) = 0 := by ring
  rw [he, Complex.cpow_zero]

/-- Full absolute convergence of the literal product Mellin integral for
complex orders, throughout Re s > |Re nu| + |Re mu|. -/
theorem actualTwoKMellinDensity_integrable {nu mu s : ℂ} (hs : |nu.re| + |mu.re| < s.re) :
    IntegrableOn (actualTwoKMellinDensity nu mu s) (Ioi 0) := by
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi
    (fun q _ => (squaredCoordinate_hasDerivAt q).hasDerivWithinAt)
    squaredCoordinate_injOn (actualSchwingerProduct nu mu s)
  rw [squaredCoordinate_image] at hchange
  have h := (hchange.mp (actualSchwingerProduct_integrable hs)).const_mul
    ((2 : ℂ) ^ (s - 3))
  apply h.congr_fun _ measurableSet_Ioi
  intro q hq
  rw [actualSchwingerProduct_jacobian nu mu s hq,
    ← mul_assoc, mellinScale_cancel, one_mul]

theorem actualTwoKMellin_integral_eq_squared (nu mu s : ℂ) :
    (∫ q in Ioi (0 : ℝ), actualTwoKMellinDensity nu mu s q) =
      (2 : ℂ) ^ (s - 3) *
        ∫ x in Ioi (0 : ℝ), actualSchwingerProduct nu mu s x := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun q _ => (squaredCoordinate_hasDerivAt q).hasDerivWithinAt)
    squaredCoordinate_injOn (actualSchwingerProduct nu mu s)
  rw [squaredCoordinate_image] at hchange
  have he : (∫ x in Ioi (0 : ℝ), actualSchwingerProduct nu mu s x) =
      (2 : ℂ) ^ (3 - s) *
        ∫ q in Ioi (0 : ℝ), actualTwoKMellinDensity nu mu s q := by
    rw [hchange, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro q hq
    exact actualSchwingerProduct_jacobian nu mu s hq
  rw [he, ← mul_assoc, mellinScale_cancel, one_mul]

/-- The actual full-strip complex two-K Mellin product formula. Every factor
comes from a proved integral; no orthogonality or product formula is assumed. -/
theorem actual_complex_twoK_mellin {nu mu s : ℂ} (hs : |nu.re| + |mu.re| < s.re) :
    (∫ q in Ioi (0 : ℝ),
      (q : ℂ) ^ (s - 1) * complexOrderK (nu) q *
        complexOrderK (mu) q) =
      (2 : ℂ) ^ (s - 3) / Complex.Gamma s *
        Complex.Gamma ((s + nu + mu) / 2) *
        Complex.Gamma ((s + nu - mu) / 2) *
        Complex.Gamma ((s - nu + mu) / 2) *
        Complex.Gamma ((s - nu - mu) / 2) := by
  change (∫ q in Ioi (0 : ℝ), actualTwoKMellinDensity nu mu s q) = _
  rw [actualTwoKMellin_integral_eq_squared, actualSchwingerProduct_integral_four_gamma hs]
  have hA : gammaA nu mu s = (s + nu - mu) / 2 := by
    unfold gammaA mellinParameter
    ring
  have hB : gammaB nu mu s = (s - nu + mu) / 2 := by
    unfold gammaB mellinParameter
    ring
  have hD : gammaD nu mu s = (s + nu + mu) / 2 := by
    unfold gammaD mellinParameter
    ring
  rw [hA, hB, hD, mellinParameter]
  ring

end
end ImbalancedChen.Part3.ActualComplexTwoKMellin20261025a

