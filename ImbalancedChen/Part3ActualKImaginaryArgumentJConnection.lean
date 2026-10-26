import ImbalancedChen.Part3ActualIImaginaryArgumentJRotation
import ImbalancedChen.Part3ActualLogCoverKModel

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual imaginary-argument cut/log-cover K connection to ordinary J,
derived from the literal I-minus-I definition and the proved I rotations.
The principal upper/lower phases and pi/(2 sin(pi nu)) remain explicit.
The nu=2it formulas keep the exact 2*pi*t hyperbolic denominator.
These are values of the actual slit/cover continuation models; no
convergence of the right-half-plane Laplace integral on its boundary,
Weber formula, spectral measure, or new J normalization is asserted.
-/

namespace ImbalancedChen.Part3.ActualKImaginaryArgumentJConnection20261026b

noncomputable section
open Complex Set
open ActualGeneralJBesselSourceOnly ActualIImaginaryArgumentJRotation20261026b
open ActualCutPlaneKIModel20261026b ActualCutPlaneKOrderZeroRemovable20261026b
open ActualLogCoverKModel20261026b

theorem cutPlaneKWithZero_rotate_upper {nu : ℂ}
    (hs : Complex.sin ((Real.pi : ℂ) * nu) ≠ 0) {q : ℝ} (hq : 0 < q) :
    cutPlaneKWithZero nu (I * (q : ℂ)) =
      (Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu)) *
        (Complex.exp ((-I) * (Real.pi : ℂ) * nu / 2) * generalJ (-nu) q -
          Complex.exp (I * (Real.pi : ℂ) * nu / 2) * generalJ nu q) := by
  have hn : nu ≠ 0 := by intro h; apply hs; simp only [h, mul_zero, Complex.sin_zero]
  rw [cutPlaneKWithZero_of_ne_zero hn, cutPlaneKNonintegral,
    complexArgumentI_rotate_upper (-nu) hq, complexArgumentI_rotate_upper nu hq,
    show I * (Real.pi : ℂ) * (-nu) / 2 = (-I) * (Real.pi : ℂ) * nu / 2 by ring]

theorem cutPlaneKWithZero_rotate_lower {nu : ℂ}
    (hs : Complex.sin ((Real.pi : ℂ) * nu) ≠ 0) {q : ℝ} (hq : 0 < q) :
    cutPlaneKWithZero nu ((-I) * (q : ℂ)) =
      (Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu)) *
        (Complex.exp (I * (Real.pi : ℂ) * nu / 2) * generalJ (-nu) q -
          Complex.exp ((-I) * (Real.pi : ℂ) * nu / 2) * generalJ nu q) := by
  have hn : nu ≠ 0 := by intro h; apply hs; simp only [h, mul_zero, Complex.sin_zero]
  rw [cutPlaneKWithZero_of_ne_zero hn, cutPlaneKNonintegral,
    complexArgumentI_rotate_lower (-nu) hq, complexArgumentI_rotate_lower nu hq,
    show (-I) * (Real.pi : ℂ) * (-nu) / 2 = I * (Real.pi : ℂ) * nu / 2 by ring]

private theorem upper_phase_imaginary (t : ℝ) :
    Complex.exp (I * (Real.pi : ℂ) * (2 * I * (t : ℂ)) / 2) = (Real.exp (-Real.pi * t) : ℂ) := by
  have he : I * (Real.pi : ℂ) * (2 * I * (t : ℂ)) / 2 = ((-Real.pi * t : ℝ) : ℂ) := by
    calc
      _ = I ^ 2 * ((Real.pi : ℂ) * (t : ℂ)) := by ring
      _ = _ := by rw [Complex.I_sq]; push_cast; ring
  rw [he, ← Complex.ofReal_exp]

private theorem lower_phase_imaginary (t : ℝ) :
    Complex.exp ((-I) * (Real.pi : ℂ) * (2 * I * (t : ℂ)) / 2) = (Real.exp (Real.pi * t) : ℂ) := by
  have he : (-I) * (Real.pi : ℂ) * (2 * I * (t : ℂ)) / 2 = ((Real.pi * t : ℝ) : ℂ) := by
    calc
      _ = -(I ^ 2) * ((Real.pi : ℂ) * (t : ℂ)) := by ring
      _ = _ := by rw [Complex.I_sq]; push_cast; ring
  rw [he, ← Complex.ofReal_exp]

private theorem sine_imaginary_order (t : ℝ) :
    Complex.sin ((Real.pi : ℂ) * (2 * I * (t : ℂ))) = (Real.sinh (2 * Real.pi * t) : ℂ) * I := by
  have he : (Real.pi : ℂ) * (2 * I * (t : ℂ)) = ((2 * Real.pi * t : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [he, Complex.sin_mul_I, ← Complex.ofReal_sinh]

theorem cutPlaneKWithZero_imaginary_order_upper (t : ℝ) (ht : t ≠ 0)
    {q : ℝ} (hq : 0 < q) :
    cutPlaneKWithZero (2 * I * (t : ℂ)) (I * (q : ℂ)) =
      (Real.pi : ℂ) / (2 * (Real.sinh (2 * Real.pi * t) : ℂ) * I) *
        ((Real.exp (Real.pi * t) : ℂ) * generalJ (-(2 * I * (t : ℂ))) q -
          (Real.exp (-Real.pi * t) : ℂ) * generalJ (2 * I * (t : ℂ)) q) := by
  have him : (2 * I * (t : ℂ)).im ≠ 0 := by
    simpa using mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) ht
  have h := cutPlaneKWithZero_rotate_upper (sin_pi_order_ne_zero_of_imaginary him) hq
  rw [upper_phase_imaginary, lower_phase_imaginary, sine_imaginary_order] at h
  simpa only [mul_assoc] using h

theorem cutPlaneKWithZero_imaginary_order_lower (t : ℝ) (ht : t ≠ 0)
    {q : ℝ} (hq : 0 < q) :
    cutPlaneKWithZero (2 * I * (t : ℂ)) ((-I) * (q : ℂ)) =
      (Real.pi : ℂ) / (2 * (Real.sinh (2 * Real.pi * t) : ℂ) * I) *
        ((Real.exp (-Real.pi * t) : ℂ) * generalJ (-(2 * I * (t : ℂ))) q -
          (Real.exp (Real.pi * t) : ℂ) * generalJ (2 * I * (t : ℂ)) q) := by
  have him : (2 * I * (t : ℂ)).im ≠ 0 := by
    simpa using mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) ht
  have h := cutPlaneKWithZero_rotate_lower (sin_pi_order_ne_zero_of_imaginary him) hq
  rw [upper_phase_imaginary, lower_phase_imaginary, sine_imaginary_order] at h
  simpa only [mul_assoc] using h

/-- The cover coordinate is log(z/2), not log(z). -/
theorem logCoverK_rotate_upper {nu : ℂ}
    (hs : Complex.sin ((Real.pi : ℂ) * nu) ≠ 0) {q : ℝ} (hq : 0 < q) :
    logCoverK nu (Complex.log ((I * (q : ℂ)) / 2)) =
      (Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu)) *
        (Complex.exp ((-I) * (Real.pi : ℂ) * nu / 2) * generalJ (-nu) q -
          Complex.exp (I * (Real.pi : ℂ) * nu / 2) * generalJ nu q) := by
  rw [logCoverK_principal_half_log nu (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne'))]
  exact cutPlaneKWithZero_rotate_upper hs hq

theorem logCoverK_rotate_lower {nu : ℂ}
    (hs : Complex.sin ((Real.pi : ℂ) * nu) ≠ 0) {q : ℝ} (hq : 0 < q) :
    logCoverK nu (Complex.log (((-I) * (q : ℂ)) / 2)) =
      (Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu)) *
        (Complex.exp (I * (Real.pi : ℂ) * nu / 2) * generalJ (-nu) q -
          Complex.exp ((-I) * (Real.pi : ℂ) * nu / 2) * generalJ nu q) := by
  rw [logCoverK_principal_half_log nu
    (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr hq.ne'))]
  exact cutPlaneKWithZero_rotate_lower hs hq

end
end ImbalancedChen.Part3.ActualKImaginaryArgumentJConnection20261026b
