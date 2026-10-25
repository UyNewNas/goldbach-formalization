import ImbalancedChen.Part3GeneralIConjugation
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-!
# Actual real and imaginary I solutions in the logarithmic radial coordinate

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The functions are the real and imaginary parts of the actual I_{i*tau}
series at q=exp(r). Their actual second derivatives solve
  f''(r) = (exp(r)^2 - tau^2) * f(r).
Their real Wronskian is sinh(pi*tau)/pi and is nonzero for tau != 0.
Thus their value/derivative vectors form a nondegenerate actual real pair.
No completeness, KL measure, automorphic measure, or P3 saving is claimed.
The spectral parameter here is the actual order tau; comparison with the
previous K_{2it} convention requires tau=2*t explicitly.
-/

namespace ImbalancedChen.Part3.ImaginaryILogRadialBasis20261025a

noncomputable section
open Complex Filter Set Topology
open GeneralComplexISeriesSourceOnly GeneralIQODE20261025a
open GeneralISmallQWronskian20261025a GeneralIConjugation20261025a

def logI (nu : ℂ) (r : ℝ) : ℂ := generalI nu (Real.exp r)

def logIFirst (nu : ℂ) (r : ℝ) : ℂ :=
  (Real.exp r : ℂ) * deriv (generalI nu) (Real.exp r)

theorem logI_hasDerivAt {nu : ℂ} (hnu : -1 < nu.re) (r : ℝ) :
    HasDerivAt (logI nu) (logIFirst nu r) r := by
  simpa only [logI, logIFirst, Function.comp_def, Complex.real_smul] using
    (generalI_differentiableAt hnu (Real.exp_pos r)).hasDerivAt.scomp r
      (Real.hasDerivAt_exp r)

/-- The actual qODE supplies the second log-coordinate derivative. -/
theorem logIFirst_hasDerivAt {nu : ℂ} (hnu : -1 < nu.re) (r : ℝ) :
    HasDerivAt (logIFirst nu)
      (((Real.exp r : ℂ) ^ 2 + nu ^ 2) * logI nu r) r := by
  have he : HasDerivAt (fun x : ℝ => (Real.exp x : ℂ)) (Real.exp r : ℂ) r :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r (Real.hasDerivAt_exp r)
  have hprime : HasDerivAt (fun x : ℝ => deriv (generalI nu) (Real.exp x))
      ((Real.exp r : ℂ) * deriv (deriv (generalI nu)) (Real.exp r)) r := by
    simpa only [Function.comp_def, Complex.real_smul] using
      (generalI_deriv_differentiableAt hnu (Real.exp_pos r)).hasDerivAt.scomp r
        (Real.hasDerivAt_exp r)
  have h := he.mul hprime
  have hODE := generalI_modifiedBessel_equation hnu (Real.exp_pos r)
  have hvalue :
      (Real.exp r : ℂ) * deriv (generalI nu) (Real.exp r) +
        (Real.exp r : ℂ) * ((Real.exp r : ℂ) * deriv (deriv (generalI nu)) (Real.exp r)) =
          ((Real.exp r : ℂ) ^ 2 + nu ^ 2) * logI nu r := by
    unfold logI
    linear_combination hODE
  simpa only [logIFirst, hvalue] using h

def imaginaryLogIReal (tau r : ℝ) : ℝ := (logI ((tau : ℂ) * I) r).re
def imaginaryLogIImag (tau r : ℝ) : ℝ := (logI ((tau : ℂ) * I) r).im

theorem imaginaryLogIReal_hasDerivAt (tau r : ℝ) :
    HasDerivAt (imaginaryLogIReal tau) (logIFirst ((tau : ℂ) * I) r).re r := by
  have hnu : -1 < ((tau : ℂ) * I).re := by simp
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (logI_hasDerivAt hnu r)

theorem imaginaryLogIImag_hasDerivAt (tau r : ℝ) :
    HasDerivAt (imaginaryLogIImag tau) (logIFirst ((tau : ℂ) * I) r).im r := by
  have hnu : -1 < ((tau : ℂ) * I).re := by simp
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt r (logI_hasDerivAt hnu r)

private theorem imaginary_coefficient (tau r : ℝ) :
    (Real.exp r : ℂ) ^ 2 + ((tau : ℂ) * I) ^ 2 =
      (((Real.exp r) ^ 2 - tau ^ 2 : ℝ) : ℂ) := by
  push_cast
  rw [mul_pow, Complex.I_sq]
  ring

/-- The real part is an actual solution of the logarithmic radial ODE. -/
theorem imaginaryLogIReal_equation (tau r : ℝ) :
    deriv (deriv (imaginaryLogIReal tau)) r =
      ((Real.exp r) ^ 2 - tau ^ 2) * imaginaryLogIReal tau r := by
  have hnu : -1 < ((tau : ℂ) * I).re := by simp
  have hfirst : deriv (imaginaryLogIReal tau) =
      fun x : ℝ => (logIFirst ((tau : ℂ) * I) x).re :=
    funext fun x => (imaginaryLogIReal_hasDerivAt tau x).deriv
  have hsecond : HasDerivAt (fun x : ℝ => (logIFirst ((tau : ℂ) * I) x).re)
      (((Real.exp r) ^ 2 - tau ^ 2) * imaginaryLogIReal tau r) r := by
    simpa only [imaginary_coefficient, Complex.re_ofReal_mul, imaginaryLogIReal] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (logIFirst_hasDerivAt hnu r)
  rw [hfirst]
  exact hsecond.deriv

/-- The imaginary part solves the identical real radial equation. -/
theorem imaginaryLogIImag_equation (tau r : ℝ) :
    deriv (deriv (imaginaryLogIImag tau)) r =
      ((Real.exp r) ^ 2 - tau ^ 2) * imaginaryLogIImag tau r := by
  have hnu : -1 < ((tau : ℂ) * I).re := by simp
  have hfirst : deriv (imaginaryLogIImag tau) =
      fun x : ℝ => (logIFirst ((tau : ℂ) * I) x).im :=
    funext fun x => (imaginaryLogIImag_hasDerivAt tau x).deriv
  have hsecond : HasDerivAt (fun x : ℝ => (logIFirst ((tau : ℂ) * I) x).im)
      (((Real.exp r) ^ 2 - tau ^ 2) * imaginaryLogIImag tau r) r := by
    simpa only [imaginary_coefficient, Complex.im_ofReal_mul, imaginaryLogIImag] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt r (logIFirst_hasDerivAt hnu r)
  rw [hfirst]
  exact hsecond.deriv

/-- The actual I/conjugate-I Wronskian in log coordinates. -/
theorem logI_conjugate_wronskian (tau r : ℝ) :
    logI ((tau : ℂ) * I) r * conj (logIFirst ((tau : ℂ) * I) r) -
      logIFirst ((tau : ℂ) * I) r * conj (logI ((tau : ℂ) * I) r) =
        -2 * ((Real.sinh (Real.pi * tau) / Real.pi : ℝ) : ℂ) * I := by
  have hL : -1 < ((tau : ℂ) * I).re := by simp
  have hU : ((tau : ℂ) * I).re < 1 := by simp
  have hW := q_mul_generalIWronskian_eq_neg_two_sin hL hU (Real.exp_pos r)
  rw [generalIWronskian, generalI_neg_imaginary_eq_conj tau (Real.exp_pos r),
    deriv_generalI_neg_imaginary_eq_conj tau (Real.exp_pos r)] at hW
  have hsin : Complex.sin ((Real.pi : ℂ) * ((tau : ℂ) * I)) =
      (Real.sinh (Real.pi * tau) : ℂ) * I := by
    rw [← mul_assoc, ← Complex.ofReal_mul, Complex.sin_mul_I, ← Complex.ofReal_sinh]
  rw [hsin] at hW
  calc
    _ = (Real.exp r : ℂ) *
        (generalI ((tau : ℂ) * I) (Real.exp r) *
          conj (deriv (generalI ((tau : ℂ) * I)) (Real.exp r)) -
        deriv (generalI ((tau : ℂ) * I)) (Real.exp r) *
          conj (generalI ((tau : ℂ) * I) (Real.exp r))) := by
      simp only [logI, logIFirst, map_mul, Complex.conj_ofReal]
      ring
    _ = -2 * ((Real.sinh (Real.pi * tau) : ℂ) * I) / (Real.pi : ℂ) := hW
    _ = _ := by push_cast; ring

/-- Exact real Wronskian of the actual real/imaginary pair. -/
theorem imaginaryLogI_wronskian (tau r : ℝ) :
    imaginaryLogIReal tau r * deriv (imaginaryLogIImag tau) r -
      deriv (imaginaryLogIReal tau) r * imaginaryLogIImag tau r =
        Real.sinh (Real.pi * tau) / Real.pi := by
  have h := congrArg Complex.im (logI_conjugate_wronskian tau r)
  have hpair (z w : ℂ) :
      (z * conj w - w * conj z).im = -2 * (z.re * w.im - w.re * z.im) := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [hpair] at h
  simp at h
  rw [(imaginaryLogIReal_hasDerivAt tau r).deriv,
    (imaginaryLogIImag_hasDerivAt tau r).deriv]
  unfold imaginaryLogIReal imaginaryLogIImag
  linarith only [h]

theorem imaginaryLogI_wronskian_ne_zero {tau : ℝ} (htau : tau ≠ 0) (r : ℝ) :
    imaginaryLogIReal tau r * deriv (imaginaryLogIImag tau) r -
      deriv (imaginaryLogIReal tau) r * imaginaryLogIImag tau r ≠ 0 := by
  rw [imaginaryLogI_wronskian]
  exact div_ne_zero (Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero htau)) Real.pi_ne_zero

/-- At every radial point, value and derivative determine the two real
coefficients uniquely. This is concrete nondegeneracy of the actual pair. -/
theorem imaginaryLogI_initial_data_nondegenerate {tau : ℝ} (htau : tau ≠ 0)
    (r a b : ℝ)
    (hvalue : a * imaginaryLogIReal tau r + b * imaginaryLogIImag tau r = 0)
    (hderiv : a * deriv (imaginaryLogIReal tau) r + b * deriv (imaginaryLogIImag tau) r = 0) :
    a = 0 ∧ b = 0 := by
  have hW := imaginaryLogI_wronskian_ne_zero htau r
  have ha : a * (imaginaryLogIReal tau r * deriv (imaginaryLogIImag tau) r -
      deriv (imaginaryLogIReal tau) r * imaginaryLogIImag tau r) = 0 := by
    linear_combination deriv (imaginaryLogIImag tau) r * hvalue - imaginaryLogIImag tau r * hderiv
  have hb : b * (imaginaryLogIReal tau r * deriv (imaginaryLogIImag tau) r -
      deriv (imaginaryLogIReal tau) r * imaginaryLogIImag tau r) = 0 := by
    linear_combination imaginaryLogIReal tau r * hderiv - deriv (imaginaryLogIReal tau) r * hvalue
  exact ⟨(mul_eq_zero.mp ha).resolve_right hW, (mul_eq_zero.mp hb).resolve_right hW⟩

end
end ImbalancedChen.Part3.ImaginaryILogRadialBasis20261025a
