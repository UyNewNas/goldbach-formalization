import ImbalancedChen.Part3ActualJComplexArgumentODE
import ImbalancedChen.Part3GeneralIQODE

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Native complex J jets on both imaginary axes, with the actual principal
branch phases. The existing literal rotations are differentiated on the
positive q-axis and compared with the newly proved complex jets. The
first-derivative factors are -i on the upper axis and +i on the lower;
both second-derivative factors are -1. No rotation of derivatives or
special-function identification is assumed.
-/

namespace ImbalancedChen.Part3.ActualJComplexJetRotations20261026b

noncomputable section
open Complex Set Filter
open scoped Topology
open GeneralComplexISeriesSourceOnly GeneralIQODE20261025a
open ActualGeneralJComplexArgument20261025a ActualJComplexArgumentJets20261026b

private theorem upper_mem_slit {q : ℝ} (hq : 0 < q) :
    I * (q : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  simpa using hq.ne'

private theorem lower_mem_slit {q : ℝ} (hq : 0 < q) :
    (-I) * (q : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  simpa using (neg_ne_zero.mpr hq.ne')

private theorem solve_mul_I {x y : ℂ} (h : x * I = y) : x = (-I) * y := by
  have he := congrArg (fun w : ℂ => w * (-I)) h
  have hi : I * (-I) = 1 := by rw [mul_neg, Complex.I_sq]; ring
  rw [mul_assoc, hi, mul_one] at he
  exact he.trans (mul_comm _ _)

private theorem solve_mul_neg_I {x y : ℂ} (h : x * (-I) = y) : x = I * y := by
  have he := congrArg (fun w : ℂ => w * I) h
  have hi : (-I) * I = 1 := by rw [neg_mul, Complex.I_sq]; ring
  rw [mul_assoc, hi, mul_one] at he
  exact he.trans (mul_comm _ _)

theorem generalJComplexFirst_rotate_upper {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) :
    generalJComplexFirst nu (I * (q : ℂ)) =
      (-I) * Complex.exp (I * (Real.pi : ℂ) * nu / 2) * generalIFirst nu q := by
  have hrot : HasDerivAt (fun x : ℝ => generalJComplex nu (I * (x : ℂ)))
      (generalJComplexFirst nu (I * (q : ℂ)) * I) q := by
    simpa only [mul_one] using
      (((generalJComplex_hasDerivAt hnu (upper_mem_slit hq)).comp (q : ℂ)
        ((hasDerivAt_id (q : ℂ)).const_mul I)).comp_ofReal)
  have hright := (generalI_hasDerivAt hnu hq).const_mul
    (Complex.exp (I * (Real.pi : ℂ) * nu / 2))
  have hsame : HasDerivAt (fun x : ℝ => generalJComplex nu (I * (x : ℂ)))
      (Complex.exp (I * (Real.pi : ℂ) * nu / 2) * generalIFirst nu q) q := by
    apply hright.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hq] with x hx
    exact generalJComplex_rotate_upper nu hx
  simpa only [mul_assoc] using solve_mul_I (hrot.unique hsame)

theorem generalJComplexFirst_rotate_lower {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) :
    generalJComplexFirst nu ((-I) * (q : ℂ)) =
      I * Complex.exp ((-I) * (Real.pi : ℂ) * nu / 2) * generalIFirst nu q := by
  have hrot : HasDerivAt (fun x : ℝ => generalJComplex nu ((-I) * (x : ℂ)))
      (generalJComplexFirst nu ((-I) * (q : ℂ)) * (-I)) q := by
    simpa only [mul_one] using
      (((generalJComplex_hasDerivAt hnu (lower_mem_slit hq)).comp (q : ℂ)
        ((hasDerivAt_id (q : ℂ)).const_mul (-I))).comp_ofReal)
  have hright := (generalI_hasDerivAt hnu hq).const_mul
    (Complex.exp ((-I) * (Real.pi : ℂ) * nu / 2))
  have hsame : HasDerivAt (fun x : ℝ => generalJComplex nu ((-I) * (x : ℂ)))
      (Complex.exp ((-I) * (Real.pi : ℂ) * nu / 2) * generalIFirst nu q) q := by
    apply hright.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hq] with x hx
    exact generalJComplex_rotate_lower nu hx
  simpa only [mul_assoc] using solve_mul_neg_I (hrot.unique hsame)

theorem generalJComplexSecond_rotate_upper {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) :
    generalJComplexSecond nu (I * (q : ℂ)) =
      -(Complex.exp (I * (Real.pi : ℂ) * nu / 2) * generalISecond nu q) := by
  have hrot : HasDerivAt (fun x : ℝ => generalJComplexFirst nu (I * (x : ℂ)))
      (generalJComplexSecond nu (I * (q : ℂ)) * I) q := by
    simpa only [mul_one] using
      (((generalJComplexFirst_hasDerivAt hnu (upper_mem_slit hq)).comp (q : ℂ)
        ((hasDerivAt_id (q : ℂ)).const_mul I)).comp_ofReal)
  have hright := (generalIFirst_hasDerivAt hnu hq).const_mul
    ((-I) * Complex.exp (I * (Real.pi : ℂ) * nu / 2))
  have hsame : HasDerivAt (fun x : ℝ => generalJComplexFirst nu (I * (x : ℂ)))
      (((-I) * Complex.exp (I * (Real.pi : ℂ) * nu / 2)) * generalISecond nu q) q := by
    apply hright.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hq] with x hx
    exact generalJComplexFirst_rotate_upper hnu hx
  calc
    _ = (-I) * (((-I) * Complex.exp (I * (Real.pi : ℂ) * nu / 2)) * generalISecond nu q) :=
      solve_mul_I (hrot.unique hsame)
    _ = (I * I) * (Complex.exp (I * (Real.pi : ℂ) * nu / 2) * generalISecond nu q) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

theorem generalJComplexSecond_rotate_lower {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) :
    generalJComplexSecond nu ((-I) * (q : ℂ)) =
      -(Complex.exp ((-I) * (Real.pi : ℂ) * nu / 2) * generalISecond nu q) := by
  have hrot : HasDerivAt (fun x : ℝ => generalJComplexFirst nu ((-I) * (x : ℂ)))
      (generalJComplexSecond nu ((-I) * (q : ℂ)) * (-I)) q := by
    simpa only [mul_one] using
      (((generalJComplexFirst_hasDerivAt hnu (lower_mem_slit hq)).comp (q : ℂ)
        ((hasDerivAt_id (q : ℂ)).const_mul (-I))).comp_ofReal)
  have hright := (generalIFirst_hasDerivAt hnu hq).const_mul
    (I * Complex.exp ((-I) * (Real.pi : ℂ) * nu / 2))
  have hsame : HasDerivAt (fun x : ℝ => generalJComplexFirst nu ((-I) * (x : ℂ)))
      ((I * Complex.exp ((-I) * (Real.pi : ℂ) * nu / 2)) * generalISecond nu q) q := by
    apply hright.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hq] with x hx
    exact generalJComplexFirst_rotate_lower hnu hx
  calc
    _ = I * ((I * Complex.exp ((-I) * (Real.pi : ℂ) * nu / 2)) * generalISecond nu q) :=
      solve_mul_neg_I (hrot.unique hsame)
    _ = (I * I) * (Complex.exp ((-I) * (Real.pi : ℂ) * nu / 2) * generalISecond nu q) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

end
end ImbalancedChen.Part3.ActualJComplexJetRotations20261026b
