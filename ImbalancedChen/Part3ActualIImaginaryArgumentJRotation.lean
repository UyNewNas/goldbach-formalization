import ImbalancedChen.Part3ActualComplexArgumentISlit
import ImbalancedChen.Part3ActualGeneralJComplexArgument

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Reverse imaginary-axis dictionary for the actual positive-quadratic I
core: I_nu(+/-iq)=exp(+/-i*pi*nu/2) J_nu(q). This is derived literally,
not inferred from the reverse J(iq) rotation. Native complex I first
derivatives on both axes are then identified by derivative uniqueness.
No K continuation, critical quotient, or normalization is an assumption.
-/

namespace ImbalancedChen.Part3.ActualIImaginaryArgumentJRotation20261026b

noncomputable section
open Complex Set Filter
open scoped Topology
open GeneralComplexISeriesSourceOnly ActualGeneralJBesselSourceOnly
open ActualComplexArgumentISlit20261026b ActualGeneralJComplexArgument20261025a

theorem complexArgumentI_rotate_upper (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    complexArgumentI nu (I * (q : ℂ)) =
      Complex.exp (I * (Real.pi : ℂ) * nu / 2) * generalJ nu q := by
  have hh : 0 < q / 2 := div_pos hq (by norm_num)
  have hb : (I * (q : ℂ)) / 2 = ((q / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have hc : ((I * (q : ℂ)) / 2) ^ (2 : ℕ) = -(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)) := by
    rw [hb, mul_pow, Complex.I_sq]
    ring
  rw [complexArgumentI, hc, hb, positive_mul_I_cpow nu hh, generalJ]
  ring

theorem complexArgumentI_rotate_lower (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    complexArgumentI nu ((-I) * (q : ℂ)) =
      Complex.exp ((-I) * (Real.pi : ℂ) * nu / 2) * generalJ nu q := by
  have hh : 0 < q / 2 := div_pos hq (by norm_num)
  have hb : ((-I) * (q : ℂ)) / 2 = ((q / 2 : ℝ) : ℂ) * (-I) := by push_cast; ring
  have hc : (((-I) * (q : ℂ)) / 2) ^ (2 : ℕ) = -(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)) := by
    rw [hb, mul_pow, neg_sq, Complex.I_sq]
    ring
  rw [complexArgumentI, hc, hb, positive_mul_neg_I_cpow nu hh, generalJ]
  ring

theorem deriv_complexArgumentI_rotate_upper {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) :
    deriv (complexArgumentI nu) (I * (q : ℂ)) =
      (-I) * Complex.exp (I * (Real.pi : ℂ) * nu / 2) * generalJFirst nu q := by
  have hz : I * (q : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; right; simpa using hq.ne'
  have hd := (complexArgumentI_analyticAt hnu hz).differentiableAt.hasDerivAt
  have hrot : HasDerivAt (fun x : ℝ => complexArgumentI nu (I * (x : ℂ)))
      (deriv (complexArgumentI nu) (I * (q : ℂ)) * I) q := by
    simpa only [mul_one] using
      ((hd.comp (q : ℂ) ((hasDerivAt_id (q : ℂ)).const_mul I)).comp_ofReal)
  have hr := (generalJ_hasDerivAt hnu hq).const_mul (Complex.exp (I * (Real.pi : ℂ) * nu / 2))
  have hs : HasDerivAt (fun x : ℝ => complexArgumentI nu (I * (x : ℂ)))
      (Complex.exp (I * (Real.pi : ℂ) * nu / 2) * generalJFirst nu q) q := by
    apply hr.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hq] with x hx
    exact complexArgumentI_rotate_upper nu hx
  have he := congrArg (fun w : ℂ => w * (-I)) (hrot.unique hs)
  have hi : I * (-I) = 1 := by rw [mul_neg, Complex.I_sq]; ring
  rw [mul_assoc, hi, mul_one] at he
  exact he.trans (by ring)

theorem deriv_complexArgumentI_rotate_lower {nu : ℂ} (hnu : -1 < nu.re)
    {q : ℝ} (hq : 0 < q) :
    deriv (complexArgumentI nu) ((-I) * (q : ℂ)) =
      I * Complex.exp ((-I) * (Real.pi : ℂ) * nu / 2) * generalJFirst nu q := by
  have hz : (-I) * (q : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; right; simpa using (neg_ne_zero.mpr hq.ne')
  have hd := (complexArgumentI_analyticAt hnu hz).differentiableAt.hasDerivAt
  have hrot : HasDerivAt (fun x : ℝ => complexArgumentI nu ((-I) * (x : ℂ)))
      (deriv (complexArgumentI nu) ((-I) * (q : ℂ)) * (-I)) q := by
    simpa only [mul_one] using
      ((hd.comp (q : ℂ) ((hasDerivAt_id (q : ℂ)).const_mul (-I))).comp_ofReal)
  have hr := (generalJ_hasDerivAt hnu hq).const_mul (Complex.exp ((-I) * (Real.pi : ℂ) * nu / 2))
  have hs : HasDerivAt (fun x : ℝ => complexArgumentI nu ((-I) * (x : ℂ)))
      (Complex.exp ((-I) * (Real.pi : ℂ) * nu / 2) * generalJFirst nu q) q := by
    apply hr.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hq] with x hx
    exact complexArgumentI_rotate_lower nu hx
  have he := congrArg (fun w : ℂ => w * I) (hrot.unique hs)
  have hi : (-I) * I = 1 := by rw [neg_mul, Complex.I_sq]; ring
  rw [mul_assoc, hi, mul_one] at he
  exact he.trans (by ring)

end
end ImbalancedChen.Part3.ActualIImaginaryArgumentJRotation20261026b
