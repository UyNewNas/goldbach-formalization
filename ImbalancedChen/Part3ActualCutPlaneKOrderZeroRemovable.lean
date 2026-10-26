import ImbalancedChen.Part3ActualCutPlaneKZeroModel
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

The actual sine/I-minus-I cut expression has its true removable order-zero
limit at every nonzero complex argument. The numerator derivative and the
sine derivative are proved, then their slope limits are divided. This
limit is exactly the previously constructed literal negative order
derivative model. A glued cut K model is therefore continuous in the
order at zero and slit-holomorphic in the argument. No singular quotient
is evaluated at zero and no removable-limit premise is supplied.
-/

namespace ImbalancedChen.Part3.ActualCutPlaneKOrderZeroRemovable20261026b

noncomputable section
open Set Filter
open scoped Topology
open ActualComplexArgumentISlit20261026b ActualCutPlaneKIModel20261026b
open ActualCutPlaneKZeroModel20261026b ActualComplexArgumentKLaplace20261026b

theorem complexArgumentI_odd_order_zero_hasDerivAt {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (fun nu : ℂ => complexArgumentI (-nu) z - complexArgumentI nu z)
      (-2 * deriv (fun nu : ℂ => complexArgumentI nu z) 0) 0 := by
  have hd := (complexArgumentI_order_analyticAt 0 (by norm_num) hz).differentiableAt.hasDerivAt
  have hm : HasDerivAt (fun nu : ℂ => complexArgumentI (-nu) z)
      (-deriv (fun nu : ℂ => complexArgumentI nu z) 0) 0 := by
    simpa only [neg_zero, mul_neg_one] using hd.comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))
  convert hm.sub hd using 1 <;> ring

/-- The actual punctured complex-order limit, from two independently
proved derivative slope limits. The argument z may be anywhere except 0. -/
theorem cutPlaneKNonintegral_tendsto_order_zero {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun nu : ℂ => cutPlaneKNonintegral nu z) (𝓝[≠] 0) (𝓝 (cutPlaneKZero z)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hg : Tendsto (fun nu : ℂ =>
      (complexArgumentI (-nu) z - complexArgumentI nu z) / nu)
      (𝓝[≠] 0) (𝓝 (-2 * deriv (fun nu : ℂ => complexArgumentI nu z) 0)) := by
    simpa only [zero_add, neg_zero, sub_self, sub_zero, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using (complexArgumentI_odd_order_zero_hasDerivAt hz).tendsto_slope_zero
  have hs : HasDerivAt (fun nu : ℂ => Complex.sin ((Real.pi : ℂ) * nu)) (Real.pi : ℂ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (Real.pi : ℂ)).csin
  have hslope : Tendsto (fun nu : ℂ => Complex.sin ((Real.pi : ℂ) * nu) / nu)
      (𝓝[≠] 0) (𝓝 (Real.pi : ℂ)) := by
    simpa only [zero_add, mul_zero, Complex.sin_zero, sub_zero, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using hs.tendsto_slope_zero
  have hratio := (hg.div hslope hpi).const_mul ((Real.pi : ℂ) / 2)
  have hconstant : (Real.pi : ℂ) / 2 *
      ((-2 * deriv (fun nu : ℂ => complexArgumentI nu z) 0) / (Real.pi : ℂ)) = cutPlaneKZero z := by
    unfold cutPlaneKZero
    field_simp [hpi] <;> ring
  rw [hconstant] at hratio
  apply hratio.congr'
  filter_upwards [self_mem_nhdsWithin] with nu hnu
  have hn : nu ≠ 0 := hnu
  unfold cutPlaneKNonintegral
  rw [div_div_div_cancel_right₀ hn]
  ring

/-- The value at order zero is supplied by its actual derivative model,
not by evaluating the singular sine quotient. -/
def cutPlaneKWithZero (nu z : ℂ) : ℂ :=
  if nu = 0 then cutPlaneKZero z else cutPlaneKNonintegral nu z

theorem cutPlaneKWithZero_zero (z : ℂ) : cutPlaneKWithZero 0 z = cutPlaneKZero z := by
  simp only [cutPlaneKWithZero, if_pos rfl]

theorem cutPlaneKWithZero_of_ne_zero {nu : ℂ} (hnu : nu ≠ 0) (z : ℂ) :
    cutPlaneKWithZero nu z = cutPlaneKNonintegral nu z := by
  simp only [cutPlaneKWithZero, if_neg hnu]

/-- Genuine continuity in the order at zero of the glued cut-plane model. -/
theorem cutPlaneKWithZero_continuousAt_order_zero {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt (fun nu : ℂ => cutPlaneKWithZero nu z) 0 := by
  rw [continuousAt_iff_punctured_nhds, cutPlaneKWithZero_zero]
  apply (cutPlaneKNonintegral_tendsto_order_zero hz).congr'
  filter_upwards [self_mem_nhdsWithin] with nu hnu
  exact (cutPlaneKWithZero_of_ne_zero hnu z).symm

/-- Slit holomorphy in z includes the actual removable zero-order value. -/
theorem cutPlaneKWithZero_analyticOnNhd {nu : ℂ} (hL : -1 < nu.re) (hU : nu.re < 1) :
    AnalyticOnNhd ℂ (cutPlaneKWithZero nu) Complex.slitPlane := by
  by_cases hnu : nu = 0
  · subst nu
    simpa only [cutPlaneKWithZero, if_pos rfl] using cutPlaneKZero_analyticOnNhd
  · simpa only [cutPlaneKWithZero, if_neg hnu] using cutPlaneKNonintegral_analyticOnNhd hL hU

/-- Agreement with the actual Laplace K on every order range for which
an actual K/I supplier has been proved, now including the zero order. -/
theorem cutPlaneKWithZero_eq_actual {nu z : ℂ}
    (horder : nu = 0 ∨ (0 < nu.re ∧ nu.re < 1) ∨ (nu.re = 0 ∧ nu.im ≠ 0))
    (hz : 0 < z.re) : cutPlaneKWithZero nu z = complexArgumentK nu z := by
  rcases horder with rfl | hpositive | himaginary
  · rw [cutPlaneKWithZero_zero]
    exact cutPlaneKZero_eq_actual hz
  · have hn : nu ≠ 0 := by intro h; simpa only [h, Complex.zero_re, lt_self_iff_false] using hpositive.1
    rw [cutPlaneKWithZero_of_ne_zero hn]
    exact cutPlaneKNonintegral_eq_actual_positive_strip hpositive.1 hpositive.2 hz
  · have hn : nu ≠ 0 := by intro h; exact himaginary.2 (by simp only [h, Complex.zero_im])
    rw [cutPlaneKWithZero_of_ne_zero hn]
    exact cutPlaneKNonintegral_eq_actual_imaginary himaginary.1 himaginary.2 hz

end
end ImbalancedChen.Part3.ActualCutPlaneKOrderZeroRemovable20261026b
