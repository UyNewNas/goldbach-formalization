import ImbalancedChen.Part3RealOrderKExceptional
import ImbalancedChen.Part3ModifiedHalfOrderISeries
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Actual half-order K integral and its normalized I-K Wronskian

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The K function is the existing actual cosh-order integral. Its half-order
value is evaluated by the genuine substitution v=sinh(u/2), using the
native Jacobian theorem and the Gaussian half-line integral. Thus no K
closed form, ODE, or Wronskian is assumed. The final Wronskian convention
is I K' - I' K = -1/q at real order 1/2, and not at imaginary order 2it.
-/

namespace ImbalancedChen.Part3.ActualHalfOrderKWronskianSourceOnly

noncomputable section

open Set MeasureTheory Filter
open scoped Topology
open RealOrderKExceptionalSourceOnly ModifiedHalfOrderISourceOnly

def halfKChange (u : ℝ) : ℝ := Real.sinh (u / 2)

theorem halfKChange_hasDerivAt (u : ℝ) :
    HasDerivAt halfKChange (Real.cosh (u / 2) / 2) u := by
  have h := (Real.hasDerivAt_sinh (u / 2)).comp u ((hasDerivAt_id u).div_const 2)
  convert h using 1 <;> dsimp [halfKChange] <;> ring

theorem halfKChange_injOn : Set.InjOn halfKChange (Ioi (0 : ℝ)) := by
  intro x _hx y _hy hxy
  dsimp [halfKChange] at hxy
  have hdiv : x / 2 = y / 2 := Real.sinh_injective hxy
  linarith only [hdiv]

theorem halfKChange_image : halfKChange '' Ioi (0 : ℝ) = Ioi 0 := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact Real.sinh_pos_iff.mpr (div_pos hu (by norm_num))
  · intro hv
    refine ⟨2 * Real.arsinh v, mul_pos (by norm_num) (Real.arsinh_pos_iff.mpr hv), ?_⟩
    simp [halfKChange]

def halfKGaussian (q v : ℝ) : ℝ :=
  2 * Real.exp (-q) * Real.exp (-(2 * q) * v ^ 2)

theorem cosh_eq_one_add_two_sinh_half_sq (u : ℝ) :
    Real.cosh u = 1 + 2 * Real.sinh (u / 2) ^ 2 := by
  have h := Real.cosh_two_mul (u / 2)
  rw [Real.cosh_sq] at h
  have heq : 2 * (u / 2) = u := by ring
  rw [heq] at h
  linarith only [h]

/-- The actual integrand is exactly the Gaussian pullback times its Jacobian. -/
theorem realOrderIntegrand_half_eq_jacobian (q u : ℝ) :
    realOrderIntegrand (1 / 2 : ℝ) q u =
      |Real.cosh (u / 2) / 2| • halfKGaussian q (halfKChange u) := by
  have hhalf : (1 / 2 : ℝ) * u = u / 2 := by ring
  have hexponent : -q * (1 + 2 * Real.sinh (u / 2) ^ 2) =
      -q + -(2 * q) * Real.sinh (u / 2) ^ 2 := by ring
  rw [realOrderIntegrand, hhalf, cosh_eq_one_add_two_sinh_half_sq, hexponent, Real.exp_add]
  simp only [halfKGaussian, halfKChange, smul_eq_mul,
    abs_of_pos (div_pos (Real.cosh_pos _) (by norm_num : (0 : ℝ) < 2))]
  ring

theorem halfKGaussian_integrable {q : ℝ} (hq : 0 < q) :
    IntegrableOn (halfKGaussian q) (Ioi (0 : ℝ)) := by
  exact ((integrable_exp_neg_mul_sq (mul_pos (by norm_num) hq)).const_mul
    (2 * Real.exp (-q))).integrableOn

/-- The half-order actual K integrand is integrable, even though this
order lies outside the earlier exceptional interval [−7/32,7/32]. -/
theorem realOrderIntegrand_half_integrable {q : ℝ} (hq : 0 < q) :
    IntegrableOn (realOrderIntegrand (1 / 2 : ℝ) q) (Ioi (0 : ℝ)) := by
  have hg : IntegrableOn (halfKGaussian q) (halfKChange '' Ioi (0 : ℝ)) := by
    rw [halfKChange_image]
    exact halfKGaussian_integrable hq
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun u _hu => (halfKChange_hasDerivAt u).hasDerivWithinAt)
    halfKChange_injOn (halfKGaussian q)).mp hg
  have heq : realOrderIntegrand (1 / 2 : ℝ) q =
      fun u => |Real.cosh (u / 2) / 2| • halfKGaussian q (halfKChange u) :=
    funext (realOrderIntegrand_half_eq_jacobian q)
  rw [heq]
  exact h

/-- Exact evaluation of the existing actual integral by a genuine
change of variables followed by the Gaussian half-line theorem. -/
theorem realOrderK_half_eq_gaussian_closedForm {q : ℝ} (hq : 0 < q) :
    realOrderK (1 / 2 : ℝ) q = Real.sqrt (Real.pi / (2 * q)) * Real.exp (-q) := by
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u _hu => (halfKChange_hasDerivAt u).hasDerivWithinAt)
    halfKChange_injOn (halfKGaussian q)
  rw [halfKChange_image] at hsub
  calc
    realOrderK (1 / 2 : ℝ) q =
        ∫ u in Ioi (0 : ℝ), |Real.cosh (u / 2) / 2| •
          halfKGaussian q (halfKChange u) := by
      unfold realOrderK
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (realOrderIntegrand_half_eq_jacobian q)
    _ = ∫ v in Ioi (0 : ℝ), halfKGaussian q v := hsub.symm
    _ = 2 * Real.exp (-q) * (Real.sqrt (Real.pi / (2 * q)) / 2) := by
      unfold halfKGaussian
      rw [integral_const_mul, integral_gaussian_Ioi]
    _ = Real.sqrt (Real.pi / (2 * q)) * Real.exp (-q) := by ring

def halfKNormalization : ℝ := Real.sqrt (Real.pi / 2)

theorem sqrt_halfK_scale_eq_rpow {q : ℝ} (hq : 0 < q) :
    Real.sqrt (Real.pi / (2 * q)) = halfKNormalization * q ^ (-1 / 2 : ℝ) := by
  have hr : q ^ (-1 / 2 : ℝ) = (Real.sqrt q)⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hq.le,
      ← Real.sqrt_eq_rpow]
  rw [hr]
  have hdiv : Real.pi / (2 * q) = (Real.pi / 2) / q := by ring
  rw [hdiv, Real.sqrt_div (div_nonneg Real.pi_pos.le (by norm_num))]
  simp only [halfKNormalization, div_eq_mul_inv]

theorem realOrderK_half_eq_rpow {q : ℝ} (hq : 0 < q) :
    realOrderK (1 / 2 : ℝ) q = halfKNormalization * q ^ (-1 / 2 : ℝ) * Real.exp (-q) := by
  rw [realOrderK_half_eq_gaussian_closedForm hq, sqrt_halfK_scale_eq_rpow hq]

def actualHalfKFirst (q : ℝ) : ℝ :=
  halfKNormalization *
    ((-1 / 2 : ℝ) * q ^ (-3 / 2 : ℝ) * Real.exp (-q) -
      q ^ (-1 / 2 : ℝ) * Real.exp (-q))

/-- Actual derivative of the actual K integral, justified by its evaluated
closed form on an open neighborhood, not by an assumed derivative supplier. -/
theorem realOrderK_half_hasDerivAt {q : ℝ} (hq : 0 < q) :
    HasDerivAt (realOrderK (1 / 2 : ℝ)) (actualHalfKFirst q) q := by
  have h := ((hasDerivAt_rpow_minus_half hq).const_mul halfKNormalization).mul
    ((hasDerivAt_id q).neg.exp)
  have hcalc : HasDerivAt
      (fun x : ℝ => halfKNormalization * x ^ (-1 / 2 : ℝ) * Real.exp (-x))
      (actualHalfKFirst q) q := by
    convert h using 1 <;> dsimp [actualHalfKFirst] <;> ring
  apply hcalc.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hq] with x hx
  exact realOrderK_half_eq_rpow hx

theorem halfIK_normalization_mul : halfINormalization * halfKNormalization = 1 := by
  unfold halfINormalization halfKNormalization
  rw [← Real.sqrt_mul (div_nonneg (by norm_num) Real.pi_pos.le)]
  have hratio : (2 / Real.pi) * (Real.pi / 2) = (1 : ℝ) := by
    field_simp [Real.pi_ne_zero]
    <;> ring
  rw [hratio, Real.sqrt_one]

theorem rpow_minus_half_mul_self {q : ℝ} (hq : 0 < q) :
    q ^ (-1 / 2 : ℝ) * q ^ (-1 / 2 : ℝ) = q⁻¹ := by
  rw [← Real.rpow_add hq]
  norm_num

/-- The normalized Wronskian of the actual convergent I-series and the
actual K-integral. The sign corresponds to I K' minus I' K. -/
theorem actual_halfOrder_IK_wronskian {q : ℝ} (hq : 0 < q) :
    modifiedHalfI q * deriv (realOrderK (1 / 2 : ℝ)) q -
      deriv modifiedHalfI q * realOrderK (1 / 2 : ℝ) q = -1 / q := by
  rw [(realOrderK_half_hasDerivAt hq).deriv, (modifiedHalfI_hasDerivAt hq).deriv,
    modifiedHalfI_eq_closedForm, realOrderK_half_eq_rpow hq]
  have hexp : Real.exp (-q) * (Real.sinh q + Real.cosh q) = 1 := by
    rw [Real.sinh_add_cosh, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    (halfINormalization * q ^ (-1 / 2 : ℝ) * Real.sinh q) * actualHalfKFirst q -
        modifiedHalfIFirst q *
          (halfKNormalization * q ^ (-1 / 2 : ℝ) * Real.exp (-q)) =
        -(halfINormalization * halfKNormalization) *
          (q ^ (-1 / 2 : ℝ) * q ^ (-1 / 2 : ℝ)) *
          (Real.exp (-q) * (Real.sinh q + Real.cosh q)) := by
      dsimp only [actualHalfKFirst, modifiedHalfIFirst]
      ring
    _ = -1 / q := by
      rw [halfIK_normalization_mul, rpow_minus_half_mul_self hq, hexp]
      ring

end

end ImbalancedChen.Part3.ActualHalfOrderKWronskianSourceOnly
