import ImbalancedChen.Part3ComplexOrderKLargeArgument
import ImbalancedChen.Part3ComplexOrderKQCalculus
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Sharp actual positive-argument K decay uniform in a closed order strip:
|K_nu(q)| <= C_A exp(-q)/sqrt(q), q>=1, |Re(nu)|<=A.
The genuine scaled Laplace identity and quadratic cosh lower bound are
reused. Completing the square absorbs the linear order factor into
exp(A^2) times the actual Gaussian exp(-v^2/4), for EVERY q>=1.
No large-q asymptotic or decay hypothesis is used. This exact exp(-q)
factor is the missing cancellation at the conjugate imaginary boundary.
-/

namespace ImbalancedChen.Part3.ActualKSharpUniformDecay20261026b

noncomputable section
open Set MeasureTheory Filter
open ComplexOrderKBridgeSourceOnly ComplexOrderKQCalculus
open ComplexOrderKLargeArgument20261025a

def sharpGaussianMass : ℝ := ∫ v in Ioi (0 : ℝ), Real.exp (-(v ^ 2 / 4))

def sharpKDecayConstant (A : ℝ) : ℝ := Real.exp (A ^ 2) * (sharpGaussianMass + 1)

theorem sharpGaussianMass_nonneg : 0 ≤ sharpGaussianMass := integral_nonneg fun _ => (Real.exp_pos _).le

theorem sharpKDecayConstant_pos (A : ℝ) : 0 < sharpKDecayConstant A :=
  mul_pos (Real.exp_pos _) (by linarith [sharpGaussianMass_nonneg])

/-- A uniform Gaussian bound valid from q=1, without the old condition
q>=2(Re(nu))^2. The order is absorbed by a completed square. -/
theorem scaledKernel_norm_le_uniform_gaussian {nu : ℂ} {q v A : ℝ}
    (hq : 1 ≤ q) (hA : 0 ≤ A) (horder : |nu.re| ≤ A) (hv : 0 ≤ v) :
    ‖scaledKernel nu q v‖ ≤ Real.exp (A ^ 2) * Real.exp (-(v ^ 2 / 4)) := by
  have hqp : 0 < q := zero_lt_one.trans_le hq
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqp
  have hs1 : 1 ≤ Real.sqrt q := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hq
  let u : ℝ := v / Real.sqrt q
  have hu : 0 ≤ u := div_nonneg hv hs.le
  have huv : u ≤ v := by
    apply (div_le_iff₀ hs).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hs1 hv
  have hfactor : q * u ^ 2 = v ^ 2 := by
    dsimp [u]
    rw [div_pow, Real.sq_sqrt hqp.le]
    field_simp [hqp.ne'] <;> ring
  have hcosh := cosh_quadratic_at_zero hu
  have hcoshWeighted := mul_le_mul_of_nonneg_left hcosh hqp.le
  have hAu := mul_le_mul_of_nonneg_left huv hA
  have hc : ‖Complex.cosh (nu * (u : ℂ))‖ ≤ Real.exp (A * u) := by
    have hn : ‖Complex.cosh (nu * (u : ℂ))‖ ≤ Real.exp (|nu.re| * u) := by
      apply (norm_complex_cosh_le_real_cosh _).trans
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
        cosh_le_exp_abs_mul nu.re hu
    exact hn.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right horder hu))
  have hdecay : -q * (Real.cosh u - 1) + A * u ≤ A ^ 2 - v ^ 2 / 4 := by
    nlinarith [sq_nonneg (v / 2 - A), hcoshWeighted, hfactor, hAu]
  calc
    ‖scaledKernel nu q v‖ = Real.exp (-q * (Real.cosh u - 1)) *
        ‖Complex.cosh (nu * (u : ℂ))‖ := by
      simp only [scaledKernel, u, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-q * (Real.cosh u - 1)) * Real.exp (A * u) :=
      mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
    _ = Real.exp (-q * (Real.cosh u - 1) + A * u) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (A ^ 2 - v ^ 2 / 4) := Real.exp_le_exp.mpr hdecay
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]

/-- Actual sharp decay of the literal K integral, with one constant for
the full closed order strip and every q>=1. -/
theorem complexOrderK_uniform_sharp_bound {nu : ℂ} {q A : ℝ}
    (hq : 1 ≤ q) (hA : 0 ≤ A) (horder : |nu.re| ≤ A) :
    ‖complexOrderK nu q‖ ≤ sharpKDecayConstant A * Real.exp (-q) / Real.sqrt q := by
  have hqp : 0 < q := zero_lt_one.trans_le hq
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqp
  have hbound : ‖∫ v in Ioi (0 : ℝ), scaledKernel nu q v‖ ≤
      Real.exp (A ^ 2) * sharpGaussianMass := by
    have h := norm_integral_le_of_norm_le (gaussianMajorant_integrable.const_mul (Real.exp (A ^ 2)))
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
        exact scaledKernel_norm_le_uniform_gaussian hq hA horder hv.le)
    simpa only [integral_const_mul, sharpGaussianMass] using h
  have hnorm := congrArg norm (scaledKernel_integral nu hqp)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos hs (Real.exp_pos q))] at hnorm
  have hscaled : (Real.sqrt q * Real.exp q) * ‖complexOrderK nu q‖ ≤ sharpKDecayConstant A := by
    apply (hnorm.symm.trans_le hbound).trans
    unfold sharpKDecayConstant
    exact mul_le_mul_of_nonneg_left (by linarith : sharpGaussianMass ≤ sharpGaussianMass + 1)
      (Real.exp_pos _).le
  have hdiv : ‖complexOrderK nu q‖ ≤ sharpKDecayConstant A / (Real.sqrt q * Real.exp q) :=
    (le_div_iff₀ (mul_pos hs (Real.exp_pos q))).mpr (by
      simpa only [mul_comm] using hscaled)
  calc
    _ ≤ sharpKDecayConstant A / (Real.sqrt q * Real.exp q) := hdiv
    _ = _ := by
      rw [Real.exp_neg]
      field_simp [hs.ne', Real.exp_ne_zero q] <;> ring

end
end ImbalancedChen.Part3.ActualKSharpUniformDecay20261026b
