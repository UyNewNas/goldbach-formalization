import ImbalancedChen.Part3PowerSeedGaussianLaplace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Absolute convergence and actual Fourier--Laplace exchange for power seeds

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The full convergence range is real s > 1/2 and y > 0. Gaussian integration
of the absolute value lowers the Laplace power from s-1 to s-3/2, giving
a convergent Gamma(s-1/2) density. This establishes joint integrability
before invoking Fubini. The actual period-one Fourier coefficient is
then expressed as a single convergent Laplace integral with exact pi and
Gamma normalization. Evaluation of that last integral by the actual
cosh-Laplace realOrderK is a separate remaining change of variables.
-/

namespace ImbalancedChen.Part3.PowerSeedFourierLaplaceFubini

noncomputable section
open Set MeasureTheory
open PowerSeedGaussianLaplace

/-- The logarithmic expression provides global measurability and agrees
with t^(s-1) on the positive integration domain. -/
def laplaceAmplitude (s y t : ℝ) : ℝ :=
  y ^ s * Real.exp (Real.log t * (s - 1)) * Real.exp (-t * y ^ 2)

def fourierPhase (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ)) * Complex.I * (x : ℂ))

def fourierLaplaceKernel (s y : ℝ) (n : ℤ) (t x : ℝ) : ℂ :=
  (laplaceAmplitude s y t : ℂ) *
    (fourierPhase n x * Complex.exp (-(t : ℂ) * (x : ℂ) ^ 2))

theorem laplaceAmplitude_nonneg {y : ℝ} (hy : 0 < y) (s t : ℝ) :
    0 ≤ laplaceAmplitude s y t := by
  unfold laplaceAmplitude
  positivity

theorem fourierPhase_norm (n : ℤ) (x : ℝ) : ‖fourierPhase n x‖ = 1 := by
  simp [fourierPhase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem fourierLaplaceKernel_norm {y : ℝ} (hy : 0 < y)
    (s : ℝ) (n : ℤ) (t x : ℝ) :
    ‖fourierLaplaceKernel s y n t x‖ =
      laplaceAmplitude s y t * Real.exp (-t * x ^ 2) := by
  simp only [fourierLaplaceKernel, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (laplaceAmplitude_nonneg hy s t),
    fourierPhase_norm, one_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re, Complex.mul_im]

theorem laplace_power_sqrt_identity (s : ℝ) {t : ℝ} (ht : 0 < t) :
    Real.exp (Real.log t * (s - 1)) * Real.sqrt (Real.pi / t) =
      Real.sqrt Real.pi * t ^ (s - 3 / 2) := by
  rw [← Real.rpow_def_of_pos ht]
  calc
    _ = Real.sqrt Real.pi * (t ^ (s - 1) / t ^ (1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.div_rpow Real.pi_pos.le ht.le,
        Real.sqrt_eq_rpow]
      ring
    _ = Real.sqrt Real.pi * t ^ ((s - 1) - (1 / 2 : ℝ)) := by
      rw [Real.rpow_sub ht]
    _ = _ := by congr 2 <;> ring

/-- This is exactly the norm density left by Gaussian x integration. -/
theorem laplaceAmplitude_mul_gaussian_integral (s y : ℝ)
    {t : ℝ} (ht : 0 < t) :
    laplaceAmplitude s y t * Real.sqrt (Real.pi / t) =
      (y ^ s * Real.sqrt Real.pi) *
        (t ^ (s - 3 / 2) * Real.exp (-(y ^ 2 * t))) := by
  calc
    _ = y ^ s *
        (Real.exp (Real.log t * (s - 1)) * Real.sqrt (Real.pi / t)) *
          Real.exp (-t * y ^ 2) := by unfold laplaceAmplitude; ring
    _ = _ := by
      rw [laplace_power_sqrt_identity s ht]
      have he : -t * y ^ 2 = -(y ^ 2 * t) := by ring
      rw [he]
      ring

theorem gaussian_norm_density_integrable {s y : ℝ}
    (hs : (1 / 2 : ℝ) < s) (hy : 0 < y) :
    IntegrableOn (fun t : ℝ => laplaceAmplitude s y t * Real.sqrt (Real.pi / t))
      (Ioi (0 : ℝ)) := by
  have hbase : IntegrableOn
      (fun t : ℝ => t ^ (s - 3 / 2) * Real.exp (-(y ^ 2 * t))) (Ioi (0 : ℝ)) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := s - 3 / 2) (b := y ^ 2)
        (by linarith only [hs]) le_rfl (sq_pos_of_pos hy))
  apply (hbase.const_mul (y ^ s * Real.sqrt Real.pi)).congr_fun _ measurableSet_Ioi
  intro t ht
  exact (laplaceAmplitude_mul_gaussian_integral s y ht).symm

theorem fourierLaplaceKernel_x_integrable (s y : ℝ) (n : ℤ)
    {t : ℝ} (ht : 0 < t) : Integrable (fourierLaplaceKernel s y n t) := by
  have hg := integrable_cexp_quadratic
    (b := (t : ℂ)) (by simpa only [Complex.ofReal_re] using ht)
    (-(2 * (Real.pi : ℂ) * (n : ℂ)) * Complex.I) 0
  have he : (fun x : ℝ =>
      Complex.exp (-(t : ℂ) * (x : ℂ) ^ 2 +
        (-(2 * (Real.pi : ℂ) * (n : ℂ)) * Complex.I) * (x : ℂ) + 0)) =
      fun x : ℝ => fourierPhase n x * Complex.exp (-(t : ℂ) * (x : ℂ) ^ 2) := by
    funext x
    rw [add_zero, Complex.exp_add]
    exact mul_comm _ _
  rw [he] at hg
  exact hg.const_mul (laplaceAmplitude s y t : ℂ)

/-- Actual joint absolute convergence, with no assumed Fubini licence. -/
theorem fourierLaplaceKernel_joint_integrable {s y : ℝ}
    (hs : (1 / 2 : ℝ) < s) (hy : 0 < y) (n : ℤ) :
    Integrable (fun p : ℝ × ℝ => fourierLaplaceKernel s y n p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hm : Measurable (fun p : ℝ × ℝ => fourierLaplaceKernel s y n p.1 p.2) := by
    unfold fourierLaplaceKernel laplaceAmplitude fourierPhase
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact fourierLaplaceKernel_x_integrable s y n ht
  · have he : (fun t : ℝ => ∫ x : ℝ, ‖fourierLaplaceKernel s y n t x‖) =
        fun t : ℝ => laplaceAmplitude s y t * Real.sqrt (Real.pi / t) := by
      funext t
      simp_rw [fourierLaplaceKernel_norm hy s n t]
      rw [integral_const_mul, integral_gaussian]
    rw [he]
    exact gaussian_norm_density_integrable hs hy

theorem fourierLaplaceKernel_t_integral {s y : ℝ}
    (hs : 0 < s) (hy : 0 < y) (n : ℤ) (x : ℝ) :
    (∫ t in Ioi (0 : ℝ), fourierLaplaceKernel s y n t x) =
      (Real.Gamma s : ℂ) * (fourierPhase n x * (powerSeed s y x : ℂ)) := by
  have he : (∫ t in Ioi (0 : ℝ), fourierLaplaceKernel s y n t x) =
      fourierPhase n x * ∫ t in Ioi (0 : ℝ), (seedLaplaceDensity s y x t : ℂ) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    unfold fourierLaplaceKernel laplaceAmplitude seedLaplaceDensity
    rw [Real.rpow_def_of_pos ht]
    simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg,
      Complex.ofReal_pow]
    ring
  rw [he, integral_ofReal, seedLaplaceDensity_integral hs hy x]
  push_cast
  ring

theorem fourierLaplaceKernel_x_integral (s y : ℝ) (n : ℤ)
    {t : ℝ} (ht : 0 < t) :
    (∫ x : ℝ, fourierLaplaceKernel s y n t x) =
      (laplaceAmplitude s y t : ℂ) *
        (((Real.pi : ℂ) / (t : ℂ)) ^ (1 / 2 : ℂ) *
          Complex.exp (-((Real.pi : ℂ) ^ 2 * (n : ℂ) ^ 2) / (t : ℂ))) := by
  unfold fourierLaplaceKernel fourierPhase
  rw [integral_const_mul, gaussian_integer_fourier_fiber ht n]

/-- The genuine power-seed Fourier integral equals the convergent Laplace
integral. No assertion of its later Bessel evaluation is needed. -/
theorem powerSeed_fourier_eq_laplace {s y : ℝ}
    (hs : (1 / 2 : ℝ) < s) (hy : 0 < y) (n : ℤ) :
    (∫ x : ℝ, fourierPhase n x * (powerSeed s y x : ℂ)) =
      (∫ t in Ioi (0 : ℝ), (laplaceAmplitude s y t : ℂ) *
        (((Real.pi : ℂ) / (t : ℂ)) ^ (1 / 2 : ℂ) *
          Complex.exp (-((Real.pi : ℂ) ^ 2 * (n : ℂ) ^ 2) / (t : ℂ)))) /
        (Real.Gamma s : ℂ) := by
  have hs0 : 0 < s := by linarith only [hs]
  have hΓ : (Real.Gamma s : ℂ) ≠ 0 := by
    exact_mod_cast (Real.Gamma_pos_of_pos hs0).ne'
  apply (eq_div_iff hΓ).mpr
  calc
    _ = ∫ x : ℝ, (Real.Gamma s : ℂ) *
        (fourierPhase n x * (powerSeed s y x : ℂ)) := by
      rw [integral_const_mul]
      exact mul_comm _ _
    _ = ∫ x : ℝ, ∫ t in Ioi (0 : ℝ), fourierLaplaceKernel s y n t x := by
      simp_rw [fourierLaplaceKernel_t_integral hs0 hy n]
    _ = ∫ t in Ioi (0 : ℝ), ∫ x : ℝ, fourierLaplaceKernel s y n t x :=
      (integral_integral_swap (fourierLaplaceKernel_joint_integrable hs hy n)).symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact fourierLaplaceKernel_x_integral s y n ht

end

end ImbalancedChen.Part3.PowerSeedFourierLaplaceFubini
