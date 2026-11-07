import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic

/-!
# Genuine Gaussian--Laplace representation of the real power seed

CODE_ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The seed is literally y^s/(x^2+y^2)^s. For positive real s and y,
its Gamma-normalized Laplace representation is proved from the pinned
Gamma integral, including integrability of the Laplace fiber.
The Gaussian Fourier fiber has the actual exp(-2*pi*i*n*x) phase.

These are prerequisites for the nonzero Fourier coefficient calculation,
not an assumed Fourier formula for the power seed. Product integrability,
Fubini and conversion of the remaining Laplace integral to the actual
cosh-Laplace realOrderK still remain to be proved. No zero-mode integral
of the power seed is asserted here.
-/

namespace ImbalancedChen.Part3.PowerSeedGaussianLaplace

noncomputable section
open Set MeasureTheory

def powerSeed (s y x : ℝ) : ℝ := y ^ s / (x ^ 2 + y ^ 2) ^ s

/-- The Gaussian x fiber is kept separate from the positive y damping. -/
def seedLaplaceDensity (s y x t : ℝ) : ℝ :=
  y ^ s * (t ^ (s - 1) * Real.exp (-t * y ^ 2) * Real.exp (-t * x ^ 2))

theorem seedLaplaceDensity_eq_gamma_kernel (s y x t : ℝ) :
    seedLaplaceDensity s y x t =
      y ^ s * (t ^ (s - 1) * Real.exp (-((x ^ 2 + y ^ 2) * t))) := by
  unfold seedLaplaceDensity
  rw [mul_assoc (t ^ (s - 1)), ← Real.exp_add]
  congr 3
  ring

theorem seedLaplaceDensity_integrable {s y : ℝ}
    (hs : 0 < s) (hy : 0 < y) (x : ℝ) :
    IntegrableOn (seedLaplaceDensity s y x) (Ioi (0 : ℝ)) := by
  have hq : 0 < x ^ 2 + y ^ 2 := by positivity
  have hbase : IntegrableOn
      (fun t : ℝ => t ^ (s - 1) * Real.exp (-((x ^ 2 + y ^ 2) * t)))
      (Ioi (0 : ℝ)) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := s - 1) (b := x ^ 2 + y ^ 2)
        (by linarith only [hs]) le_rfl hq)
  simpa only [seedLaplaceDensity_eq_gamma_kernel] using hbase.const_mul (y ^ s)

/-- Exact real-s Laplace integral, with the Gamma factor and y^s retained. -/
theorem seedLaplaceDensity_integral {s y : ℝ}
    (hs : 0 < s) (hy : 0 < y) (x : ℝ) :
    (∫ t in Ioi (0 : ℝ), seedLaplaceDensity s y x t) =
      Real.Gamma s * powerSeed s y x := by
  have hq : 0 < x ^ 2 + y ^ 2 := by positivity
  simp_rw [seedLaplaceDensity_eq_gamma_kernel]
  rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hs hq,
    Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) hq.le, Real.one_rpow]
  unfold powerSeed
  ring

/-- The genuine positive seed is the Gaussian mixture divided by Gamma(s).
Gamma nonvanishing is proved from s>0, not assumed as a normalization. -/
theorem powerSeed_eq_normalized_laplace {s y : ℝ}
    (hs : 0 < s) (hy : 0 < y) (x : ℝ) :
    powerSeed s y x =
      (∫ t in Ioi (0 : ℝ), seedLaplaceDensity s y x t) / Real.Gamma s := by
  rw [seedLaplaceDensity_integral hs hy x]
  exact (mul_div_cancel_left₀ (powerSeed s y x) (Real.Gamma_pos_of_pos hs).ne').symm

/-- The exact Gaussian Fourier fiber in the period-one convention.
The negative sign and 2*pi frequency are supplied explicitly. This is
valid for all integer modes, and in particular for nonzero modes. -/
theorem gaussian_integer_fourier_fiber {t : ℝ} (ht : 0 < t) (n : ℤ) :
    (∫ x : ℝ,
      Complex.exp (-(2 * (Real.pi : ℂ) * (n : ℂ)) * Complex.I * (x : ℂ)) *
        Complex.exp (-(t : ℂ) * (x : ℂ) ^ 2)) =
      ((Real.pi : ℂ) / (t : ℂ)) ^ (1 / 2 : ℂ) *
        Complex.exp (-((Real.pi : ℂ) ^ 2 * (n : ℂ) ^ 2) / (t : ℂ)) := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have h := fourierIntegral_gaussian
    (b := (t : ℂ)) (by simpa only [Complex.ofReal_re] using ht)
    (-(2 * (Real.pi : ℂ) * (n : ℂ)))
  calc
    _ = ∫ x : ℝ,
        Complex.exp (Complex.I * (-(2 * (Real.pi : ℂ) * (n : ℂ))) * (x : ℂ)) *
          Complex.exp (-(t : ℂ) * (x : ℂ) ^ 2) := by
      apply integral_congr_ae
      filter_upwards [] with x
      congr 2
      ring
    _ = _ := by
      rw [h]
      congr 2
      field_simp [htC]
      <;> ring

end

end ImbalancedChen.Part3.PowerSeedGaussianLaplace
