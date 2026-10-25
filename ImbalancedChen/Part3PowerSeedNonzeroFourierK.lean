import ImbalancedChen.Part3PowerSeedFourierLaplaceFubini
import ImbalancedChen.Part3RealOrderKPositiveLaplace

/-!
# Nonzero Fourier coefficient of the real power seed, with actual K

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

For real s>1/2, y>0 and integer n!=0, the period-one Fourier transform
of y^s/(x^2+y^2)^s is evaluated using the proved Gaussian/Laplace Fubini
identity and the actual cosh-Laplace realOrderK definition. The coefficient
is 2*pi^s/Gamma(s) * |n|^(s-1/2) * sqrt(y), and the K argument is
2*pi*|n|*y. No Fourier or Bessel evaluation is a hypothesis.
-/

namespace ImbalancedChen.Part3.PowerSeedNonzeroFourierK

noncomputable section
open Set MeasureTheory
open PowerSeedGaussianLaplace PowerSeedFourierLaplaceFubini
open RealOrderKPositiveLaplace RealOrderKExceptionalSourceOnly

theorem laplace_fourier_integrand_eq_real (s y : ℝ) (n : ℤ)
    {t : ℝ} (ht : 0 < t) :
    (laplaceAmplitude s y t : ℂ) *
      (((Real.pi : ℂ) / (t : ℂ)) ^ (1 / 2 : ℂ) *
        Complex.exp (-((Real.pi : ℂ) ^ 2 * (n : ℂ) ^ 2) / (t : ℂ))) =
      (((y ^ s * Real.sqrt Real.pi) *
        (t ^ (s - 3 / 2) *
          Real.exp (-(y ^ 2 * t) - (Real.pi ^ 2 * (n : ℝ) ^ 2) / t))) : ℝ) := by
  have hsqrt : ((Real.pi : ℂ) / (t : ℂ)) ^ (1 / 2 : ℂ) =
      (Real.sqrt (Real.pi / t) : ℂ) := by
    rw [Real.sqrt_eq_rpow,
      Complex.ofReal_cpow (div_nonneg Real.pi_pos.le ht.le)]
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  have hexp : Complex.exp (-((Real.pi : ℂ) ^ 2 * (n : ℂ) ^ 2) / (t : ℂ)) =
      (Real.exp (-(Real.pi ^ 2 * (n : ℝ) ^ 2) / t) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
  rw [hsqrt, hexp]
  have hreal : laplaceAmplitude s y t *
      (Real.sqrt (Real.pi / t) * Real.exp (-(Real.pi ^ 2 * (n : ℝ) ^ 2) / t)) =
      (y ^ s * Real.sqrt Real.pi) *
        (t ^ (s - 3 / 2) *
          Real.exp (-(y ^ 2 * t) - (Real.pi ^ 2 * (n : ℝ) ^ 2) / t)) := by
    rw [← mul_assoc, laplaceAmplitude_mul_gaussian_integral s y ht]
    have he : -(y ^ 2 * t) - (Real.pi ^ 2 * (n : ℝ) ^ 2) / t =
        -(y ^ 2 * t) + (-(Real.pi ^ 2 * (n : ℝ) ^ 2) / t) := by ring
    rw [he, Real.exp_add]
    ring
  exact_mod_cast hreal

theorem reciprocal_gaussian_integral (s : ℝ) {y : ℝ} (hy : 0 < y)
    {n : ℤ} (hn : n ≠ 0) :
    (∫ t in Ioi (0 : ℝ), t ^ (s - 3 / 2) *
      Real.exp (-(y ^ 2 * t) - (Real.pi ^ 2 * (n : ℝ) ^ 2) / t)) =
      2 * (Real.pi * |(n : ℝ)| / y) ^ (s - 1 / 2) *
        realOrderK (s - 1 / 2) (2 * Real.pi * |(n : ℝ)| * y) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have ha : 0 < |(n : ℝ)| := abs_pos.mpr hnR
  have hc : 0 < Real.pi * |(n : ℝ)| / y := div_pos (mul_pos Real.pi_pos ha) hy
  have hq : 0 < 2 * Real.pi * |(n : ℝ)| * y := by positivity
  have hA : (2 * Real.pi * |(n : ℝ)| * y) /
      (2 * (Real.pi * |(n : ℝ)| / y)) = y ^ 2 := by
    field_simp [Real.pi_ne_zero, ha.ne', hy.ne']
    <;> ring
  have hB : (2 * Real.pi * |(n : ℝ)| * y) *
      (Real.pi * |(n : ℝ)| / y) / 2 = Real.pi ^ 2 * (n : ℝ) ^ 2 := by
    rw [← sq_abs (n : ℝ)]
    field_simp [hy.ne']
    <;> ring
  have h := scaled_positive_laplace_integral (s - 1 / 2) hq hc
  have he : s - 1 / 2 - 1 = s - 3 / 2 := by ring
  simpa only [he, hA, hB, neg_mul] using h

theorem power_seed_fourier_constant (s : ℝ) {y a : ℝ}
    (hy : 0 < y) (ha : 0 < a) :
    y ^ s * Real.sqrt Real.pi * (Real.pi * a / y) ^ (s - 1 / 2) =
      Real.pi ^ s * a ^ (s - 1 / 2) * Real.sqrt y := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    Real.div_rpow (mul_nonneg Real.pi_pos.le ha.le) hy.le,
    Real.mul_rpow Real.pi_pos.le ha.le]
  calc
    _ = (Real.pi ^ (1 / 2 : ℝ) * Real.pi ^ (s - 1 / 2)) *
        a ^ (s - 1 / 2) * (y ^ s / y ^ (s - 1 / 2)) := by ring
    _ = Real.pi ^ ((1 / 2 : ℝ) + (s - 1 / 2)) * a ^ (s - 1 / 2) *
        y ^ (s - (s - 1 / 2)) := by
      rw [Real.rpow_add Real.pi_pos, Real.rpow_sub hy]
    _ = _ := by
      rw [show (1 / 2 : ℝ) + (s - 1 / 2) = s by ring,
        show s - (s - 1 / 2) = (1 / 2 : ℝ) by ring]

/-- The exact nonzero period-one Fourier coefficient of the power seed,
using the actual realOrderK cosh integral, for real s>1/2. -/
theorem powerSeed_nonzero_fourier_actualK {s y : ℝ}
    (hs : (1 / 2 : ℝ) < s) (hy : 0 < y) {n : ℤ} (hn : n ≠ 0) :
    (∫ x : ℝ, fourierPhase n x * (powerSeed s y x : ℂ)) =
      ((2 * Real.pi ^ s / Real.Gamma s * |(n : ℝ)| ^ (s - 1 / 2) * Real.sqrt y *
        realOrderK (s - 1 / 2) (2 * Real.pi * |(n : ℝ)| * y) : ℝ) : ℂ) := by
  rw [powerSeed_fourier_eq_laplace hs hy n]
  have hreal : (∫ t in Ioi (0 : ℝ), (laplaceAmplitude s y t : ℂ) *
      (((Real.pi : ℂ) / (t : ℂ)) ^ (1 / 2 : ℂ) *
        Complex.exp (-((Real.pi : ℂ) ^ 2 * (n : ℂ) ^ 2) / (t : ℂ)))) =
      ((y ^ s * Real.sqrt Real.pi) *
        (∫ t in Ioi (0 : ℝ), t ^ (s - 3 / 2) *
          Real.exp (-(y ^ 2 * t) - (Real.pi ^ 2 * (n : ℝ) ^ 2) / t)) : ℝ) := by
    calc
      _ = ∫ t in Ioi (0 : ℝ),
          (((y ^ s * Real.sqrt Real.pi) * (t ^ (s - 3 / 2) *
            Real.exp (-(y ^ 2 * t) - (Real.pi ^ 2 * (n : ℝ) ^ 2) / t))) : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact laplace_fourier_integrand_eq_real s y n ht
      _ = _ := by rw [integral_ofReal, integral_const_mul]
  rw [hreal, reciprocal_gaussian_integral s hy hn]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hconst := power_seed_fourier_constant s hy (abs_pos.mpr hnR)
  have halgebra :
      (y ^ s * Real.sqrt Real.pi) *
        (2 * (Real.pi * |(n : ℝ)| / y) ^ (s - 1 / 2) *
          realOrderK (s - 1 / 2) (2 * Real.pi * |(n : ℝ)| * y)) / Real.Gamma s =
      2 * Real.pi ^ s / Real.Gamma s * |(n : ℝ)| ^ (s - 1 / 2) * Real.sqrt y *
        realOrderK (s - 1 / 2) (2 * Real.pi * |(n : ℝ)| * y) := by
    calc
      _ = 2 * (y ^ s * Real.sqrt Real.pi *
          (Real.pi * |(n : ℝ)| / y) ^ (s - 1 / 2)) *
          realOrderK (s - 1 / 2) (2 * Real.pi * |(n : ℝ)| * y) / Real.Gamma s := by ring
      _ = _ := by rw [hconst]; ring
  exact_mod_cast halgebra

end

end ImbalancedChen.Part3.PowerSeedNonzeroFourierK
