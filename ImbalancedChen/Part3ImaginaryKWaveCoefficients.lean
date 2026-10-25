import ImbalancedChen.Part3ImaginaryGammaNormalization
import ImbalancedChen.Part3GeneralIConjugation
import Mathlib.Tactic

/-!
# Actual Gamma wave coefficients and reflection normalization

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The two coefficients are Gamma(i*tau)*2^(i*tau)/2 and its conjugate.
Each travelling-wave coefficient has squared norm pi/(4*tau*sinh(pi*tau)).
The amplitude of the real conjugate-pair oscillation is twice that norm,
so its square is pi/(tau*sinh(pi*tau)). These are distinct normalizations.
No measure or Plancherel theorem follows here from either amplitude.
-/

namespace ImbalancedChen.Part3.ImaginaryKWaveCoefficients20261025a

noncomputable section
open Complex
open ImaginaryGammaNormalization20261025a GeneralIConjugation20261025a

def connectionCoefficient (tau : ℝ) : ℂ :=
  (Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * ((tau : ℂ) * I)))

def waveMinus (tau : ℝ) : ℂ :=
  (Complex.Gamma ((tau : ℂ) * I) / 2) * (2 : ℂ) ^ ((tau : ℂ) * I)

def wavePlus (tau : ℝ) : ℂ :=
  (Complex.Gamma (-((tau : ℂ) * I)) / 2) * (2 : ℂ) ^ (-((tau : ℂ) * I))

def qWaveProfile (tau q : ℝ) : ℂ :=
  (Complex.Gamma ((tau : ℂ) * I) / 2) * (((q / 2 : ℝ) : ℂ) ^ (-((tau : ℂ) * I))) +
  (Complex.Gamma (-((tau : ℂ) * I)) / 2) * (((q / 2 : ℝ) : ℂ) ^ ((tau : ℂ) * I))

def logWaveProfile (tau r : ℝ) : ℂ :=
  waveMinus tau * Complex.exp (-((tau : ℂ) * I) * (r : ℂ)) +
  wavePlus tau * Complex.exp (((tau : ℂ) * I) * (r : ℂ))

def realOscillationAmplitude (tau : ℝ) : ℝ := 2 * ‖waveMinus tau‖
def reflectionCoefficient (tau : ℝ) : ℂ := wavePlus tau / waveMinus tau

/-- Reflection fixes the coefficient of the negative-frequency wave. -/
theorem connectionCoefficient_mul_gamma_minus_inv (tau : ℝ) :
    connectionCoefficient tau * (Complex.Gamma (1 - (tau : ℂ) * I))⁻¹ =
      Complex.Gamma ((tau : ℂ) * I) / 2 := by
  have hG : Complex.Gamma (1 - (tau : ℂ) * I) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp)
  calc
    _ = (Complex.Gamma ((tau : ℂ) * I) *
        Complex.Gamma (1 - (tau : ℂ) * I) / 2) *
          (Complex.Gamma (1 - (tau : ℂ) * I))⁻¹ := by
      rw [Complex.Gamma_mul_Gamma_one_sub]
      unfold connectionCoefficient
      ring
    _ = _ := by field_simp [hG]; ring

/-- The minus sign in the K/I difference supplies the opposite Gamma factor. -/
theorem neg_connectionCoefficient_mul_gamma_plus_inv (tau : ℝ) :
    (-connectionCoefficient tau) * (Complex.Gamma ((tau : ℂ) * I + 1))⁻¹ =
      Complex.Gamma (-((tau : ℂ) * I)) / 2 := by
  have h := connectionCoefficient_mul_gamma_minus_inv (-tau)
  simpa [connectionCoefficient, sub_eq_add_neg, add_comm] using h

theorem conj_waveMinus (tau : ℝ) : conj (waveMinus tau) = wavePlus tau := by
  have hG : conj (Complex.Gamma ((tau : ℂ) * I)) =
      Complex.Gamma (-((tau : ℂ) * I)) := by
    simpa using (Complex.Gamma_conj ((tau : ℂ) * I)).symm
  have hp : conj ((2 : ℂ) ^ ((tau : ℂ) * I)) =
      (2 : ℂ) ^ (-((tau : ℂ) * I)) := by
    simpa using conj_positive_cpow ((tau : ℂ) * I) (x := 2) (by norm_num)
  simp only [waveMinus, wavePlus, map_mul, map_div, hG, hp, map_ofNat]

/-- Positive-base powers retain the exact factors 2^(+/-i*tau). -/
theorem exp_half_cpow (nu : ℂ) (r : ℝ) :
    (((Real.exp r / 2 : ℝ) : ℂ) ^ nu) =
      (2 : ℂ) ^ (-nu) * Complex.exp ((r : ℂ) * nu) := by
  have hb : ((Real.exp r / 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_pos (Real.exp_pos r) (by norm_num)).ne'
  have hlog : Complex.log ((Real.exp r / 2 : ℝ) : ℂ) =
      (r : ℂ) - Complex.log (2 : ℂ) := by
    rw [← Complex.ofReal_log (div_pos (Real.exp_pos r) (by norm_num)).le,
      Real.log_div (Real.exp_ne_zero r) (by norm_num), Real.log_exp,
      Complex.ofReal_sub, Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Complex.cpow_def_of_ne_zero hb,
    Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0),
    ← Complex.exp_add, hlog]
  congr 1
  ring

theorem qWaveProfile_exp_eq (tau r : ℝ) :
    qWaveProfile tau (Real.exp r) = logWaveProfile tau r := by
  simp only [qWaveProfile, logWaveProfile, waveMinus, wavePlus, exp_half_cpow, neg_neg]
  simp only [mul_comm (r : ℂ) ((tau : ℂ) * I),
    mul_comm (r : ℂ) (-((tau : ℂ) * I))]
  ring

/-- The two-wave profile is twice a real part, justifying the real
oscillation amplitude normalization rather than a travelling-wave norm. -/
theorem logWaveProfile_eq_two_re (tau r : ℝ) :
    logWaveProfile tau r =
      ((2 * (waveMinus tau * Complex.exp (-((tau : ℂ) * I) * (r : ℂ))).re : ℝ) : ℂ) := by
  have hc : conj (waveMinus tau * Complex.exp (-((tau : ℂ) * I) * (r : ℂ))) =
      wavePlus tau * Complex.exp (((tau : ℂ) * I) * (r : ℂ)) := by
    simp [map_mul, ← Complex.exp_conj, conj_waveMinus]
  rw [logWaveProfile, ← hc, Complex.add_conj]

theorem norm_waveMinus (tau : ℝ) :
    ‖waveMinus tau‖ = ‖Complex.Gamma ((tau : ℂ) * I)‖ / 2 := by
  have hp : ‖(2 : ℂ) ^ ((tau : ℂ) * I)‖ = 1 := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)
      ((tau : ℂ) * I)
  rw [waveMinus, norm_mul, norm_div, hp]
  norm_num

theorem realOscillationAmplitude_eq_gamma_norm (tau : ℝ) :
    realOscillationAmplitude tau = ‖Complex.Gamma ((tau : ℂ) * I)‖ := by
  rw [realOscillationAmplitude, norm_waveMinus]
  ring

theorem realOscillationAmplitude_sq (tau : ℝ) (htau : tau ≠ 0) :
    realOscillationAmplitude tau ^ 2 = Real.pi / (tau * Real.sinh (Real.pi * tau)) := by
  rw [realOscillationAmplitude_eq_gamma_norm, norm_gamma_mul_I_sq tau htau]

theorem norm_waveMinus_sq (tau : ℝ) (htau : tau ≠ 0) :
    ‖waveMinus tau‖ ^ 2 = Real.pi / (4 * tau * Real.sinh (Real.pi * tau)) := by
  rw [norm_waveMinus, div_pow, norm_gamma_mul_I_sq tau htau]
  ring

theorem norm_wavePlus_sq (tau : ℝ) (htau : tau ≠ 0) :
    ‖wavePlus tau‖ ^ 2 = Real.pi / (4 * tau * Real.sinh (Real.pi * tau)) := by
  rw [← conj_waveMinus, Complex.norm_conj]
  exact norm_waveMinus_sq tau htau

theorem waveMinus_ne_zero (tau : ℝ) (htau : tau ≠ 0) : waveMinus tau ≠ 0 := by
  have hs : Real.sinh (Real.pi * tau) ≠ 0 :=
    Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero htau)
  have hprod : Complex.Gamma ((tau : ℂ) * I) * Complex.Gamma (-((tau : ℂ) * I)) ≠ 0 := by
    rw [gamma_mul_gamma_neg_mul_I tau htau]
    exact Complex.ofReal_ne_zero.mpr (div_ne_zero Real.pi_ne_zero (mul_ne_zero htau hs))
  have hG := (mul_ne_zero_iff.mp hprod).1
  exact mul_ne_zero (div_ne_zero hG (by norm_num))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num : (2 : ℂ) ≠ 0)))

/-- Actual coefficient ratio; its unit modulus is a Gamma/conjugation
calculation, with no spectral normalization premise. -/
theorem norm_reflectionCoefficient (tau : ℝ) (htau : tau ≠ 0) :
    ‖reflectionCoefficient tau‖ = 1 := by
  rw [reflectionCoefficient, norm_div, ← conj_waveMinus, Complex.norm_conj]
  exact div_self (norm_ne_zero_iff.mpr (waveMinus_ne_zero tau htau))

/-- Explicit conversion to the original K_(2*i*t) parameter. -/
theorem realOscillationAmplitude_two_mul_sq (t : ℝ) (ht : t ≠ 0) :
    realOscillationAmplitude (2 * t) ^ 2 =
      Real.pi / (2 * t * Real.sinh (2 * Real.pi * t)) := by
  rw [realOscillationAmplitude_sq (2 * t) (mul_ne_zero (by norm_num) ht)]
  rw [show Real.pi * (2 * t) = 2 * Real.pi * t by ring]

/-- Each original travelling coefficient has one fourth of the real
oscillation amplitude squared; tau=2*t contributes the further factor two. -/
theorem norm_waveMinus_two_mul_sq (t : ℝ) (ht : t ≠ 0) :
    ‖waveMinus (2 * t)‖ ^ 2 = Real.pi / (8 * t * Real.sinh (2 * Real.pi * t)) := by
  rw [norm_waveMinus_sq (2 * t) (mul_ne_zero (by norm_num) ht)]
  rw [show Real.pi * (2 * t) = 2 * Real.pi * t by ring]
  ring

theorem norm_wavePlus_two_mul_sq (t : ℝ) (ht : t ≠ 0) :
    ‖wavePlus (2 * t)‖ ^ 2 = Real.pi / (8 * t * Real.sinh (2 * Real.pi * t)) := by
  rw [← conj_waveMinus, Complex.norm_conj]
  exact norm_waveMinus_two_mul_sq t ht

end
end ImbalancedChen.Part3.ImaginaryKWaveCoefficients20261025a
