import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Independent Gamma algebra for the prospective Mellin multiplier of the
literal J_{+/-2it} kernel. The actual generalJ source uses order nu, and its
native spectral kernel uses exactly the two orders +/-2*i*t and i times
their difference divided by sinh(pi*t). Accordingly the classical J-ratio
has the shifts (s+nu)/2 and (2-s+nu)/2, specialized here without rescaling t.

Reflection derives the exact i and 2^s/pi factors. This file DOES NOT prove
or assume that any actual J Mellin integral equals the Gamma ratio below.
That transform identification and the automorphic normalization remain OPEN.
No held Mellin-convergence module is imported or used.
-/

namespace ImbalancedChen.Part3.JMellinGammaParity20261026b

noncomputable section
open Complex

/-- Prospective general-order Gamma ratio; not a definition of an actual
Mellin transform. -/
def jGammaRatio (s nu : ℂ) : ℂ :=
  (2 : ℂ) ^ (s - 1) * Gamma ((s + nu) / 2) / Gamma ((2 - s + nu) / 2)

def jImaginaryGammaRatio (s : ℂ) (t : ℝ) : ℂ :=
  (2 : ℂ) ^ (s - 1) * Gamma (s / 2 + I * (t : ℂ)) /
    Gamma (1 - s / 2 + I * (t : ℂ))

theorem jGammaRatio_order_two_I (s : ℂ) (t : ℝ) :
    jGammaRatio s (2 * I * (t : ℂ)) = jImaginaryGammaRatio s t := by
  have h1 : (s + 2 * I * (t : ℂ)) / 2 = s / 2 + I * (t : ℂ) := by ring
  have h2 : (2 - s + 2 * I * (t : ℂ)) / 2 = 1 - s / 2 + I * (t : ℂ) := by ring
  simp only [jGammaRatio, jImaginaryGammaRatio, h1, h2]

/-- The candidate continuous multiplier, with the normalization obtained
from reflection rather than imposed as an actual transform identity. -/
def jGammaMultiplier (s : ℂ) (t : ℝ) : ℂ :=
  (2 : ℂ) ^ s / (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * s / 2) *
    Gamma (s / 2 + I * (t : ℂ)) * Gamma (s / 2 - I * (t : ℂ))

private theorem inverseGamma_one_sub {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    (Gamma (1 - z))⁻¹ = Gamma z * Complex.sin ((Real.pi : ℂ) * z) /
      (Real.pi : ℂ) := by
  have hgz : Gamma z ≠ 0 := Gamma_ne_zero_of_re_pos hz0
  have hg1 : Gamma (1 - z) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp only [Complex.sub_re, Complex.one_re]
    linarith)
  have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
    intro hh
    have h := Gamma_mul_Gamma_one_sub z
    rw [hh, div_zero] at h
    exact mul_ne_zero hgz hg1 h
  have href : Gamma z * Gamma (1 - z) * Complex.sin ((Real.pi : ℂ) * z) =
      (Real.pi : ℂ) :=
    (eq_div_iff hsin).1 (Gamma_mul_Gamma_one_sub z)
  apply (eq_div_iff (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).2
  calc
    (Gamma (1 - z))⁻¹ * (Real.pi : ℂ) =
        (Gamma (1 - z))⁻¹ *
          (Gamma z * Gamma (1 - z) * Complex.sin ((Real.pi : ℂ) * z)) := by rw [href]
    _ = Gamma z * Complex.sin ((Real.pi : ℂ) * z) := by
      field_simp [hg1] <;> ring

theorem gammaRatio_reflection {a b : ℂ} (hb0 : 0 < b.re) (hb1 : b.re < 1) :
    Gamma a / Gamma (1 - b) =
      Gamma a * Gamma b * Complex.sin ((Real.pi : ℂ) * b) / (Real.pi : ℂ) := by
  rw [div_eq_mul_inv, inverseGamma_one_sub hb0 hb1]
  ring

private theorem imaginary_shift_re (s : ℂ) (t : ℝ) :
    (s / 2 + I * (t : ℂ)).re = s.re / 2 := by simp

private theorem imaginary_minus_shift_re (s : ℂ) (t : ℝ) :
    (s / 2 - I * (t : ℂ)).re = s.re / 2 := by simp

theorem jImaginaryGammaRatio_reflection {s : ℂ}
    (hs0 : 0 < s.re) (hs2 : s.re < 2) (t : ℝ) :
    jImaginaryGammaRatio s t =
      (2 : ℂ) ^ (s - 1) * Gamma (s / 2 + I * (t : ℂ)) *
        Gamma (s / 2 - I * (t : ℂ)) *
          Complex.sin ((Real.pi : ℂ) * (s / 2 - I * (t : ℂ))) / (Real.pi : ℂ) := by
  have h0 : 0 < (s / 2 - I * (t : ℂ)).re := by
    rw [imaginary_minus_shift_re]
    linarith
  have h1 : (s / 2 - I * (t : ℂ)).re < 1 := by
    rw [imaginary_minus_shift_re]
    linarith
  have he : 1 - s / 2 + I * (t : ℂ) = 1 - (s / 2 - I * (t : ℂ)) := by ring
  rw [jImaginaryGammaRatio, he, mul_div_assoc, gammaRatio_reflection h0 h1]
  ring

theorem I_mul_sine_order_difference (s : ℂ) (t : ℝ) :
    I * (Complex.sin ((Real.pi : ℂ) * (s / 2 - I * (t : ℂ))) -
      Complex.sin ((Real.pi : ℂ) * (s / 2 + I * (t : ℂ)))) =
      2 * Complex.cos ((Real.pi : ℂ) * s / 2) * (Real.sinh (Real.pi * t) : ℂ) := by
  have hsin : Complex.sin ((Real.pi : ℂ) * (I * (t : ℂ))) =
      (Real.sinh (Real.pi * t) : ℂ) * I := by
    have he : (Real.pi : ℂ) * (I * (t : ℂ)) =
        ((Real.pi * t : ℝ) : ℂ) * I := by push_cast; ring
    rw [he, Complex.sin_mul_I, ← Complex.ofReal_sinh]
  rw [show (Real.pi : ℂ) * (s / 2 - I * (t : ℂ)) =
      (Real.pi : ℂ) * s / 2 - (Real.pi : ℂ) * (I * (t : ℂ)) by ring,
    show (Real.pi : ℂ) * (s / 2 + I * (t : ℂ)) =
      (Real.pi : ℂ) * s / 2 + (Real.pi : ℂ) * (I * (t : ℂ)) by ring,
    Complex.sin_sub, Complex.sin_add, hsin]
  calc
    I * (Complex.sin ((Real.pi : ℂ) * s / 2) *
        Complex.cos ((Real.pi : ℂ) * (I * (t : ℂ))) -
        Complex.cos ((Real.pi : ℂ) * s / 2) *
          ((Real.sinh (Real.pi * t) : ℂ) * I) -
        (Complex.sin ((Real.pi : ℂ) * s / 2) *
          Complex.cos ((Real.pi : ℂ) * (I * (t : ℂ))) +
          Complex.cos ((Real.pi : ℂ) * s / 2) *
            ((Real.sinh (Real.pi * t) : ℂ) * I))) =
      -(2 * (I * I) * Complex.cos ((Real.pi : ℂ) * s / 2) *
        (Real.sinh (Real.pi * t) : ℂ)) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

/-- Division-free identity valid also at t=0. This fixes the exact i sign
and the extra factor two from the two opposite J orders. -/
theorem jGammaRatio_odd_normalization {s : ℂ}
    (hs0 : 0 < s.re) (hs2 : s.re < 2) (t : ℝ) :
    I * (jImaginaryGammaRatio s t - jImaginaryGammaRatio s (-t)) =
      (Real.sinh (Real.pi * t) : ℂ) * jGammaMultiplier s t := by
  have hp := jImaginaryGammaRatio_reflection hs0 hs2 t
  have hn := jImaginaryGammaRatio_reflection hs0 hs2 (-t)
  simp only [Complex.ofReal_neg, mul_neg, sub_neg_eq_add] at hn
  have hpow : (2 : ℂ) ^ (s - 1) * 2 = (2 : ℂ) ^ s := by
    simpa using (Complex.cpow_add (s - 1) 1 (by norm_num : (2 : ℂ) ≠ 0)).symm
  calc
    I * (jImaginaryGammaRatio s t - jImaginaryGammaRatio s (-t)) =
        ((2 : ℂ) ^ (s - 1) * Gamma (s / 2 + I * (t : ℂ)) *
          Gamma (s / 2 - I * (t : ℂ)) / (Real.pi : ℂ)) *
            (I * (Complex.sin ((Real.pi : ℂ) * (s / 2 - I * (t : ℂ))) -
              Complex.sin ((Real.pi : ℂ) * (s / 2 + I * (t : ℂ))))) := by
      rw [hp, hn]
      ring
    _ = (((2 : ℂ) ^ (s - 1) * 2) / (Real.pi : ℂ) *
        Complex.cos ((Real.pi : ℂ) * s / 2) * Gamma (s / 2 + I * (t : ℂ)) *
          Gamma (s / 2 - I * (t : ℂ))) * (Real.sinh (Real.pi * t) : ℂ) := by
      rw [I_mul_sine_order_difference]
      ring
    _ = (Real.sinh (Real.pi * t) : ℂ) * jGammaMultiplier s t := by
      rw [hpow]
      unfold jGammaMultiplier
      ring

theorem jGammaRatio_quotient_eq {s : ℂ}
    (hs0 : 0 < s.re) (hs2 : s.re < 2) {t : ℝ} (ht : t ≠ 0) :
    I * (jImaginaryGammaRatio s t - jImaginaryGammaRatio s (-t)) /
      (Real.sinh (Real.pi * t) : ℂ) = jGammaMultiplier s t := by
  have hd : (Real.sinh (Real.pi * t) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero ht))
  rw [jGammaRatio_odd_normalization hs0 hs2]
  exact mul_div_cancel_left₀ _ hd

end
end ImbalancedChen.Part3.JMellinGammaParity20261026b
