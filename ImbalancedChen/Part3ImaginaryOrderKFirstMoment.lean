import ImbalancedChen.Part3ImaginaryOrderKMellinGamma
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-!
# Half-shift Gamma normalization and the actual imaginary K first moment

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

Pinned Gamma reflection and conjugation give the half-shift norm for every
real t, including zero. The actual proved Mellin source is then evaluated
at s = 1. Since imaginaryOrderK uses cos(2*t*u), its Mellin Gamma arguments
are 1/2 +/- it and the exact first moment is pi/(2*cosh(pi*t)).

The actual integral and its integrability are conclusions, not premises.
This is an exact special-function normalization only. It does not construct
a KL Plancherel measure or an automorphic spectral measure; those and the
genuine P3 distribution saving remain OPEN.
-/

namespace ImbalancedChen.Part3.ImaginaryOrderKFirstMoment20261025a

noncomputable section
open Complex Set MeasureTheory
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKMellinReduction20261025a
open ImaginaryOrderKMellinGamma20261025a

/-- Reflection on the vertical line through one half. The denominator
never vanishes and the formula includes t = 0 without a special value. -/
theorem gamma_half_add_mul_I_mul_gamma_half_sub_mul_I (t : ℝ) :
    Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * I) *
      Complex.Gamma ((1 / 2 : ℂ) - (t : ℂ) * I) =
        ((Real.pi / Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
  have harg : (Real.pi : ℂ) * ((1 / 2 : ℂ) + (t : ℂ) * I) =
      ((Real.pi / 2 : ℝ) : ℂ) + ((Real.pi * t : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hsin : Complex.sin ((Real.pi : ℂ) * ((1 / 2 : ℂ) + (t : ℂ) * I)) =
      (Real.cosh (Real.pi * t) : ℂ) := by
    rw [harg, Complex.sin_add_mul_I]
    simp only [← Complex.ofReal_sin, ← Complex.ofReal_cos,
      Real.sin_pi_div_two, Real.cos_pi_div_two, Complex.ofReal_one,
      Complex.ofReal_zero, one_mul, zero_mul, add_zero, ← Complex.ofReal_cosh]
  have h := Complex.Gamma_mul_Gamma_one_sub ((1 / 2 : ℂ) + (t : ℂ) * I)
  rw [show (1 : ℂ) - ((1 / 2 : ℂ) + (t : ℂ) * I) =
      (1 / 2 : ℂ) - (t : ℂ) * I by ring, hsin] at h
  simpa only [Complex.ofReal_div] using h

/-- Squared Gamma norm on the half-shift line, valid for all real t. -/
theorem norm_gamma_half_add_mul_I_sq (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) := by
  have hconj : Complex.Gamma ((1 / 2 : ℂ) - (t : ℂ) * I) =
      conj (Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * I)) := by
    simpa [sub_eq_add_neg] using
      Complex.Gamma_conj ((1 / 2 : ℂ) + (t : ℂ) * I)
  have h := gamma_half_add_mul_I_mul_gamma_half_sub_mul_I t
  rw [hconj, Complex.mul_conj'] at h
  exact_mod_cast h

/-- The literal q-first moment exists as a Bochner integral. -/
theorem integrableOn_imaginaryOrderK (t : ℝ) :
    IntegrableOn (imaginaryOrderK t) (Ioi (0 : ℝ)) := by
  simpa only [sub_self, Real.rpow_zero, one_mul] using
    imaginaryOrderK_mellin_integrable t (s := 1) (by norm_num)

/-- Exact first moment for the actual K_{2it} convention. No integral or
Gamma-product estimate is assumed; the s = 1 Mellin evaluation supplies it. -/
theorem integral_imaginaryOrderK_eq_pi_div_two_cosh (t : ℝ) :
    (∫ q in Ioi (0 : ℝ), imaginaryOrderK t q) =
      Real.pi / (2 * Real.cosh (Real.pi * t)) := by
  have hhalf : (2 : ℝ) ^ ((1 : ℝ) - 2) = 1 / 2 := by
    norm_num [Real.rpow_neg_one]
  have hMellin : ((∫ q in Ioi (0 : ℝ), imaginaryOrderK t q) : ℂ) =
      (1 / 2 : ℂ) * Complex.Gamma ((1 / 2 : ℂ) + (t : ℂ) * I) *
        Complex.Gamma ((1 / 2 : ℂ) - (t : ℂ) * I) := by
    simpa only [sub_self, Real.rpow_zero, one_mul, hhalf, mellinA, mellinB,
      Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_ofNat] using
      imaginaryOrderK_mellin_eq_gamma t (s := 1) (by norm_num)
  have hcosh : (Real.cosh (Real.pi * t) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.cosh_pos (Real.pi * t)).ne'
  apply Complex.ofReal_injective
  calc
    ((∫ q in Ioi (0 : ℝ), imaginaryOrderK t q) : ℂ) =
        (1 / 2 : ℂ) * ((Real.pi / Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
      simpa only [mul_assoc, gamma_half_add_mul_I_mul_gamma_half_sub_mul_I] using hMellin
    _ = ((Real.pi / (2 * Real.cosh (Real.pi * t)) : ℝ) : ℂ) := by
      push_cast
      field_simp [hcosh] <;> ring

end
end ImbalancedChen.Part3.ImaginaryOrderKFirstMoment20261025a
