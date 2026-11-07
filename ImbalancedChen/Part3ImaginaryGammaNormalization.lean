import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
# Actual imaginary-parameter Gamma normalization

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

These constants follow from pinned Mathlib's Gamma reflection, recurrence,
and conjugation theorems. No Gamma identity or spectral estimate is assumed.
The actual imaginaryOrderK source uses cos(2*t*u), hence represents K_{2it};
its Mellin Gamma factors have parameters s/2 +/- it. The identities here
use that literal t, without replacing it silently by 2*t.

The expression pi*t/sinh(pi*t) is only equal to the shifted Gamma norm
away from zero. Its raw field value at zero is zero; the continuous
normalization below explicitly assigns the correct removable value one.
No KL Plancherel measure, automorphic spectral measure, or P3 saving is
constructed or assumed by this local special-function calculation.
-/

namespace ImbalancedChen.Part3.ImaginaryGammaNormalization20261025a

noncomputable section
open Complex Filter Topology

/-- Reflection and recurrence at it, with the literal imaginary parameter. -/
theorem gamma_mul_gamma_neg_mul_I (t : ℝ) (ht : t ≠ 0) :
    Complex.Gamma ((t : ℂ) * I) * Complex.Gamma (-((t : ℂ) * I)) =
      ((Real.pi / (t * Real.sinh (Real.pi * t)) : ℝ) : ℂ) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have hz : (t : ℂ) * I ≠ 0 := mul_ne_zero htC Complex.I_ne_zero
  have hs : Real.sinh (Real.pi * t) ≠ 0 :=
    Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero ht)
  have hsC : (Real.sinh (Real.pi * t) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hs
  have hrec : Complex.Gamma (1 - (t : ℂ) * I) =
      (-((t : ℂ) * I)) * Complex.Gamma (-((t : ℂ) * I)) := by
    simpa only [sub_eq_add_neg, add_comm] using
      Complex.Gamma_add_one (-((t : ℂ) * I)) (neg_ne_zero.mpr hz)
  have hsin : Complex.sin ((Real.pi : ℂ) * ((t : ℂ) * I)) =
      (Real.sinh (Real.pi * t) : ℂ) * I := by
    rw [← mul_assoc, ← Complex.ofReal_mul, Complex.sin_mul_I,
      ← Complex.ofReal_sinh]
  have href := Complex.Gamma_mul_Gamma_one_sub ((t : ℂ) * I)
  rw [hrec, hsin] at href
  rw [Complex.ofReal_div, Complex.ofReal_mul]
  apply mul_left_cancel₀ (neg_ne_zero.mpr hz)
  calc
    (-((t : ℂ) * I)) *
        (Complex.Gamma ((t : ℂ) * I) * Complex.Gamma (-((t : ℂ) * I))) =
      Complex.Gamma ((t : ℂ) * I) *
        ((-((t : ℂ) * I)) * Complex.Gamma (-((t : ℂ) * I))) := by ring
    _ = (Real.pi : ℂ) / ((Real.sinh (Real.pi * t) : ℂ) * I) := href
    _ = (-((t : ℂ) * I)) *
        ((Real.pi : ℂ) / ((t : ℂ) * (Real.sinh (Real.pi * t) : ℂ))) := by
      simp only [div_eq_mul_inv, mul_inv, Complex.inv_I]
      field_simp [htC, hsC] <;> ring

/-- The conjugate pair is the squared norm, with the exact real constant. -/
theorem norm_gamma_mul_I_sq (t : ℝ) (ht : t ≠ 0) :
    ‖Complex.Gamma ((t : ℂ) * I)‖ ^ 2 =
      Real.pi / (t * Real.sinh (Real.pi * t)) := by
  have hconj : Complex.Gamma (-((t : ℂ) * I)) =
      conj (Complex.Gamma ((t : ℂ) * I)) := by
    simpa using Complex.Gamma_conj ((t : ℂ) * I)
  have h := gamma_mul_gamma_neg_mul_I t ht
  rw [hconj, Complex.mul_conj'] at h
  exact_mod_cast h

/-- Recurrence gives the normalization regular at zero, away from its
removable point. There is no lost factor two from the K_{2it} convention. -/
theorem norm_gamma_one_add_mul_I_sq (t : ℝ) (ht : t ≠ 0) :
    ‖Complex.Gamma (1 + (t : ℂ) * I)‖ ^ 2 =
      Real.pi * t / Real.sinh (Real.pi * t) := by
  have hz : (t : ℂ) * I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) Complex.I_ne_zero
  have hs : Real.sinh (Real.pi * t) ≠ 0 :=
    Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero ht)
  rw [show (1 : ℂ) + (t : ℂ) * I = (t : ℂ) * I + 1 by ring,
    Complex.Gamma_add_one _ hz, norm_mul, mul_pow,
    norm_mul, Complex.norm_real, Complex.norm_I]
  simp only [mul_one, Real.norm_eq_abs, sq_abs]
  rw [norm_gamma_mul_I_sq t ht]
  field_simp [ht, hs] <;> ring

/-- The removable zero is assigned its limiting value explicitly. -/
def normalizedImaginaryGamma (t : ℝ) : ℝ :=
  if t = 0 then 1 else Real.pi * t / Real.sinh (Real.pi * t)

theorem normalizedImaginaryGamma_eq_norm_sq (t : ℝ) :
    normalizedImaginaryGamma t = ‖Complex.Gamma (1 + (t : ℂ) * I)‖ ^ 2 := by
  by_cases ht : t = 0
  · subst t
    simp [normalizedImaginaryGamma]
  · rw [normalizedImaginaryGamma, if_neg ht]
    exact (norm_gamma_one_add_mul_I_sq t ht).symm

/-- The shifted Gamma function proves the actual zero normalization, rather
than assigning a limiting value to the raw quotient without justification. -/
theorem tendsto_normalizedImaginaryGamma_zero :
    Tendsto normalizedImaginaryGamma (𝓝 (0 : ℝ)) (𝓝 1) := by
  have hpath : Tendsto (fun t : ℝ => (1 : ℂ) + (t : ℂ) * I)
      (𝓝 0) (𝓝 1) := by
    simpa using
      (show Continuous (fun t : ℝ => (1 : ℂ) + (t : ℂ) * I) from by fun_prop).tendsto 0
  have hGamma := Complex.continuousAt_Gamma_one.tendsto.comp hpath
  have hnorm := hGamma.norm.pow 2
  have heq : normalizedImaginaryGamma =
      fun t : ℝ => ‖Complex.Gamma (1 + (t : ℂ) * I)‖ ^ 2 :=
    funext normalizedImaginaryGamma_eq_norm_sq
  rw [heq]
  simpa only [Complex.Gamma_one, norm_one, one_pow] using hnorm

/-- The unmodified quotient has the claimed punctured limit, despite its
different field value at the origin. -/
theorem tendsto_pi_mul_div_sinh_zero :
    Tendsto (fun t : ℝ => Real.pi * t / Real.sinh (Real.pi * t))
      (𝓝[≠] 0) (𝓝 1) := by
  have h := tendsto_normalizedImaginaryGamma_zero.mono_left nhdsWithin_le_nhds
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht
  simp only [normalizedImaginaryGamma, if_neg ht0]

end
end ImbalancedChen.Part3.ImaginaryGammaNormalization20261025a
