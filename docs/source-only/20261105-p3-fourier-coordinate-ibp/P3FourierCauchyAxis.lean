import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
P3.6 / MANUSCRIPT-INTERNAL / SOURCE_ONLY / UNCOMPILED.
The elementary ONE-AXIS Cauchy Fourier majorant in the exact physical
frequency xi = 2*pi*eta convention of manuscript (F).

This is not a claim of multidimensional Fubini, uniform original W_T
admissibility, arithmetic modulus error, or the full H-box tail.
The integral identities use named lemmas from PINNED Mathlib:
  integrable_inv_one_add_sq, integral_univ_inv_one_add_sq,
  integral_Iic_inv_one_add_sq, integral_Ioi_inv_one_add_sq,
  Measure.integral_comp_mul_left, Real.arctan_neg,
  Real.arctan_le_arctan_iff, Real.arctan_lt_pi_div_two.
No research distribution statement is assumed.
-/

namespace ImbalancedChen.P3FourierCauchyAxis
noncomputable section
open MeasureTheory
open scoped Real

/-- The scalar factor in the physical-frequency product decay. -/
def axisKernel (xi : ℝ) : ℝ := (1 + xi ^ 2)⁻¹

/-- The ONE-axis kernel is genuinely Lebesgue-integrable. -/
theorem axisKernel_integrable : Integrable axisKernel := by
  simpa only [axisKernel] using integrable_inv_one_add_sq

/-- Exact unscaled Cauchy mass, including its pi normalization. -/
theorem axisKernel_full_mass : (∫ xi : ℝ, axisKernel xi) = Real.pi := by
  simpa only [axisKernel] using integral_univ_inv_one_add_sq

/-- Mathlib uses eta with a 2*pi phase. The Fourier integration variable
has mass 1/2 per coordinate, NOT pi and NOT one. -/
theorem axisKernel_mathlib_mass :
    (∫ eta : ℝ, axisKernel (2 * Real.pi * eta)) = (1 / 2 : ℝ) := by
  have h := Measure.integral_comp_mul_left axisKernel (2 * Real.pi)
  have hpi : 0 < (2 * Real.pi : ℝ) := by positivity
  rw [axisKernel_full_mass] at h
  rw [abs_of_pos (inv_pos.mpr hpi), smul_eq_mul] at h
  have hmass :
      (∫ eta : ℝ, axisKernel (2 * Real.pi * eta)) =
        (2 * Real.pi)⁻¹ * Real.pi := h
  calc
    _ = (2 * Real.pi)⁻¹ * Real.pi := hmass
    _ = 1 / 2 := by
      have hne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      field_simp
      <;> ring

/-- Left and right physical-frequency tails, counted separately to avoid
an unproved measure-union identity. The boundary at -H is harmless. -/
def axisPairTail (H : ℝ) : ℝ :=
  (∫ xi in Set.Iic (-H), axisKernel xi) +
  (∫ xi in Set.Ioi H, axisKernel xi)

/-- Exact left/right primitive from the pinned arctangent integral. -/
theorem axisPairTail_exact (H : ℝ) :
    axisPairTail H = 2 * (Real.pi / 2 - Real.arctan H) := by
  unfold axisPairTail axisKernel
  rw [integral_Iic_inv_one_add_sq, integral_Ioi_inv_one_add_sq]
  rw [Real.arctan_neg]
  ring

/-- The separated-axis tails are nonnegative, including H=0. -/
theorem axisPairTail_nonneg (H : ℝ) : 0 ≤ axisPairTail H := by
  rw [axisPairTail_exact]
  have h := Real.arctan_lt_pi_div_two H
  linarith

/-- Widening the physical-frequency window cannot increase the tail
(the estimate here is exact, not a postulated Fourier-tail majorant). -/
theorem axisPairTail_antitone {H K : ℝ} (hHK : H ≤ K) :
    axisPairTail K ≤ axisPairTail H := by
  rw [axisPairTail_exact, axisPairTail_exact]
  have ha : Real.arctan H ≤ Real.arctan K :=
    Real.arctan_le_arctan_iff.mpr hHK
  linarith

end
end ImbalancedChen.P3FourierCauchyAxis
