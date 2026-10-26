import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Angular-frequency Plancherel measure and the actual quotient-space unitary

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
The frequency variable is t=2*pi*xi. Its measure is literally dt/(2*pi).
This is ordinary real Fourier analysis; no automorphic completeness or
KL-density identification is asserted.
-/
namespace ImbalancedChen.Part3.AngularFourierUnitary20261026b
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform ENNReal

abbrev RealL2 := Lp (α := ℝ) ℂ 2 volume

def angularMeasure : Measure ℝ :=
  ENNReal.ofReal ((2 * Real.pi)⁻¹) • volume

abbrev AngularL2 := Lp ℂ 2 angularMeasure

private theorem two_pi_ne : 2 * Real.pi ≠ 0 :=
  (mul_pos (by norm_num) Real.pi_pos).ne'

def angularCoordinate : ℝ ≃ᵐ ℝ :=
  (Homeomorph.mulLeft₀ (2 * Real.pi) two_pi_ne).toMeasurableEquiv

@[simp] theorem angularCoordinate_apply (x : ℝ) :
    angularCoordinate x = (2 * Real.pi) * x := rfl

@[simp] theorem angularCoordinate_symm_apply (t : ℝ) :
    angularCoordinate.symm t = t / (2 * Real.pi) := by
  change (2 * Real.pi)⁻¹ * t = t / (2 * Real.pi)
  ring

theorem angularCoordinate_measurePreserving :
    MeasurePreserving angularCoordinate volume angularMeasure := by
  refine ⟨angularCoordinate.measurable, ?_⟩
  change Measure.map (fun x : ℝ => (2 * Real.pi) * x) volume = _
  rw [Real.map_volume_mul_left two_pi_ne]
  simp only [angularMeasure, abs_of_pos (inv_pos.mpr
    (mul_pos (by norm_num) Real.pi_pos))]

theorem angularCoordinate_symm_measurePreserving :
    MeasurePreserving angularCoordinate.symm angularMeasure volume :=
  MeasurePreserving.symm angularCoordinate angularCoordinate_measurePreserving

/-- Integral substitution with the literal dt/(2*pi) measure. -/
theorem angularMeasure_integral (g : ℝ → ℂ) :
    (∫ t, g t ∂angularMeasure) =
      ((2 * Real.pi)⁻¹ : ℝ) • (∫ t, g t) := by
  rw [angularMeasure, integral_smul_measure, ENNReal.toReal_ofReal
    (inv_nonneg.mpr (mul_pos (by norm_num) Real.pi_pos).le)]

theorem angularCoordinate_integral (g : ℝ → ℂ) :
    (∫ x : ℝ, g ((2 * Real.pi) * x)) = ∫ t, g t ∂angularMeasure :=
  angularCoordinate_measurePreserving.integral_comp' g

/-- Pullback by t=2*pi*xi, with surjectivity on actual L2 classes. -/
def angularPullback : AngularL2 ≃ₗᵢ[ℂ] RealL2 where
  toLinearEquiv :=
    { toFun := Lp.compMeasurePreserving angularCoordinate
        angularCoordinate_measurePreserving
      invFun := Lp.compMeasurePreserving angularCoordinate.symm
        angularCoordinate_symm_measurePreserving
      left_inv := by
        intro f
        rw [← Lp.compMeasurePreserving_comp_apply f
          angularCoordinate_measurePreserving angularCoordinate_symm_measurePreserving]
        simpa only [angularCoordinate.self_comp_symm] using
          (Lp.compMeasurePreserving_id_apply f)
      right_inv := by
        intro f
        rw [← Lp.compMeasurePreserving_comp_apply f
          angularCoordinate_symm_measurePreserving angularCoordinate_measurePreserving]
        simpa only [angularCoordinate.symm_comp_self] using
          (Lp.compMeasurePreserving_id_apply f)
      map_add' := (Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) angularCoordinate
        angularCoordinate_measurePreserving).map_add
      map_smul' := (Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) angularCoordinate
        angularCoordinate_measurePreserving).map_smul }
  norm_map' := (Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) angularCoordinate
    angularCoordinate_measurePreserving).norm_map

theorem angularPullback_ae (f : AngularL2) :
    angularPullback f =ᵐ[volume] fun x => f ((2 * Real.pi) * x) :=
  Lp.coeFn_compMeasurePreserving f angularCoordinate_measurePreserving

theorem angularPullback_symm_ae (f : RealL2) :
    angularPullback.symm f =ᵐ[angularMeasure]
      fun t => f (t / (2 * Real.pi)) := by
  simpa only [Function.comp_def, angularCoordinate_symm_apply] using
    (Lp.coeFn_compMeasurePreserving f angularCoordinate_symm_measurePreserving)

/-- Fourier transform in the exp(-i*t*r) convention, onto L2(dt/(2*pi)). -/
def angularFourierUnitary : RealL2 ≃ₗᵢ[ℂ] AngularL2 :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).trans angularPullback.symm

theorem angularFourierUnitary_forward_ae (f : RealL2) :
    angularFourierUnitary f =ᵐ[angularMeasure]
      fun t => (𝓕 f : RealL2) (t / (2 * Real.pi)) :=
  angularPullback_symm_ae (𝓕 f)

theorem angularFourierUnitary_inverse_forward (f : RealL2) :
    angularFourierUnitary.symm (angularFourierUnitary f) = f :=
  angularFourierUnitary.symm_apply_apply f

theorem angularFourierUnitary_forward_inverse (f : AngularL2) :
    angularFourierUnitary (angularFourierUnitary.symm f) = f :=
  angularFourierUnitary.apply_symm_apply f

end
end ImbalancedChen.Part3.AngularFourierUnitary20261026b


