import ImbalancedChen.Part3GenericResolventCyclicIntertwining
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
The coordinate-weighted quadratic integral for arbitrary scalar L2
vectors, rather than just continuous spectral tests. This supplies the
norm identities needed to complete actual energy lifts in weighted L2.
-/

namespace ImbalancedChen.Part3.CyclicCoordinateQuadraticIntegral20261025a

noncomputable section
open MeasureTheory
open GenericResolventScalarMeasure20261025a
open GenericResolventCyclicL2Representation20261025a
open GenericResolventCyclicIntertwining20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R) (f : H)

private theorem star_mul_self_complex (z : ℂ) :
    star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

theorem coordinate_quadratic_integrable (ξ : ScalarL2 R hSA f) :
    Integrable (fun t : ResolventSpectrum R => (t : ℝ) * ‖ξ t‖ ^ 2)
      (scalarMeasure R hSA f) := by
  have h := (L2.integrable_inner (𝕜 := ℂ) ξ
    (coordinateMultiplier R hSA f ξ)).re
  apply h.congr
  filter_upwards [coordinateMultiplier_coe_ae R hSA f ξ] with t ht
  rw [ht]
  simp only [RCLike.inner_apply', ← mul_assoc]
  have halg : star (ξ t) * (((t : ℝ) : ℂ) * ξ t) =
      ((t : ℝ) : ℂ) * (star (ξ t) * ξ t) := by ring
  rw [halg, star_mul_self_complex]
  simp

theorem coordinate_quadratic_integral (ξ : ScalarL2 R hSA f) :
    (inner ℂ ξ (coordinateMultiplier R hSA f ξ)).re =
      ∫ t : ResolventSpectrum R, (t : ℝ) * ‖ξ t‖ ^ 2 ∂scalarMeasure R hSA f := by
  rw [L2.inner_def, ← integral_re (L2.integrable_inner (𝕜 := ℂ) ξ
    (coordinateMultiplier R hSA f ξ))]
  apply integral_congr_ae
  filter_upwards [coordinateMultiplier_coe_ae R hSA f ξ] with t ht
  rw [ht]
  simp only [RCLike.inner_apply']
  have halg : star (ξ t) * (((t : ℝ) : ℂ) * ξ t) =
      ((t : ℝ) : ℂ) * (star (ξ t) * ξ t) := by ring
  rw [halg, star_mul_self_complex]
  simp

theorem coordinate_square_integrable (ξ : ScalarL2 R hSA f) :
    Integrable (fun t : ResolventSpectrum R => (t : ℝ) ^ 2 * ‖ξ t‖ ^ 2)
      (scalarMeasure R hSA f) := by
  have h := (L2.integrable_inner (𝕜 := ℂ)
    (coordinateMultiplier R hSA f ξ) (coordinateMultiplier R hSA f ξ)).re
  apply h.congr
  filter_upwards [coordinateMultiplier_coe_ae R hSA f ξ] with t ht
  rw [ht, inner_self_eq_norm_sq_to_K]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs]

theorem coordinate_square_integral (ξ : ScalarL2 R hSA f) :
    ‖coordinateMultiplier R hSA f ξ‖ ^ 2 =
      ∫ t : ResolventSpectrum R, (t : ℝ) ^ 2 * ‖ξ t‖ ^ 2 ∂scalarMeasure R hSA f := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ)
      (coordinateMultiplier R hSA f ξ) (coordinateMultiplier R hSA f ξ))]
  apply integral_congr_ae
  filter_upwards [coordinateMultiplier_coe_ae R hSA f ξ] with t ht
  rw [ht, inner_self_eq_norm_sq_to_K]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs]

end
end ImbalancedChen.Part3.CyclicCoordinateQuadraticIntegral20261025a
