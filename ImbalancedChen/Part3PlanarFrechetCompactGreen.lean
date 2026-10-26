import ImbalancedChen.Part3ProductConvolutionSecondDerivatives
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Nonperiodic complex planar Green from native multidimensional Frechet
integration by parts. Compactness belongs only to the test, so this applies
to a cutoff squared times a smooth noncompact mollification. Every product
integrability obligation is discharged here; no Green identity is assumed.
-/

namespace ImbalancedChen.Part3.PlanarFrechetCompactGreen20261026b
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
open ProductConvolutionSecondDerivatives20261026a

theorem compact_star_pair_integrable {P Q : Plane → ℂ}
    (hPc : HasCompactSupport P) (hP : Continuous P) (hQ : Continuous Q) :
    Integrable (fun p => star (P p) * Q p) :=
  (hP.star.mul hQ).integrable_of_hasCompactSupport
    ((hPc.comp_left (g := star) (by simp)).mul_right)

theorem directional_star (P : Plane → ℂ) (v p : Plane) :
    directional v (fun q => star (P q)) p = star (directional v P p) := by
  simp [directional, fderiv_star]

/-- First-order identity needed to identify a weak gradient after extraction. -/
theorem compact_first_green {P U : Plane → ℂ}
    (hPc : HasCompactSupport P) (hP : ContDiff ℝ ∞ P)
    (hU : ContDiff ℝ ∞ U) (v : Plane) :
    (∫ p : Plane, star (P p) * directional v U p) =
      -(∫ p : Plane, star (directional v P p) * U p) := by
  have h₁ := compact_star_pair_integrable (directional_hasCompactSupport hPc v)
    (directional_cinfty hP v).continuous hU.continuous
  have h₂ := compact_star_pair_integrable hPc hP.continuous
    (directional_cinfty hU v).continuous
  have h₀ := compact_star_pair_integrable hPc hP.continuous hU.continuous
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Plane))
    (f := fun p => star (P p)) (g := U) (v := v)
    (by simpa only [← directional, directional_star] using h₁)
    h₂ h₀
    (fun p _ => ((hP.differentiable (by simp)) p).star)
    (fun p _ => (hU.differentiable (by simp)) p)
  simpa only [← directional, directional_star] using h

theorem compact_direction_green {P U : Plane → ℂ}
    (hPc : HasCompactSupport P) (hP : ContDiff ℝ ∞ P)
    (hU : ContDiff ℝ ∞ U) (v : Plane) :
    (∫ p : Plane, star (P p) * directional v (directional v U) p) =
      -(∫ p : Plane, star (directional v P p) * directional v U p) := by
  have hPd := directional_cinfty hP v
  have hUd := directional_cinfty hU v
  have hUdd := directional_cinfty hUd v
  have h₁ := compact_star_pair_integrable
    (directional_hasCompactSupport hPc v) hPd.continuous hUd.continuous
  have h₂ := compact_star_pair_integrable hPc hP.continuous hUdd.continuous
  have h₀ := compact_star_pair_integrable hPc hP.continuous hUd.continuous
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Plane))
    (f := fun p => star (P p)) (g := directional v U) (v := v)
    (by simpa only [← directional, directional_star] using h₁)
    h₂ h₀
    (fun p _ => ((hP.differentiable (by simp)) p).star)
    (fun p _ => (hUd.differentiable (by simp)) p)
  simpa only [← directional, directional_star] using h

def gradientPair (P U : Plane → ℂ) (p : Plane) : ℂ :=
  star (directional xDirection P p) * directional xDirection U p +
    star (directional yDirection P p) * directional yDirection U p

theorem compact_planar_green {P U : Plane → ℂ}
    (hPc : HasCompactSupport P) (hP : ContDiff ℝ ∞ P)
    (hU : ContDiff ℝ ∞ U) :
    (∫ p : Plane, -(star (P p) * euclideanLaplacian U p)) =
      ∫ p : Plane, gradientPair P U p := by
  have hx := compact_direction_green hPc hP hU xDirection
  have hy := compact_direction_green hPc hP hU yDirection
  have hxx := compact_star_pair_integrable hPc hP.continuous
    (directional_cinfty (directional_cinfty hU xDirection) xDirection).continuous
  have hyy := compact_star_pair_integrable hPc hP.continuous
    (directional_cinfty (directional_cinfty hU yDirection) yDirection).continuous
  have hdx := compact_star_pair_integrable (directional_hasCompactSupport hPc xDirection)
    (directional_cinfty hP xDirection).continuous (directional_cinfty hU xDirection).continuous
  have hdy := compact_star_pair_integrable (directional_hasCompactSupport hPc yDirection)
    (directional_cinfty hP yDirection).continuous (directional_cinfty hU yDirection).continuous
  simp only [euclideanLaplacian, Pi.add_apply, mul_add, gradientPair]
  rw [integral_neg, integral_add hxx hyy, integral_add hdx hdy, hx, hy]
  ring

end
end ImbalancedChen.Part3.PlanarFrechetCompactGreen20261026b
