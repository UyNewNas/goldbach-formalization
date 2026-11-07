import ImbalancedChen.Part3ActualAllLevelGreenCoordinateBridge
import ImbalancedChen.Part3Gamma0FiniteCosetGreenTrace
import ImbalancedChen.Part3ActualMobiusMaassEquivariance

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Actual pulled-back completed fields used by the finite coset Green trace.
The genuine old Mobius C2 chain/Hessian trace theorem is reused, including
its mixed-term cancellation, rather than postulating a pulled-back eigen
equation. Native C-infinity supplies the actual outer regularity. The exact
determinant-one area compensation det(Dg)/(Im(gz))^2=1/y^2 is proved for
the SAME real Mobius map and tangent factor used by the trace. No trace
divergence or pullback Green identity is an assumption.
-/

namespace ImbalancedChen.Part3.ActualMobiusCompletedPullback20261026b
noncomputable section
open Set Complex Filter Topology Matrix
open scoped UpperHalfPlane MatrixGroups
open AllLevelContinuedMaass20261026a LevelOldformScattering20261026a
open ContinuedFourierNonconstantMaass ContinuedFourierSpatialContDiffTwo
open ActualCompletedGamma0Sides20261026b SLRealGreenCurrent20261026b
open Gamma0PairedEdgeGreen20261026b Gamma0FiniteCosetGreenTrace20261026b FrickeNormalizer
open ActualMobiusConformalTwoJet20261025a ActualMobiusMaassEquivariance20261025a
open MaassWeakOperatorCore20261024zz

theorem realGL_realSL_eq_realMatrix (g : SL(2, ℤ)) : realGL (realSL g) = realMatrix g := by
  ext i j
  simp [realGL, realSL, realMatrix]

theorem slMap_realSL_eq_actualMobius (g : SL(2, ℤ)) : slMap (realSL g) = actualMobius g := by
  funext w
  unfold slMap actualMobius
  rw [realGL_realSL_eq_realMatrix]

theorem slFactor_realSL_eq_factor (g : SL(2, ℤ)) (w : ℂ) : slFactor (realSL g) w = factor g w := by
  unfold slFactor factor
  rw [realGL_realSL_eq_realMatrix]

theorem complex_mk_contDiff : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Complex.mk p.1 p.2) := by
  have h : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) := by fun_prop
  convert h using 1
  funext p
  ext <;> simp [Complex.mul_re, Complex.mul_im]

theorem slMap_realSL_contDiffAt (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    ContDiffAt ℝ ∞ (slMap (realSL g)) (z : ℂ) := by
  have hD : DifferentiableOn ℂ (slMap (realSL g)) UpperHalfPlane.upperHalfPlaneSet := by
    intro w hw
    exact (slMap_hasDerivAt (realSL g) (⟨w, hw⟩ : UpperHalfPlane)).differentiableAt.differentiableWithinAt
  have hA : AnalyticAt ℂ (slMap (realSL g)) (z : ℂ) :=
    (hD.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet) z z.im_pos
  exact hA.contDiffAt.restrict_scalars ℝ

theorem pulledCompletedField_contDiffAt (N : ℕ) (s : ℂ) (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    ContDiffAt ℝ ∞ (pulledField g (completedComplexField N s)) (z : ℂ) := by
  have hOuter : ContDiffAt ℝ ∞ (completedComplexField N s) (slMap (realSL g) z) := by
    simpa only [slMap_eq_action, realSL_action_int] using completedComplexField_contDiffAt N s (g • z)
  exact hOuter.comp (z : ℂ) (slMap_realSL_contDiffAt g z)

def pulledCompletedChart (N : ℕ) (s : ℂ) (g : SL(2, ℤ)) (p : ℝ × ℝ) : ℂ :=
  pulledField g (completedComplexField N s) (Complex.mk p.1 p.2)

theorem pulledCompletedChart_contDiffOn (N : ℕ) (s : ℂ) (g : SL(2, ℤ)) :
    ContDiffOn ℝ ∞ (pulledCompletedChart N s g) upperChart := by
  intro p hp
  let z : UpperHalfPlane := ⟨Complex.mk p.1 p.2, hp⟩
  exact ((pulledCompletedField_contDiffAt N s g z).comp p complex_mk_contDiff.contDiffAt).contDiffWithinAt

/-- Existing centred and literal coordinate operators agree by genuine
translation of the actual derivatives; no eigenfunction hypothesis enters. -/
theorem centredMaass_eq_coordinate (F : ℂ → ℂ) (w : ℂ) :
    centredMaass F w = maassLaplacian (fun p : ℝ × ℝ => F (Complex.mk p.1 p.2)) w.re w.im := by
  have h := centredMaass_complexFunction_eq_chartMaass
    (fun p : ℝ × ℝ => F (Complex.mk p.1 p.2)) w
  change centredMaass F w = _ at h
  rw [h]
  unfold chartMaass maassLaplacian
  ring

theorem completedComplexField_centredMaass (N : ℕ) (s : ℂ)
    (hs : s ∈ completedRegularDomain N) (z : UpperHalfPlane) :
    centredMaass (completedComplexField N s) z = s * (1 - s) * completedComplexField N s z := by
  rw [centredMaass_eq_coordinate]
  exact completedLevelChart_maass N s hs z.re z.im z.im_pos

/-- ACTUAL pulled field eigen-equation obtained from the true C2 second
chain and mixed Hessian cancellation, never supplied as a trace premise. -/
theorem pulledCompletedField_centredMaass (N : ℕ) (s : ℂ)
    (hs : s ∈ completedRegularDomain N) (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    centredMaass (pulledField g (completedComplexField N s)) z =
      s * (1 - s) * pulledField g (completedComplexField N s) z := by
  have hOuter : ContDiffAt ℝ 2 (completedComplexField N s) ((g • z : UpperHalfPlane) : ℂ) :=
    (completedComplexField_contDiffAt N s (g • z)).of_le (by simp)
  simp only [pulledField, slMap_realSL_eq_actualMobius]
  rw [centredMaass_actualMobius_pullback g z _ hOuter,
    completedComplexField_centredMaass N s hs (g • z), actualMobius_eq_smul]

theorem pulledCompletedChart_maass (N : ℕ) (s : ℂ) (hs : s ∈ completedRegularDomain N)
    (g : SL(2, ℤ)) (x y : ℝ) (hy : 0 < y) :
    maassLaplacian (pulledCompletedChart N s g) x y =
      s * (1 - s) * pulledCompletedChart N s g (x, y) := by
  have h := pulledCompletedField_centredMaass N s hs g (⟨Complex.mk x y, hy⟩ : UpperHalfPlane)
  rw [centredMaass_eq_coordinate] at h
  exact h

theorem slJacobian_realSL_eq_normSq_factor (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    slJacobian (realSL g) z = Complex.normSq (factor g z) := by
  unfold slJacobian
  rw [realGL_realSL_eq_realMatrix]
  norm_num [factor, Complex.normSq_div, map_pow, Complex.normSq_eq_norm_sq, ← pow_mul]

/-- Canonical hyperbolic density compensation for the SAME actual map and
Jacobian used by the side-current trace, with exact orientation sign. -/
theorem slJacobian_over_image_height_sq (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    slJacobian (realSL g) z / (g • z).im ^ 2 = 1 / z.im ^ 2 := by
  have h := height_sq_mul_normSq_factor g z
  rw [← slJacobian_realSL_eq_normSq_factor g z] at h
  apply (div_eq_div_iff (pow_ne_zero 2 (g • z).im_pos.ne') (pow_ne_zero 2 z.im_pos.ne')).mpr
  linear_combination h

theorem slJacobian_over_image_height_sq_complex (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    (slJacobian (realSL g) z : ℂ) / ((g • z).im : ℂ) ^ 2 = 1 / (z.im : ℂ) ^ 2 := by
  exact_mod_cast slJacobian_over_image_height_sq g z

theorem slMap_det_over_image_height_sq (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    (fderiv ℝ (slMap (realSL g)) (z : ℂ)).det / (g • z).im ^ 2 = 1 / z.im ^ 2 := by
  rw [slMap_fderiv_det, slJacobian_over_image_height_sq]

end
end ImbalancedChen.Part3.ActualMobiusCompletedPullback20261026b
