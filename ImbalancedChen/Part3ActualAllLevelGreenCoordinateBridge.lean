import ImbalancedChen.Part3ActualAllLevelGreenInterior
import ImbalancedChen.Part3ActualCompletedGamma0SideCancellation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Exact compatibility of the ACTUAL all-level coordinate Green one-form with
the ACTUAL complex-field one-form used by Mobius covariance and Gamma0
side cancellation. Real coordinate paths identify the genuine Frechet
derivatives on 1 and I with the literal chart slice derivatives. Thus
-Jy dx+Jx dy is the same one-form, with the exact outward-right-normal
sign and no area-Jacobian factor. Integrability of this actual coordinate
edge density is derived from true all-level C-infinity on C1 paths. No
side-pairing, current equality, or line-integrability premise is assumed.
-/

namespace ImbalancedChen.Part3.ActualAllLevelGreenCoordinateBridge20261026b
noncomputable section
open Set Complex Filter Topology MeasureTheory
open scoped UpperHalfPlane MatrixGroups
open AllLevelContinuedMaass20261026a
open ContinuedFourierSpatialContDiffTwo
open ActualAllLevelGreenInterior20261026b
open SLRealGreenCurrent20261026b ActualCompletedGamma0Sides20261026b

/-- Actual first complex-coordinate direction 1 is the native horizontal
slice derivative, proved through a real differentiable coordinate path. -/
theorem completedComplexField_fderiv_one (N : ℕ) (s : ℂ) (w : ℂ) (hw : 0 < w.im) :
    fderiv ℝ (completedComplexField N s) w 1 =
      deriv (fun t : ℝ => completedLevelChart N s (t, w.im)) w.re := by
  let z : UpperHalfPlane := ⟨w, hw⟩
  have hF : DifferentiableAt ℝ (completedComplexField N s) w :=
    (completedComplexField_contDiffAt N s z).differentiableAt (by simp)
  have hp : HasDerivAt (fun t : ℝ => Complex.mk t w.im) (1 : ℂ) w.re := by
    have h := ((hasDerivAt_id w.re).ofReal_comp).add_const ((w.im : ℂ) * I)
    convert h using 1 <;> ext <;> simp [Complex.mul_re, Complex.mul_im]
  have h := hF.hasFDerivAt.comp_hasDerivAt w.re hp
  exact h.deriv.symm

/-- Actual first complex-coordinate direction I is the native vertical
slice derivative, with no holomorphy assumption on the Eisenstein field. -/
theorem completedComplexField_fderiv_I (N : ℕ) (s : ℂ) (w : ℂ) (hw : 0 < w.im) :
    fderiv ℝ (completedComplexField N s) w I =
      deriv (fun t : ℝ => completedLevelChart N s (w.re, t)) w.im := by
  let z : UpperHalfPlane := ⟨w, hw⟩
  have hF : DifferentiableAt ℝ (completedComplexField N s) w :=
    (completedComplexField_contDiffAt N s z).differentiableAt (by simp)
  have hp : HasDerivAt (fun t : ℝ => Complex.mk w.re t) I w.im := by
    have h := (((hasDerivAt_id w.im).ofReal_comp).mul_const I).const_add (w.re : ℂ)
    convert h using 1 <;> ext <;> simp [Complex.mul_re, Complex.mul_im]
  have h := hF.hasFDerivAt.comp_hasDerivAt w.im hp
  exact h.deriv.symm

/-- The global side-current one-form and the actual coordinate current
used by interior divergence are literally the same physical one-form. -/
theorem actualLevelGreenOneForm_eq_complex (N : ℕ) (s u : ℂ) (w v : ℂ) (hw : 0 < w.im) :
    actualLevelGreenOneForm N s u (w.re, w.im) (v.re, v.im) =
      greenOneForm (completedComplexField N s) (completedComplexField N u) w v := by
  rw [greenOneForm_coordinates,
    completedComplexField_fderiv_one N s w hw, completedComplexField_fderiv_one N u w hw,
    completedComplexField_fderiv_I N s w hw, completedComplexField_fderiv_I N u w hw]
  simp only [actualLevelGreenOneForm, coordinateLinear_apply, Complex.real_smul,
    actualLevelGreenCurrentX, actualLevelGreenCurrentY, completedComplexField, Complex.star_def]
  ring

theorem actualLevelGreenOneForm_eq_complex_native (N : ℕ) (s u : ℂ)
    (z : UpperHalfPlane) (v : ℂ) :
    actualLevelGreenOneForm N s u (z.re, z.im) (v.re, v.im) =
      greenOneForm (completedComplexField N s) (completedComplexField N u) z v :=
  actualLevelGreenOneForm_eq_complex N s u z v z.im_pos

/-- Every genuine C1 physical edge has an integrable actual coordinate
current. This is supplied rather than assumed by quotient-side assembly. -/
theorem actualLevelGreenOneForm_edge_intervalIntegrable (N : ℕ) (s u : ℂ)
    (c : ℝ → UpperHalfPlane) (hc : ContDiff ℝ 1 (fun t : ℝ => (c t : ℂ))) :
    IntervalIntegrable (fun t : ℝ => actualLevelGreenOneForm N s u ((c t).re, (c t).im)
      ((deriv (fun r : ℝ => (c r : ℂ)) t).re, (deriv (fun r : ℝ => (c r : ℂ)) t).im)) volume 0 1 := by
  have hi := completedGreen_edge_intervalIntegrable N s u c hc
  have he : (fun t : ℝ => actualLevelGreenOneForm N s u ((c t).re, (c t).im)
      ((deriv (fun r : ℝ => (c r : ℂ)) t).re, (deriv (fun r : ℝ => (c r : ℂ)) t).im)) =
      (fun t : ℝ => greenOneForm (completedComplexField N s) (completedComplexField N u)
        (c t) (deriv (fun r : ℝ => (c r : ℂ)) t)) := by
    funext t
    exact actualLevelGreenOneForm_eq_complex_native N s u (c t) _
  rw [he]
  exact hi

/-- The original coordinate boundary functional is identified with the
same actual-field edge integral used in covariance and paired-side proofs. -/
theorem actualLevelGreenOneForm_edge_integral_eq (N : ℕ) (s u : ℂ)
    (c : ℝ → UpperHalfPlane) :
    (∫ t in (0 : ℝ)..1, actualLevelGreenOneForm N s u ((c t).re, (c t).im)
      ((deriv (fun r : ℝ => (c r : ℂ)) t).re, (deriv (fun r : ℝ => (c r : ℂ)) t).im)) =
      ∫ t in (0 : ℝ)..1, greenOneForm (completedComplexField N s) (completedComplexField N u)
        (c t) (deriv (fun r : ℝ => (c r : ℂ)) t) := by
  congr 1
  funext t
  exact actualLevelGreenOneForm_eq_complex_native N s u (c t) _

end
end ImbalancedChen.Part3.ActualAllLevelGreenCoordinateBridge20261026b
