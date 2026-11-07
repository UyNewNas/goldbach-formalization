import ImbalancedChen.Part3FrickeNormalizer
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The sesquilinear Green boundary ONE-FORM is evaluated on the outward
right-normal -I*v of a positively oriented tangent v. Its covariance is
proved under the actual determinant-one REAL Mobius action. The native
complex derivative is (cz+d)^(-2); the exact positive real Jacobian is
|cz+d|^(-4). The one-form transports with the actual transformed tangent,
without an additional area-Jacobian factor. Fricke charts are included.
No Stokes theorem, side cancellation or quotient Green identity is a premise.
-/

noncomputable section
open Complex Matrix
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.FrickeNormalizer

namespace ImbalancedChen.Part3.SLRealGreenCurrent20261026b

def realGL (g : SL(2, ℝ)) : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ g

def slMap (g : SL(2, ℝ)) (w : ℂ) : ℂ :=
  ((realGL g • UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ)

def slFactor (g : SL(2, ℝ)) (w : ℂ) : ℂ :=
  1 / UpperHalfPlane.denom (realGL g) w ^ 2

def slJacobian (g : SL(2, ℝ)) (w : ℂ) : ℝ :=
  1 / ‖UpperHalfPlane.denom (realGL g) w‖ ^ 4

theorem slMap_eq_action (g : SL(2, ℝ)) (z : UpperHalfPlane) :
    slMap g z = ((g • z : UpperHalfPlane) : ℂ) := by
  simp [slMap, realGL, UpperHalfPlane.ofComplex_apply]

theorem slMap_hasDerivAt (g : SL(2, ℝ)) (z : UpperHalfPlane) :
    HasDerivAt (slMap g) (slFactor g z) (z : ℂ) := by
  have hdet : (realGL g).val.det = 1 := by simp [realGL]
  have h := UpperHalfPlane.hasStrictDerivAt_smul
    (g := realGL g) (by rw [hdet]; norm_num) z
  simpa only [slMap, slFactor, hdet, Complex.ofReal_one] using h.hasDerivAt

theorem slMap_hasFDerivAt (g : SL(2, ℝ)) (z : UpperHalfPlane) :
    HasFDerivAt (slMap g) (slFactor g z • (1 : ℂ →L[ℝ] ℂ)) (z : ℂ) :=
  (slMap_hasDerivAt g z).complexToReal_fderiv

theorem slJacobian_pos (g : SL(2, ℝ)) (z : UpperHalfPlane) : 0 < slJacobian g z := by
  exact one_div_pos.mpr (pow_pos
    (norm_pos_iff.mpr (UpperHalfPlane.denom_ne_zero (realGL g) z)) 4)

/-- Exact signed real Jacobian; determinant one makes its sign positive. -/
theorem slMap_fderiv_det (g : SL(2, ℝ)) (z : UpperHalfPlane) :
    (fderiv ℝ (slMap g) (z : ℂ)).det = slJacobian g z := by
  have h := (UpperHalfPlane.hasStrictFDerivAt_smul (realGL g) z).hasFDerivAt.fderiv
  change fderiv ℝ (slMap g) (z : ℂ) = _ at h
  rw [h, UpperHalfPlane.det_smulFDeriv]
  have hd : (realGL g).det.val = 1 := by simp [realGL]
  simp [hd, slJacobian]

/-- The actual first derivative has the exact conformal coordinate matrix. -/
theorem slMap_first_coordinate_data (g : SL(2, ℝ)) (z : UpperHalfPlane) :
    (fderiv ℝ (slMap g) z 1).re = (slFactor g z).re ∧
    (fderiv ℝ (slMap g) z 1).im = (slFactor g z).im ∧
    (fderiv ℝ (slMap g) z I).re = -(slFactor g z).im ∧
    (fderiv ℝ (slMap g) z I).im = (slFactor g z).re := by
  rw [(slMap_hasFDerivAt g z).fderiv]
  simp [Complex.mul_re, Complex.mul_im]

/-- Outward right normal for a counterclockwise tangent. This is
the normal flux, not a new definition of the existing horocycle Jy. -/
def greenOneForm (F G : ℂ → ℂ) (z v : ℂ) : ℂ :=
  conj (F z) * fderiv ℝ G z (-I * v) - conj (fderiv ℝ F z (-I * v)) * G z

theorem greenOneForm_coordinates (F G : ℂ → ℂ) (z v : ℂ) :
    greenOneForm F G z v =
      -(v.re : ℂ) * (conj (F z) * fderiv ℝ G z I - conj (fderiv ℝ F z I) * G z) +
        (v.im : ℂ) * (conj (F z) * fderiv ℝ G z 1 - conj (fderiv ℝ F z 1) * G z) := by
  have hv : -I * v = v.im • (1 : ℂ) + (-v.re) • I := by
    ext <;> simp [Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring
  unfold greenOneForm
  rw [hv]
  simp only [map_add, map_smul, Complex.real_smul, map_add, map_mul, conj_ofReal, map_neg]
  ring

theorem slMap_pullback_derivative (g : SL(2, ℝ)) (z : UpperHalfPlane)
    (F : ℂ → ℂ) (hF : DifferentiableAt ℝ F (slMap g z)) (v : ℂ) :
    fderiv ℝ (fun w => F (slMap g w)) (z : ℂ) v =
      fderiv ℝ F (slMap g z) (slFactor g z * v) := by
  rw [(hF.hasFDerivAt.comp (z : ℂ) (slMap_hasFDerivAt g z)).fderiv]
  rfl

/-- Genuine covariance of the boundary one-form under literal SL(2,R).
Real differentiability of the two outer functions is the only analytic input. -/
theorem greenOneForm_slMap_pullback (g : SL(2, ℝ)) (z : UpperHalfPlane)
    (F G : ℂ → ℂ) (hF : DifferentiableAt ℝ F (slMap g z))
    (hG : DifferentiableAt ℝ G (slMap g z)) (v : ℂ) :
    greenOneForm (fun w => F (slMap g w)) (fun w => G (slMap g w)) z v =
      greenOneForm F G (slMap g z) (slFactor g z * v) := by
  unfold greenOneForm
  rw [slMap_pullback_derivative g z G hG, slMap_pullback_derivative g z F hF]
  rw [show slFactor g z * (-I * v) = -I * (slFactor g z * v) by ring]

theorem greenOneForm_fricke_pullback (N : ℕ) (hN : 0 < N) (z : UpperHalfPlane)
    (F G : ℂ → ℂ) (hF : DifferentiableAt ℝ F (slMap (frickeSL N hN) z))
    (hG : DifferentiableAt ℝ G (slMap (frickeSL N hN) z)) (v : ℂ) :
    greenOneForm (fun w => F (slMap (frickeSL N hN) w))
      (fun w => G (slMap (frickeSL N hN) w)) z v =
      greenOneForm F G (slMap (frickeSL N hN) z) (slFactor (frickeSL N hN) z * v) :=
  greenOneForm_slMap_pullback _ z F G hF hG v

theorem slFactor_fricke (N : ℕ) (hN : 0 < N) (z : ℂ) :
    slFactor (frickeSL N hN) z = 1 / ((Real.sqrt (N : ℝ) : ℂ) * z) ^ 2 := by
  simp [slFactor, realGL, UpperHalfPlane.denom, frickeSL, frickeMatrix]

end ImbalancedChen.Part3.SLRealGreenCurrent20261026b
