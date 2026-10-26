import ImbalancedChen.Part3Gamma0TranslatedProductWeakPDE
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

For a locally integrable complex function on the ordinary real plane,
smooth compact real-kernel convolution can be differentiated twice in
each coordinate. Derivatives are obtained from the native dominated
convolution differentiation theorem, not an assumed differentiation
identity. The resulting trace equals the literal sum of the two ordinary
slice second derivatives. The actual normalized product kernel from the
Gamma0 defect tests is instantiated explicitly.
-/

namespace ImbalancedChen.Part3.ProductConvolutionSecondDerivatives20261026a

noncomputable section
open Set Function Filter MeasureTheory ContinuousLinearMap
open scoped Topology ContDiff Convolution
open ImbalancedChen.Part3.Gamma0TranslatedProductWeakPDE20261026a

abbrev Plane := ℝ × ℝ
def xDirection : Plane := (1, 0)
def yDirection : Plane := (0, 1)

def directional {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : Plane) (f : Plane → F) (p : Plane) : F := fderiv ℝ f p v

def euclideanLaplacian {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Plane → F) : Plane → F :=
  directional xDirection (directional xDirection f) +
    directional yDirection (directional yDirection f)

def planeAction : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := lsmul ℝ ℝ

theorem directional_cinfty {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Plane → F} (hf : ContDiff ℝ ∞ f) (v : Plane) :
    ContDiff ℝ ∞ (directional v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem directional_hasCompactSupport {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Plane → F} (hf : HasCompactSupport f) (v : Plane) :
    HasCompactSupport (directional v f) := by
  apply HasCompactSupport.of_support_subset_isCompact (hf.fderiv ℝ).isCompact
  intro p hp
  apply subset_closure
  intro hz
  exact hp (by simp [directional, hz])

/-- Evaluating the native CLM-valued derivative convolution really is
convolution with the evaluated derivative kernel. -/
theorem directional_convolution {k : Plane → ℝ} {g : Plane → ℂ}
    (hkc : HasCompactSupport k) (hk : ContDiff ℝ ∞ k)
    (hg : LocallyIntegrable g volume) (v : Plane) :
    directional v (k ⋆[planeAction, volume] g) =
      directional v k ⋆[planeAction, volume] g := by
  funext p
  have hk1 : ContDiff ℝ 1 k := hk.of_le (by simp)
  have hA := (hkc.fderiv ℝ).convolutionExists_left (planeAction.precompL Plane)
    (hk1.continuous_fderiv (by norm_num)) hg p
  unfold directional
  rw [(hkc.hasFDerivAt_convolution_left planeAction hk1 hg p).fderiv]
  rw [convolution_def, ContinuousLinearMap.integral_apply hA]
  rfl

theorem euclideanLaplacian_convolution {k : Plane → ℝ} {g : Plane → ℂ}
    (hkc : HasCompactSupport k) (hk : ContDiff ℝ ∞ k)
    (hg : LocallyIntegrable g volume) :
    euclideanLaplacian (k ⋆[planeAction, volume] g) =
      euclideanLaplacian k ⋆[planeAction, volume] g := by
  have hx : directional xDirection (directional xDirection
      (k ⋆[planeAction, volume] g)) =
      directional xDirection (directional xDirection k) ⋆[planeAction, volume] g := by
    rw [directional_convolution hkc hk hg xDirection,
      directional_convolution (directional_hasCompactSupport hkc xDirection)
        (directional_cinfty hk xDirection) hg xDirection]
  have hy : directional yDirection (directional yDirection
      (k ⋆[planeAction, volume] g)) =
      directional yDirection (directional yDirection k) ⋆[planeAction, volume] g := by
    rw [directional_convolution hkc hk hg yDirection,
      directional_convolution (directional_hasCompactSupport hkc yDirection)
        (directional_cinfty hk yDirection) hg yDirection]
  have hcx := (directional_hasCompactSupport
    (directional_hasCompactSupport hkc xDirection) xDirection).convolutionExists_left
    planeAction (directional_cinfty (directional_cinfty hk xDirection) xDirection).continuous hg
  have hcy := (directional_hasCompactSupport
    (directional_hasCompactSupport hkc yDirection) yDirection).convolutionExists_left
    planeAction (directional_cinfty (directional_cinfty hk yDirection) yDirection).continuous hg
  unfold euclideanLaplacian
  rw [hx, hy]
  exact (hcx.add_distrib hcy).symm

theorem directional_x_eq_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Plane → F} (hf : ContDiff ℝ ∞ f) (p : Plane) :
    directional xDirection f p = deriv (fun t : ℝ => f (t, p.2)) p.1 := by
  have h := ((hf.differentiable (by simp)) p).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  simpa only [directional, xDirection, Function.comp_def] using h.deriv.symm

theorem directional_y_eq_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Plane → F} (hf : ContDiff ℝ ∞ f) (p : Plane) :
    directional yDirection f p = deriv (fun t : ℝ => f (p.1, t)) p.2 := by
  have h := ((hf.differentiable (by simp)) p).hasFDerivAt.comp_hasDerivAt p.2
    ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  simpa only [directional, yDirection, Function.comp_def] using h.deriv.symm

theorem second_x_eq_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Plane → F} (hf : ContDiff ℝ ∞ f) (p : Plane) :
    directional xDirection (directional xDirection f) p =
      deriv (deriv (fun t : ℝ => f (t, p.2))) p.1 := by
  have hfun : deriv (fun t : ℝ => f (t, p.2)) =
      fun t => directional xDirection f (t, p.2) := by
    funext t
    exact (directional_x_eq_slice hf (t, p.2)).symm
  rw [hfun]
  exact directional_x_eq_slice (directional_cinfty hf xDirection) p

theorem second_y_eq_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Plane → F} (hf : ContDiff ℝ ∞ f) (p : Plane) :
    directional yDirection (directional yDirection f) p =
      deriv (deriv (fun t : ℝ => f (p.1, t))) p.2 := by
  have hfun : deriv (fun t : ℝ => f (p.1, t)) =
      fun t => directional yDirection f (p.1, t) := by
    funext t
    exact (directional_y_eq_slice hf (p.1, t)).symm
  rw [hfun]
  exact directional_y_eq_slice (directional_cinfty hf yDirection) p

theorem euclideanLaplacian_eq_slice {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Plane → F} (hf : ContDiff ℝ ∞ f) (p : Plane) :
    euclideanLaplacian f p =
      deriv (deriv (fun t : ℝ => f (t, p.2))) p.1 +
      deriv (deriv (fun t : ℝ => f (p.1, t))) p.2 := by
  exact congrArg₂ (· + ·) (second_x_eq_slice hf p) (second_y_eq_slice hf p)

theorem lineKernel_cinfty (n : ℕ) : ContDiff ℝ ∞ (lineKernel n) :=
  (lineBump n).contDiff_normed

theorem productKernel_dx (n : ℕ) :
    directional xDirection (productKernel n) =
      fun p => deriv (lineKernel n) p.1 * lineKernel n p.2 := by
  funext p
  rw [directional_x_eq_slice (productKernel_cinfty n)]
  exact (((lineKernel_cinfty n).differentiable (by simp) p.1).hasDerivAt.mul_const _).deriv

theorem productKernel_dy (n : ℕ) :
    directional yDirection (productKernel n) =
      fun p => lineKernel n p.1 * deriv (lineKernel n) p.2 := by
  funext p
  rw [directional_y_eq_slice (productKernel_cinfty n)]
  exact (((lineKernel_cinfty n).differentiable (by simp) p.2).hasDerivAt.const_mul _).deriv

theorem productKernel_dxx (n : ℕ) (p : Plane) :
    directional xDirection (directional xDirection (productKernel n)) p =
      deriv (deriv (lineKernel n)) p.1 * lineKernel n p.2 := by
  rw [productKernel_dx]
  have hd : ContDiff ℝ ∞ (deriv (lineKernel n)) :=
    (contDiff_infty_iff_deriv.mp (lineKernel_cinfty n)).2
  have hF : ContDiff ℝ ∞ (fun q : Plane =>
      deriv (lineKernel n) q.1 * lineKernel n q.2) :=
    (hd.comp contDiff_fst).mul ((lineKernel_cinfty n).comp contDiff_snd)
  rw [directional_x_eq_slice hF]
  exact ((hd.differentiable (by simp) p.1).hasDerivAt.mul_const _).deriv

theorem productKernel_dyy (n : ℕ) (p : Plane) :
    directional yDirection (directional yDirection (productKernel n)) p =
      lineKernel n p.1 * deriv (deriv (lineKernel n)) p.2 := by
  rw [productKernel_dy]
  have hd : ContDiff ℝ ∞ (deriv (lineKernel n)) :=
    (contDiff_infty_iff_deriv.mp (lineKernel_cinfty n)).2
  have hF : ContDiff ℝ ∞ (fun q : Plane =>
      lineKernel n q.1 * deriv (lineKernel n) q.2) :=
    ((lineKernel_cinfty n).comp contDiff_fst).mul (hd.comp contDiff_snd)
  rw [directional_y_eq_slice hF]
  exact ((hd.differentiable (by simp) p.2).hasDerivAt.const_mul _).deriv

theorem productKernel_laplacian (n : ℕ) (p : Plane) :
    euclideanLaplacian (productKernel n) p =
      deriv (deriv (lineKernel n)) p.1 * lineKernel n p.2 +
        lineKernel n p.1 * deriv (deriv (lineKernel n)) p.2 :=
  congrArg₂ (· + ·) (productKernel_dxx n p) (productKernel_dyy n p)

def productSmooth (n : ℕ) (g : Plane → ℂ) : Plane → ℂ :=
  productKernel n ⋆[planeAction, volume] g

theorem productSmooth_cinfty {g : Plane → ℂ} (hg : LocallyIntegrable g volume) (n : ℕ) :
    ContDiff ℝ ∞ (productSmooth n g) :=
  (productKernel_hasCompactSupport n).contDiff_convolution_left planeAction
    (productKernel_cinfty n) hg

/-- This is a derived twice-differentiated ordinary convolution identity. -/
theorem productSmooth_laplacian {g : Plane → ℂ} (hg : LocallyIntegrable g volume)
    (n : ℕ) (p : Plane) :
    euclideanLaplacian (productSmooth n g) p =
      ∫ t : Plane,
        (deriv (deriv (lineKernel n)) (p.1 - t.1) * lineKernel n (p.2 - t.2) +
          lineKernel n (p.1 - t.1) * deriv (deriv (lineKernel n)) (p.2 - t.2)) • g t := by
  rw [productSmooth, euclideanLaplacian_convolution
    (productKernel_hasCompactSupport n) (productKernel_cinfty n) hg]
  rw [convolution_eq_swap]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    rw [productKernel_laplacian]
    rfl

end
end ImbalancedChen.Part3.ProductConvolutionSecondDerivatives20261026a
