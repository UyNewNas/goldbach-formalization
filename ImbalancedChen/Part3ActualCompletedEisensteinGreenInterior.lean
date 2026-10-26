import ImbalancedChen.Part3ActualEisensteinHorocycleGreenFlux
import ImbalancedChen.Part3CompletedEisensteinSpatialMaass
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The actual completed Eisenstein Green vector and its outward-normal
one-form, with the existing horocycle current as the vertical component.
Actual genuine C2 supplies the slice derivatives, the product rule proves
their cancellation, and the proved actual Maass equations give the signed
pointwise divergence. No Green identity or eigen-equation is an input to
the final actual theorem. This source is independent of the CentralFourier
channel chain with the reported namespace API issue.
-/

namespace ImbalancedChen.Part3.ActualCompletedEisensteinGreenInterior20261026b
noncomputable section
open Set Complex Filter Topology
open CompletedEisensteinReflection20261025a CompletedEisensteinSpatialMaass
open ContinuedFourierNonconstantMaass ContinuedFourierSpatialContDiffTwo
open ActualEisensteinHorocycleGreenFlux20261026b

/-- Horizontal component in the same (height, horizontal) order as the
existing actualGreenCurrent, which is the vertical component. -/
def actualGreenCurrentX (s u : ℂ) (y x : ℝ) : ℂ :=
  star (completedEisensteinFourier s y x) * deriv (fun t : ℝ => completedEisensteinFourier u y t) x -
    star (deriv (fun t : ℝ => completedEisensteinFourier s y t) x) * completedEisensteinFourier u y x

def actualGreenVector (s u : ℂ) (p : ℝ × ℝ) : ℂ × ℂ :=
  (actualGreenCurrentX s u p.2 p.1, actualGreenCurrent s u p.2 p.1)

/-- Positively oriented tangent h has outward right normal (h_y,-h_x),
so this is the one-form -Jy dx + Jx dy used by the global side pairing. -/
def actualGreenOneForm (s u : ℂ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℂ :=
  coordinateLinear (-actualGreenCurrent s u p.2 p.1) (actualGreenCurrentX s u p.2 p.1)

theorem actualGreenOneForm_apply (s u : ℂ) (p h : ℝ × ℝ) :
    actualGreenOneForm s u p h = h.1 • (-actualGreenCurrent s u p.2 p.1) +
      h.2 • actualGreenCurrentX s u p.2 p.1 := by
  exact coordinateLinear_apply _ _ h

def actualGreenDivergence (s u : ℂ) (y x : ℝ) : ℂ :=
  deriv (fun t : ℝ => actualGreenCurrentX s u y t) x +
    deriv (fun t : ℝ => actualGreenCurrent s u t x) y

private theorem wronskian_hasDerivAt (f g : ℝ → ℂ) (x : ℝ)
    (hf : HasDerivAt f (deriv f x) x) (hg : HasDerivAt g (deriv g x) x)
    (hdf : HasDerivAt (deriv f) (deriv (deriv f) x) x)
    (hdg : HasDerivAt (deriv g) (deriv (deriv g) x) x) :
    HasDerivAt (fun t : ℝ => star (f t) * deriv g t - star (deriv f t) * g t)
      (star (f x) * deriv (deriv g) x - star (deriv (deriv f) x) * g x) x := by
  convert (hf.star.mul hdg).sub (hdf.star.mul hg) using 1 <;> ring

private theorem horizontal_c2 (s : ℂ) (y : ℝ) (hy : 0 < y) :
    ContDiff ℝ 2 (fun x : ℝ => completedEisensteinFourier s y x) :=
  (completedEisensteinFourier_contDiffOn_two s).comp_contDiff (by fun_prop) (fun _ => hy)

private theorem vertical_c2 (s : ℂ) (x : ℝ) :
    ContDiffOn ℝ 2 (fun y : ℝ => completedEisensteinFourier s y x) (Ioi (0 : ℝ)) :=
  (completedEisensteinFourier_contDiffOn_two s).comp (by fun_prop) (fun _ hy => hy)

/-- Genuine horizontal slice derivative of the actual current, including
all product-rule terms before their cancellation. -/
theorem actualGreenCurrentX_hasDerivAt_x (s u : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => actualGreenCurrentX s u y t)
      (star (completedEisensteinFourier s y x) *
        deriv (deriv (fun t : ℝ => completedEisensteinFourier u y t)) x -
      star (deriv (deriv (fun t : ℝ => completedEisensteinFourier s y t)) x) *
        completedEisensteinFourier u y x) x := by
  have hf := horizontal_c2 s y hy
  have hg := horizontal_c2 u y hy
  have hdf : ContDiff ℝ 1 (deriv (fun t : ℝ => completedEisensteinFourier s y t)) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ ((1 : ℕ∞ω) + 1)
      (fun t : ℝ => completedEisensteinFourier s y t) from hf)).2.2
  have hdg : ContDiff ℝ 1 (deriv (fun t : ℝ => completedEisensteinFourier u y t)) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ ((1 : ℕ∞ω) + 1)
      (fun t : ℝ => completedEisensteinFourier u y t) from hg)).2.2
  exact wronskian_hasDerivAt _ _ x ((hf.differentiable (by norm_num)) x).hasDerivAt
    ((hg.differentiable (by norm_num)) x).hasDerivAt
    (hdf.differentiable_one x).hasDerivAt (hdg.differentiable_one x).hasDerivAt

/-- Genuine vertical slice derivative of the PREEXISTING boundary current;
there is one Jy definition for both interior and horocycle theorems. -/
theorem actualGreenCurrent_hasDerivAt_y (s u : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => actualGreenCurrent s u t x)
      (star (completedEisensteinFourier s y x) *
        deriv (deriv (fun t : ℝ => completedEisensteinFourier u t x)) y -
      star (deriv (deriv (fun t : ℝ => completedEisensteinFourier s t x)) y) *
        completedEisensteinFourier u y x) y := by
  have hf := vertical_c2 s x
  have hg := vertical_c2 u x
  have hdf : ContDiffOn ℝ 1 (deriv (fun t : ℝ => completedEisensteinFourier s t x)) (Ioi (0 : ℝ)) :=
    hf.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hdg : ContDiffOn ℝ 1 (deriv (fun t : ℝ => completedEisensteinFourier u t x)) (Ioi (0 : ℝ)) :=
    hg.deriv_of_isOpen isOpen_Ioi (by norm_num)
  exact wronskian_hasDerivAt _ _ y
    (((hf y hy).contDiffAt (isOpen_Ioi.mem_nhds hy)).differentiableAt (by norm_num)).hasDerivAt
    (((hg y hy).contDiffAt (isOpen_Ioi.mem_nhds hy)).differentiableAt (by norm_num)).hasDerivAt
    (((hdf y hy).contDiffAt (isOpen_Ioi.mem_nhds hy)).differentiableAt (by norm_num)).hasDerivAt
    (((hdg y hy).contDiffAt (isOpen_Ioi.mem_nhds hy)).differentiableAt (by norm_num)).hasDerivAt

private theorem green_eigen_algebra (lam mu f g fxx fyy gxx gyy : ℂ)
    (y : ℝ) (hy : 0 < y)
    (hf : -(y : ℂ) ^ 2 * (fxx + fyy) = lam * f)
    (hg : -(y : ℂ) ^ 2 * (gxx + gyy) = mu * g) :
    (star f * gxx - star fxx * g) + (star f * gyy - star fyy * g) =
      (star lam - mu) * star f * g / (y : ℂ) ^ 2 := by
  have hfstar := congrArg star hf
  simp only [star_neg, star_mul, star_add, star_pow] at hfstar
  have hyStar : star (y : ℂ) = (y : ℂ) := by simp
  rw [hyStar] at hfstar
  apply (eq_div_iff (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hy.ne'))).mpr
  linear_combination g * hfstar - star f * hg

/-- Actual signed pointwise interior identity. The eigen-equations are
conclusions from true KODE/spatial jets in frozen19d514, not hypotheses. -/
theorem actualGreenDivergence_eq (s u : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) (y x : ℝ) (hy : 0 < y) :
    actualGreenDivergence s u y x =
      (star (s * (1 - s)) - u * (1 - u)) * star (completedEisensteinFourier s y x) *
        completedEisensteinFourier u y x / (y : ℂ) ^ 2 := by
  unfold actualGreenDivergence
  rw [(actualGreenCurrentX_hasDerivAt_x s u y x hy).deriv,
    (actualGreenCurrent_hasDerivAt_y s u y x hy).deriv]
  exact green_eigen_algebra (s * (1 - s)) (u * (1 - u)) _ _ _ _ _ _ y hy
    (completedEisensteinFourier_maass_eigen s hs0 hs1 y x hy)
    (completedEisensteinFourier_maass_eigen u hu0 hu1 y x hy)

end
end ImbalancedChen.Part3.ActualCompletedEisensteinGreenInterior20261026b
