import ImbalancedChen.Part3AllLevelContinuedMaass
import ImbalancedChen.Part3ActualCompletedGreenCurrentRegularity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Actual all-level completed Eisenstein Green current on the genuine native
chart. The chart is the literal finite oldform expression, with its actual
Euler denominator. Its proved spatial C-infinity supplies genuine Frechet
first jets and C1 current components; the slice product rule then gives
the actual divergence. The eigenparameters are retained exactly through
the proved all-level Maass equation. No regularity, Green identity or
eigen-equation of the final current is a caller hypothesis.
This uses valid de936 native geometry and has no16b003 dependency.
-/

namespace ImbalancedChen.Part3.ActualAllLevelGreenInterior20261026b
noncomputable section
open Set Complex Filter Topology
open scoped UpperHalfPlane
open AllLevelContinuedMaass20261026a LevelOldformScattering20261026a
open ContinuedFourierSpatialContDiffTwo ContinuedFourierNonconstantMaass
open ActualCompletedGreenCurrentRegularity20261026b

def actualLevelGreenCurrentX (N : ℕ) (s u : ℂ) (y x : ℝ) : ℂ :=
  star (completedLevelChart N s (x, y)) * deriv (fun t : ℝ => completedLevelChart N u (t, y)) x -
    star (deriv (fun t : ℝ => completedLevelChart N s (t, y)) x) * completedLevelChart N u (x, y)

def actualLevelGreenCurrentY (N : ℕ) (s u : ℂ) (y x : ℝ) : ℂ :=
  star (completedLevelChart N s (x, y)) * deriv (fun t : ℝ => completedLevelChart N u (x, t)) y -
    star (deriv (fun t : ℝ => completedLevelChart N s (x, t)) y) * completedLevelChart N u (x, y)

def actualLevelGreenVector (N : ℕ) (s u : ℂ) (p : ℝ × ℝ) : ℂ × ℂ :=
  (actualLevelGreenCurrentX N s u p.2 p.1, actualLevelGreenCurrentY N s u p.2 p.1)

def actualLevelGreenOneForm (N : ℕ) (s u : ℂ) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℂ :=
  coordinateLinear (-actualLevelGreenCurrentY N s u p.2 p.1) (actualLevelGreenCurrentX N s u p.2 p.1)

def actualLevelGreenDivergence (N : ℕ) (s u : ℂ) (y x : ℝ) : ℂ :=
  deriv (fun t : ℝ => actualLevelGreenCurrentX N s u y t) x +
    deriv (fun t : ℝ => actualLevelGreenCurrentY N s u t x) y

/-- Genuine finite-oldform first spatial jets are Frechet coordinate
evaluations; C1 follows from native C-infinity, with no jet regularity input. -/
theorem completedLevel_partialX_contDiffOn_one (N : ℕ) (s : ℂ) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => deriv (fun t : ℝ => completedLevelChart N s (t, p.2)) p.1) upperChart := by
  have hF := completedLevelChart_smooth N s
  have hD : ContDiffOn ℝ 1 (fderiv ℝ (completedLevelChart N s)) upperChart :=
    hF.fderiv_of_isOpen upperChart_isOpen (by simp)
  apply (hD.clm_apply (contDiffOn_const (c := (1, 0)))).congr
  intro p hp
  exact slice_deriv_x_eq_fderiv
    (((hF p hp).contDiffAt (upperChart_isOpen.mem_nhds hp)).differentiableAt (by simp))

theorem completedLevel_partialY_contDiffOn_one (N : ℕ) (s : ℂ) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => deriv (fun t : ℝ => completedLevelChart N s (p.1, t)) p.2) upperChart := by
  have hF := completedLevelChart_smooth N s
  have hD : ContDiffOn ℝ 1 (fderiv ℝ (completedLevelChart N s)) upperChart :=
    hF.fderiv_of_isOpen upperChart_isOpen (by simp)
  apply (hD.clm_apply (contDiffOn_const (c := (0, 1)))).congr
  intro p hp
  exact slice_deriv_y_eq_fderiv
    (((hF p hp).contDiffAt (upperChart_isOpen.mem_nhds hp)).differentiableAt (by simp))

theorem actualLevelGreenCurrentX_contDiffOn_one (N : ℕ) (s u : ℂ) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => actualLevelGreenCurrentX N s u p.2 p.1) upperChart := by
  have hs : ContDiffOn ℝ 1 (completedLevelChart N s) upperChart :=
    (completedLevelChart_smooth N s).of_le (by simp)
  have hu : ContDiffOn ℝ 1 (completedLevelChart N u) upperChart :=
    (completedLevelChart_smooth N u).of_le (by simp)
  simpa only [actualLevelGreenCurrentX] using
    ((hs.star.mul (completedLevel_partialX_contDiffOn_one N u)).sub
      ((completedLevel_partialX_contDiffOn_one N s).star.mul hu))

theorem actualLevelGreenCurrentY_contDiffOn_one (N : ℕ) (s u : ℂ) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => actualLevelGreenCurrentY N s u p.2 p.1) upperChart := by
  have hs : ContDiffOn ℝ 1 (completedLevelChart N s) upperChart :=
    (completedLevelChart_smooth N s).of_le (by simp)
  have hu : ContDiffOn ℝ 1 (completedLevelChart N u) upperChart :=
    (completedLevelChart_smooth N u).of_le (by simp)
  simpa only [actualLevelGreenCurrentY] using
    ((hs.star.mul (completedLevel_partialY_contDiffOn_one N u)).sub
      ((completedLevel_partialY_contDiffOn_one N s).star.mul hu))

theorem actualLevelGreenVector_contDiffOn_one (N : ℕ) (s u : ℂ) :
    ContDiffOn ℝ 1 (actualLevelGreenVector N s u) upperChart :=
  (actualLevelGreenCurrentX_contDiffOn_one N s u).prodMk (actualLevelGreenCurrentY_contDiffOn_one N s u)

theorem actualLevelGreenOneForm_contDiffOn_one (N : ℕ) (s u : ℂ) :
    ContDiffOn ℝ 1 (actualLevelGreenOneForm N s u) upperChart := by
  simpa only [actualLevelGreenOneForm, coordinateLinear] using
    ((firstLift.contDiff.comp_contDiffOn (actualLevelGreenCurrentY_contDiffOn_one N s u).neg).add
      (secondLift.contDiff.comp_contDiffOn (actualLevelGreenCurrentX_contDiffOn_one N s u)))

private theorem wronskian_hasDerivAt (f g : ℝ → ℂ) (x : ℝ)
    (hf : HasDerivAt f (deriv f x) x) (hg : HasDerivAt g (deriv g x) x)
    (hdf : HasDerivAt (deriv f) (deriv (deriv f) x) x)
    (hdg : HasDerivAt (deriv g) (deriv (deriv g) x) x) :
    HasDerivAt (fun t : ℝ => star (f t) * deriv g t - star (deriv f t) * g t)
      (star (f x) * deriv (deriv g) x - star (deriv (deriv f) x) * g x) x := by
  convert (hf.star.mul hdg).sub (hdf.star.mul hg) using 1 <;> ring

theorem actualLevelGreenCurrentX_hasDerivAt_x (N : ℕ) (s u : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => actualLevelGreenCurrentX N s u y t)
      (star (completedLevelChart N s (x, y)) * deriv (deriv (fun t : ℝ => completedLevelChart N u (t, y))) x -
        star (deriv (deriv (fun t : ℝ => completedLevelChart N s (t, y))) x) * completedLevelChart N u (x, y)) x := by
  have hf : ContDiff ℝ 2 (fun t : ℝ => completedLevelChart N s (t, y)) :=
    ((completedLevelChart_smooth N s).of_le (by simp)).comp_contDiff (by fun_prop) (fun _ => hy)
  have hg : ContDiff ℝ 2 (fun t : ℝ => completedLevelChart N u (t, y)) :=
    ((completedLevelChart_smooth N u).of_le (by simp)).comp_contDiff (by fun_prop) (fun _ => hy)
  have hdf := (contDiff_succ_iff_deriv.mp (show ContDiff ℝ ((1 : ℕ∞ω) + 1)
    (fun t : ℝ => completedLevelChart N s (t, y)) from hf)).2.2
  have hdg := (contDiff_succ_iff_deriv.mp (show ContDiff ℝ ((1 : ℕ∞ω) + 1)
    (fun t : ℝ => completedLevelChart N u (t, y)) from hg)).2.2
  exact wronskian_hasDerivAt _ _ x ((hf.differentiable (by norm_num)) x).hasDerivAt
    ((hg.differentiable (by norm_num)) x).hasDerivAt
    (hdf.differentiable_one x).hasDerivAt (hdg.differentiable_one x).hasDerivAt

theorem actualLevelGreenCurrentY_hasDerivAt_y (N : ℕ) (s u : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => actualLevelGreenCurrentY N s u t x)
      (star (completedLevelChart N s (x, y)) * deriv (deriv (fun t : ℝ => completedLevelChart N u (x, t))) y -
        star (deriv (deriv (fun t : ℝ => completedLevelChart N s (x, t))) y) * completedLevelChart N u (x, y)) y := by
  have hf : ContDiffOn ℝ 2 (fun t : ℝ => completedLevelChart N s (x, t)) (Ioi (0 : ℝ)) :=
    ((completedLevelChart_smooth N s).of_le (by simp)).comp (by fun_prop) (fun _ ht => ht)
  have hg : ContDiffOn ℝ 2 (fun t : ℝ => completedLevelChart N u (x, t)) (Ioi (0 : ℝ)) :=
    ((completedLevelChart_smooth N u).of_le (by simp)).comp (by fun_prop) (fun _ ht => ht)
  have hdf : ContDiffOn ℝ 1 (deriv (fun t : ℝ => completedLevelChart N s (x, t))) (Ioi (0 : ℝ)) :=
    hf.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hdg : ContDiffOn ℝ 1 (deriv (fun t : ℝ => completedLevelChart N u (x, t))) (Ioi (0 : ℝ)) :=
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

/-- Actual all-level interior Green identity, using true native Maass
equations. The exact eigenparameters and finite-oldform field are retained. -/
theorem actualLevelGreenDivergence_eq (N : ℕ) (s u : ℂ)
    (hs : s ∈ completedRegularDomain N) (hu : u ∈ completedRegularDomain N)
    (y x : ℝ) (hy : 0 < y) :
    actualLevelGreenDivergence N s u y x =
      (star (s * (1 - s)) - u * (1 - u)) * star (completedLevelChart N s (x, y)) *
        completedLevelChart N u (x, y) / (y : ℂ) ^ 2 := by
  unfold actualLevelGreenDivergence
  rw [(actualLevelGreenCurrentX_hasDerivAt_x N s u y x hy).deriv,
    (actualLevelGreenCurrentY_hasDerivAt_y N s u y x hy).deriv]
  exact green_eigen_algebra (s * (1 - s)) (u * (1 - u)) _ _ _ _ _ _ y hy
    (completedLevelChart_maass N s hs x y hy) (completedLevelChart_maass N u hu x y hy)

theorem actualLevelGreen_fderiv_divergence_eq (N : ℕ) (s u : ℂ)
    (hs : s ∈ completedRegularDomain N) (hu : u ∈ completedRegularDomain N)
    (x y : ℝ) (hy : 0 < y) :
    fderiv ℝ (fun p : ℝ × ℝ => actualLevelGreenCurrentX N s u p.2 p.1) (x, y) (1, 0) +
      fderiv ℝ (fun p : ℝ × ℝ => actualLevelGreenCurrentY N s u p.2 p.1) (x, y) (0, 1) =
      (star (s * (1 - s)) - u * (1 - u)) * star (completedLevelChart N s (x, y)) *
        completedLevelChart N u (x, y) / (y : ℂ) ^ 2 := by
  have hx := ((actualLevelGreenCurrentX_contDiffOn_one N s u) (x, y) hy).contDiffAt
    (upperChart_isOpen.mem_nhds hy)
  have hv := ((actualLevelGreenCurrentY_contDiffOn_one N s u) (x, y) hy).contDiffAt
    (upperChart_isOpen.mem_nhds hy)
  rw [← slice_deriv_x_eq_fderiv (hx.differentiableAt (by norm_num)),
    ← slice_deriv_y_eq_fderiv (hv.differentiableAt (by norm_num))]
  exact actualLevelGreenDivergence_eq N s u hs hu y x hy

/-- Native physical-value form of the interior identity. -/
theorem actualLevelGreenDivergence_native (N : ℕ) (s u : ℂ)
    (hs : s ∈ completedRegularDomain N) (hu : u ∈ completedRegularDomain N)
    (z : UpperHalfPlane) : actualLevelGreenDivergence N s u z.im z.re =
      (star (s * (1 - s)) - u * (1 - u)) * star (completedLevelOldform N s z) *
        completedLevelOldform N u z / (z.im : ℂ) ^ 2 := by
  rw [actualLevelGreenDivergence_eq N s u hs hu z.im z.re z.im_pos,
    completedLevelChart_eq_native, completedLevelChart_eq_native]

end
end ImbalancedChen.Part3.ActualAllLevelGreenInterior20261026b
