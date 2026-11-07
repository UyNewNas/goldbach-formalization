import ImbalancedChen.Part3ActualMobiusCompletedPullback

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The actual Green current of the actual pulled-back completed fields is C1.
Its product-rule divergence is derived from genuine C2, and the actual
pulled eigen-equations (proved with genuine Mobius second-chain/mixed-term
cancellation) give the signed density. Exact hyperbolic area compensation
then proves d(g*current)=det(Dg)*div(current)(gz). The same coordinate
one-form is identified with the actual complex one-form and its literal
Mobius tangent pullback. No pullback-divergence or trace identity is input.
-/

namespace ImbalancedChen.Part3.ActualMobiusGreenPullbackDivergence20261026b
noncomputable section
open Set Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open AllLevelContinuedMaass20261026a LevelOldformScattering20261026a
open ContinuedFourierSpatialContDiffTwo ContinuedFourierNonconstantMaass
open ActualCompletedGreenCurrentRegularity20261026b ActualAllLevelGreenInterior20261026b
open ActualAllLevelGreenCoordinateBridge20261026b
open SLRealGreenCurrent20261026b ActualCompletedGamma0Sides20261026b
open Gamma0PairedEdgeGreen20261026b Gamma0FiniteCosetGreenTrace20261026b FrickeNormalizer
open ActualMobiusCompletedPullback20261026b

private def chartCurrentX (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  star (F p) * deriv (fun t : ℝ => G (t, p.2)) p.1 -
    star (deriv (fun t : ℝ => F (t, p.2)) p.1) * G p

private def chartCurrentY (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  star (F p) * deriv (fun t : ℝ => G (p.1, t)) p.2 -
    star (deriv (fun t : ℝ => F (p.1, t)) p.2) * G p

private theorem partial_x_c1 {F : ℝ × ℝ → ℂ} (hF : ContDiffOn ℝ ∞ F upperChart) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => deriv (fun t : ℝ => F (t, p.2)) p.1) upperChart := by
  have hD : ContDiffOn ℝ 1 (fderiv ℝ F) upperChart := hF.fderiv_of_isOpen upperChart_isOpen (by simp)
  apply (hD.clm_apply (contDiffOn_const (c := (1, 0)))).congr
  intro p hp
  exact slice_deriv_x_eq_fderiv
    (((hF p hp).contDiffAt (upperChart_isOpen.mem_nhds hp)).differentiableAt (by simp))

private theorem partial_y_c1 {F : ℝ × ℝ → ℂ} (hF : ContDiffOn ℝ ∞ F upperChart) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => deriv (fun t : ℝ => F (p.1, t)) p.2) upperChart := by
  have hD : ContDiffOn ℝ 1 (fderiv ℝ F) upperChart := hF.fderiv_of_isOpen upperChart_isOpen (by simp)
  apply (hD.clm_apply (contDiffOn_const (c := (0, 1)))).congr
  intro p hp
  exact slice_deriv_y_eq_fderiv
    (((hF p hp).contDiffAt (upperChart_isOpen.mem_nhds hp)).differentiableAt (by simp))

private theorem current_x_c1 {F G : ℝ × ℝ → ℂ}
    (hF : ContDiffOn ℝ ∞ F upperChart) (hG : ContDiffOn ℝ ∞ G upperChart) :
    ContDiffOn ℝ 1 (chartCurrentX F G) upperChart := by
  simpa only [chartCurrentX] using
    (((hF.of_le (by simp)).star.mul (partial_x_c1 hG)).sub
      ((partial_x_c1 hF).star.mul (hG.of_le (by simp))))

private theorem current_y_c1 {F G : ℝ × ℝ → ℂ}
    (hF : ContDiffOn ℝ ∞ F upperChart) (hG : ContDiffOn ℝ ∞ G upperChart) :
    ContDiffOn ℝ 1 (chartCurrentY F G) upperChart := by
  simpa only [chartCurrentY] using
    (((hF.of_le (by simp)).star.mul (partial_y_c1 hG)).sub
      ((partial_y_c1 hF).star.mul (hG.of_le (by simp))))

private theorem wronskian_derivative (f g : ℝ → ℂ) (x : ℝ)
    (hf : HasDerivAt f (deriv f x) x) (hg : HasDerivAt g (deriv g x) x)
    (hdf : HasDerivAt (deriv f) (deriv (deriv f) x) x)
    (hdg : HasDerivAt (deriv g) (deriv (deriv g) x) x) :
    deriv (fun t : ℝ => star (f t) * deriv g t - star (deriv f t) * g t) x =
      star (f x) * deriv (deriv g) x - star (deriv (deriv f) x) * g x := by
  have h := (hf.star.mul hdg).sub (hdf.star.mul hg)
  convert h.deriv using 1 <;> ring

private theorem current_divergence (F G : ℝ × ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F upperChart) (hG : ContDiffOn ℝ ∞ G upperChart)
    (lam mu : ℂ) (x y : ℝ) (hy : 0 < y)
    (hEF : maassLaplacian F x y = lam * F (x, y))
    (hEG : maassLaplacian G x y = mu * G (x, y)) :
    fderiv ℝ (chartCurrentX F G) (x, y) (1, 0) + fderiv ℝ (chartCurrentY F G) (x, y) (0, 1) =
      (star lam - mu) * star (F (x, y)) * G (x, y) / (y : ℂ) ^ 2 := by
  have hx := ((current_x_c1 hF hG) (x, y) hy).contDiffAt (upperChart_isOpen.mem_nhds hy)
  have hv := ((current_y_c1 hF hG) (x, y) hy).contDiffAt (upperChart_isOpen.mem_nhds hy)
  rw [← slice_deriv_x_eq_fderiv (hx.differentiableAt (by norm_num)),
    ← slice_deriv_y_eq_fderiv (hv.differentiableAt (by norm_num))]
  have hFx : ContDiff ℝ 2 (fun t : ℝ => F (t, y)) :=
    (hF.of_le (by simp)).comp_contDiff (by fun_prop) (fun _ => hy)
  have hGx : ContDiff ℝ 2 (fun t : ℝ => G (t, y)) :=
    (hG.of_le (by simp)).comp_contDiff (by fun_prop) (fun _ => hy)
  have hDFx := (contDiff_succ_iff_deriv.mp (show ContDiff ℝ ((1 : ℕ∞ω) + 1) _ from hFx)).2.2
  have hDGx := (contDiff_succ_iff_deriv.mp (show ContDiff ℝ ((1 : ℕ∞ω) + 1) _ from hGx)).2.2
  have hFy : ContDiffOn ℝ 2 (fun t : ℝ => F (x, t)) (Ioi (0 : ℝ)) :=
    (hF.of_le (by simp)).comp (by fun_prop) (fun _ ht => ht)
  have hGy : ContDiffOn ℝ 2 (fun t : ℝ => G (x, t)) (Ioi (0 : ℝ)) :=
    (hG.of_le (by simp)).comp (by fun_prop) (fun _ ht => ht)
  have hDFy : ContDiffOn ℝ 1 (deriv (fun t : ℝ => F (x, t))) (Ioi (0 : ℝ)) := hFy.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hDGy : ContDiffOn ℝ 1 (deriv (fun t : ℝ => G (x, t))) (Ioi (0 : ℝ)) := hGy.deriv_of_isOpen isOpen_Ioi (by norm_num)
  unfold chartCurrentX chartCurrentY
  rw [wronskian_derivative _ _ x ((hFx.differentiable (by norm_num)) x).hasDerivAt
    ((hGx.differentiable (by norm_num)) x).hasDerivAt (hDFx.differentiable_one x).hasDerivAt (hDGx.differentiable_one x).hasDerivAt,
    wronskian_derivative _ _ y
      (((hFy y hy).contDiffAt (isOpen_Ioi.mem_nhds hy)).differentiableAt (by norm_num)).hasDerivAt
      (((hGy y hy).contDiffAt (isOpen_Ioi.mem_nhds hy)).differentiableAt (by norm_num)).hasDerivAt
      (((hDFy y hy).contDiffAt (isOpen_Ioi.mem_nhds hy)).differentiableAt (by norm_num)).hasDerivAt
      (((hDGy y hy).contDiffAt (isOpen_Ioi.mem_nhds hy)).differentiableAt (by norm_num)).hasDerivAt]
  have hStar := congrArg star hEF
  unfold maassLaplacian at hStar hEG
  simp only [star_neg, star_mul, star_add, star_pow] at hStar
  have hyStar : star (y : ℂ) = (y : ℂ) := by simp
  rw [hyStar] at hStar
  apply (eq_div_iff (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hy.ne'))).mpr
  linear_combination G (x, y) * hStar - star (F (x, y)) * hEG

def pulledGreenX (N : ℕ) (s u : ℂ) (g : SL(2, ℤ)) (p : ℝ × ℝ) : ℂ :=
  chartCurrentX (pulledCompletedChart N s g) (pulledCompletedChart N u g) p

def pulledGreenY (N : ℕ) (s u : ℂ) (g : SL(2, ℤ)) (p : ℝ × ℝ) : ℂ :=
  chartCurrentY (pulledCompletedChart N s g) (pulledCompletedChart N u g) p

def pulledGreenOneForm (N : ℕ) (s u : ℂ) (g : SL(2, ℤ)) (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℂ :=
  coordinateLinear (-pulledGreenY N s u g p) (pulledGreenX N s u g p)

def pulledGreenDivergence (N : ℕ) (s u : ℂ) (g : SL(2, ℤ)) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ (pulledGreenX N s u g) p (1, 0) + fderiv ℝ (pulledGreenY N s u g) p (0, 1)

theorem pulledGreenX_contDiffOn_one (N : ℕ) (s u : ℂ) (g : SL(2, ℤ)) :
    ContDiffOn ℝ 1 (pulledGreenX N s u g) upperChart :=
  current_x_c1 (pulledCompletedChart_contDiffOn N s g) (pulledCompletedChart_contDiffOn N u g)

theorem pulledGreenY_contDiffOn_one (N : ℕ) (s u : ℂ) (g : SL(2, ℤ)) :
    ContDiffOn ℝ 1 (pulledGreenY N s u g) upperChart :=
  current_y_c1 (pulledCompletedChart_contDiffOn N s g) (pulledCompletedChart_contDiffOn N u g)

/-- Actual pullback divergence, from true pulled-field C2 and actual
Mobius second-chain eigen-equations, with the exact spectral sign. -/
theorem pulledGreenDivergence_eq (N : ℕ) (s u : ℂ)
    (hs : s ∈ completedRegularDomain N) (hu : u ∈ completedRegularDomain N)
    (g : SL(2, ℤ)) (x y : ℝ) (hy : 0 < y) :
    pulledGreenDivergence N s u g (x, y) =
      (star (s * (1 - s)) - u * (1 - u)) * star (pulledCompletedChart N s g (x, y)) *
        pulledCompletedChart N u g (x, y) / (y : ℂ) ^ 2 :=
  current_divergence _ _ (pulledCompletedChart_contDiffOn N s g) (pulledCompletedChart_contDiffOn N u g)
    (s * (1 - s)) (u * (1 - u)) x y hy
    (pulledCompletedChart_maass N s hs g x y hy) (pulledCompletedChart_maass N u hu g x y hy)

/-- d(g*current)=det(Dg)*div(current)(gz), for the actual completed
Eisenstein pair and the same native Jacobian as the physical one-form. -/
theorem pulledGreenDivergence_eq_jacobian (N : ℕ) (s u : ℂ)
    (hs : s ∈ completedRegularDomain N) (hu : u ∈ completedRegularDomain N)
    (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    pulledGreenDivergence N s u g (z.re, z.im) =
      (slJacobian (realSL g) z : ℂ) * actualLevelGreenDivergence N s u (g • z).im (g • z).re := by
  rw [pulledGreenDivergence_eq N s u hs hu g z.re z.im z.im_pos,
    actualLevelGreenDivergence_native N s u hs hu (g • z)]
  have hF (v : ℂ) : pulledCompletedChart N v g (z.re, z.im) = completedLevelOldform N v (g • z) := by
    simp only [pulledCompletedChart, pulledField, slMap_eq_action, realSL_action_int,
      completedComplexField_eq_native]
  rw [hF s, hF u]
  have harea := slJacobian_over_image_height_sq_complex g z
  calc
    _ = ((slJacobian (realSL g) z : ℂ) / ((g • z).im : ℂ) ^ 2) *
        ((star (s * (1 - s)) - u * (1 - u)) * star (completedLevelOldform N s (g • z)) *
          completedLevelOldform N u (g • z)) := by rw [harea]; ring
    _ = _ := by ring

private theorem field_derivative_coordinates (F : ℂ → ℂ) (w : ℂ)
    (hF : DifferentiableAt ℝ F w) :
    fderiv ℝ F w 1 = deriv (fun t : ℝ => F (Complex.mk t w.im)) w.re ∧
    fderiv ℝ F w I = deriv (fun t : ℝ => F (Complex.mk w.re t)) w.im := by
  have hx : HasDerivAt (fun t : ℝ => Complex.mk t w.im) (1 : ℂ) w.re := by
    convert ((hasDerivAt_id w.re).ofReal_comp).add_const ((w.im : ℂ) * I) using 1 <;>
      ext <;> simp [Complex.mul_re, Complex.mul_im]
  have hy : HasDerivAt (fun t : ℝ => Complex.mk w.re t) I w.im := by
    convert (((hasDerivAt_id w.im).ofReal_comp).mul_const I).const_add (w.re : ℂ) using 1 <;>
      ext <;> simp [Complex.mul_re, Complex.mul_im]
  exact ⟨(hF.hasFDerivAt.comp_hasDerivAt w.re hx).deriv.symm,
    (hF.hasFDerivAt.comp_hasDerivAt w.im hy).deriv.symm⟩

/-- Identification with the very same actual pulled-field one-form used
by Prime's finite coset trace, rather than a prescribed current coefficient. -/
theorem pulledGreenOneForm_eq_complex (N : ℕ) (s u : ℂ) (g : SL(2, ℤ))
    (z : UpperHalfPlane) (v : ℂ) :
    pulledGreenOneForm N s u g (z.re, z.im) (v.re, v.im) =
      greenOneForm (pulledField g (completedComplexField N s)) (pulledField g (completedComplexField N u)) z v := by
  have hFs := field_derivative_coordinates _ z
    ((pulledCompletedField_contDiffAt N s g z).differentiableAt (by simp))
  have hGu := field_derivative_coordinates _ z
    ((pulledCompletedField_contDiffAt N u g z).differentiableAt (by simp))
  rw [greenOneForm_coordinates, hFs.1, hFs.2, hGu.1, hGu.2]
  simp only [pulledGreenOneForm, coordinateLinear_apply, Complex.real_smul,
    pulledGreenX, pulledGreenY, chartCurrentX, chartCurrentY, pulledCompletedChart, Complex.star_def]
  ring

/-- The current really is the pullback with the literal transformed
tangent; covariance is reused and no Jacobian is attached to a one-form. -/
theorem pulledGreenOneForm_eq_physical (N : ℕ) (s u : ℂ) (g : SL(2, ℤ))
    (z : UpperHalfPlane) (v : ℂ) :
    pulledGreenOneForm N s u g (z.re, z.im) (v.re, v.im) =
      actualLevelGreenOneForm N s u ((g • z).re, (g • z).im)
        ((slFactor (realSL g) z * v).re, (slFactor (realSL g) z * v).im) := by
  rw [pulledGreenOneForm_eq_complex]
  have hF : DifferentiableAt ℝ (completedComplexField N s) (slMap (realSL g) z) := by
    simpa only [slMap_eq_action, realSL_action_int] using
      (completedComplexField_contDiffAt N s (g • z)).differentiableAt (by simp)
  have hG : DifferentiableAt ℝ (completedComplexField N u) (slMap (realSL g) z) := by
    simpa only [slMap_eq_action, realSL_action_int] using
      (completedComplexField_contDiffAt N u (g • z)).differentiableAt (by simp)
  rw [show pulledField g (completedComplexField N s) = fun w => completedComplexField N s (slMap (realSL g) w) from rfl,
    show pulledField g (completedComplexField N u) = fun w => completedComplexField N u (slMap (realSL g) w) from rfl,
    greenOneForm_slMap_pullback (realSL g) z _ _ hF hG,
    slMap_eq_action, realSL_action_int, ← actualLevelGreenOneForm_eq_complex_native]

end
end ImbalancedChen.Part3.ActualMobiusGreenPullbackDivergence20261026b
