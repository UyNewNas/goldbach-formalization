import ImbalancedChen.Part3ActualMobiusMaassEquivariance
import ImbalancedChen.Part3Gamma0CompactGreenProductL1

/-!
# Actual Mobius covariance of the first-gradient Dirichlet density

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.

For arbitrary C1 complex-valued outer chart functions, the actual Mobius
pullback first gradients have Dirichlet pairing scaled by normSq((cz+d)^-2).
The actual imaginary-part formula gives exact hyperbolic y^2 compensation.
The derivatives are the existing literal sliceDx/sliceDy used by the Green
worker. No formal conformality field, energy target, eigenfunction or
tensor restriction is among the premises.
-/

namespace ImbalancedChen.Part3.ActualMobiusDirichletCovariance20261025a
noncomputable section
open Complex Filter Topology Set Matrix
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.ActualMobiusConformalTwoJet20261025a
open ImbalancedChen.Part3.ActualMobiusMaassEquivariance20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.Gamma0CompactGreenProductL120261025a

def centredFirst (F : ℂ → ℂ) (z v : ℂ) : ℂ :=
  deriv (fun t : ℝ => F (z + (t : ℂ) * v)) 0

def centredDirichlet (F G : ℂ → ℂ) (z : ℂ) : ℂ :=
  star (centredFirst F z 1) * centredFirst G z 1 +
    star (centredFirst F z Complex.I) * centredFirst G z Complex.I

def chartDirichlet (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  star (sliceDx F p) * sliceDx G p + star (sliceDy F p) * sliceDy G p

def hyperbolicChartDirichlet (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.2 : ℂ) ^ 2 * chartDirichlet F G p

/-- The full sesquilinear trace identity for any two REAL-linear maps;
no complex-linearity of either outer derivative is assumed. -/
theorem real_linear_sesquilinear_conformal_trace
    (D E : ℂ →L[ℝ] ℂ) (a : ℂ) :
    star (D a) * E a + star (D (a * Complex.I)) * E (a * Complex.I) =
      (Complex.normSq a : ℂ) * (star (D 1) * E 1 + star (D Complex.I) * E Complex.I) := by
  have ha : a = a.re • (1 : ℂ) + a.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im a).symm
  have hai : a * Complex.I = (-a.im) • (1 : ℂ) + a.re • Complex.I := by
    ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.real_smul] <;> ring
  calc
    _ = star (D (a.re • (1 : ℂ) + a.im • Complex.I)) *
        E (a.re • (1 : ℂ) + a.im • Complex.I) +
        star (D ((-a.im) • (1 : ℂ) + a.re • Complex.I)) *
          E ((-a.im) • (1 : ℂ) + a.re • Complex.I) := by rw [← ha, ← hai]
    _ = _ := by
      simp only [map_add, map_smul, Complex.real_smul, Complex.star_def,
        map_add, map_mul, Complex.conj_ofReal, Complex.normSq_apply]
      push_cast
      ring

private theorem straight_hasDerivAt (z v : ℂ) (t : ℝ) :
    HasDerivAt (fun r : ℝ => z + (r : ℂ) * v) v t := by
  have h : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  convert (h.mul_const v).const_add z using 1 <;> simp

theorem centredFirst_eq_fderiv (F : ℂ → ℂ) (z v : ℂ)
    (hF : DifferentiableAt ℝ F z) : centredFirst F z v = fderiv ℝ F z v := by
  have hF' : DifferentiableAt ℝ F (z + (0 : ℂ) * v) := by simpa using hF
  simpa only [centredFirst, Complex.ofReal_zero, zero_mul, add_zero] using
    (hF'.hasFDerivAt.comp_hasDerivAt 0 (straight_hasDerivAt z v 0)).deriv

theorem centredFirst_actualMobius_pullback (g : SL(2, ℤ)) (z : UpperHalfPlane)
    (F : ℂ → ℂ) (hF : DifferentiableAt ℝ F (actualMobius g z)) (v : ℂ) :
    centredFirst (fun w => F (actualMobius g w)) z v =
      fderiv ℝ F (actualMobius g z) (factor g z * v) := by
  have hc := linePullback_hasDerivAt g z v 0 (by simpa using z.im_pos)
  have hF' : DifferentiableAt ℝ F (linePullback g z v 0) := by
    simpa only [linePullback, Complex.ofReal_zero, zero_mul, add_zero] using hF
  simpa only [centredFirst, linePullback, lineVelocity, Complex.ofReal_zero,
    zero_mul, add_zero] using (hF'.hasFDerivAt.comp_hasDerivAt 0 hc).deriv

theorem centredDirichlet_actualMobius_pullback
    (g : SL(2, ℤ)) (z : UpperHalfPlane) (F G : ℂ → ℂ)
    (hF : DifferentiableAt ℝ F (actualMobius g z))
    (hG : DifferentiableAt ℝ G (actualMobius g z)) :
    centredDirichlet (fun w => F (actualMobius g w)) (fun w => G (actualMobius g w)) z =
      (Complex.normSq (factor g z) : ℂ) * centredDirichlet F G (actualMobius g z) := by
  unfold centredDirichlet
  rw [centredFirst_actualMobius_pullback g z F hF 1,
    centredFirst_actualMobius_pullback g z G hG 1,
    centredFirst_actualMobius_pullback g z F hF Complex.I,
    centredFirst_actualMobius_pullback g z G hG Complex.I,
    centredFirst_eq_fderiv F _ 1 hF, centredFirst_eq_fderiv G _ 1 hG,
    centredFirst_eq_fderiv F _ Complex.I hF, centredFirst_eq_fderiv G _ Complex.I hG]
  simpa only [mul_one] using real_linear_sesquilinear_conformal_trace
    (fderiv ℝ F (actualMobius g z)) (fderiv ℝ G (actualMobius g z)) (factor g z)

theorem centredDirichlet_complexFunction_eq_chartDirichlet
    (F G : ℝ × ℝ → ℂ) (z : ℂ) :
    centredDirichlet (complexFunction F) (complexFunction G) z =
      chartDirichlet F G (pairOfComplex z) := by
  have hx (H : ℝ × ℝ → ℂ) : centredFirst (complexFunction H) z 1 = sliceDx H (pairOfComplex z) := by
    have heq : (fun t : ℝ => complexFunction H (z + (t : ℂ) * 1)) =
        (fun t : ℝ => H (z.re + t, z.im)) := by
      funext t
      simp [complexFunction, pairOfComplex]
    unfold centredFirst
    rw [heq, deriv_comp_const_add]
    simp only [add_zero, sliceDx, pairOfComplex]
  have hy (H : ℝ × ℝ → ℂ) : centredFirst (complexFunction H) z Complex.I = sliceDy H (pairOfComplex z) := by
    have heq : (fun t : ℝ => complexFunction H (z + (t : ℂ) * Complex.I)) =
        (fun t : ℝ => H (z.re, z.im + t)) := by
      funext t
      simp [complexFunction, pairOfComplex, Complex.mul_re, Complex.mul_im]
    unfold centredFirst
    rw [heq, deriv_comp_const_add]
    simp only [add_zero, sliceDy, pairOfComplex]
  unfold centredDirichlet chartDirichlet
  rw [hx F, hy F, hx G, hy G]

theorem centredDirichlet_congr_of_eventuallyEq
    (F F' G G' : ℂ → ℂ) (z : ℂ)
    (hF : F =ᶠ[𝓝 z] F') (hG : G =ᶠ[𝓝 z] G') :
    centredDirichlet F G z = centredDirichlet F' G' z := by
  have hd (H H' : ℂ → ℂ) (h : H =ᶠ[𝓝 z] H') (v : ℂ) :
      centredFirst H z v = centredFirst H' z v := by
    have hc : Continuous (fun t : ℝ => z + (t : ℂ) * v) := by fun_prop
    have ht : Tendsto (fun t : ℝ => z + (t : ℂ) * v) (𝓝 0) (𝓝 z) := by
      simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hc.continuousAt (x := 0)
    exact (h.comp_tendsto ht).deriv_eq
  unfold centredDirichlet
  rw [hd F F' hF 1, hd F F' hF Complex.I, hd G G' hG 1, hd G G' hG Complex.I]

/-- Actual local identity of rational chart pullback and the genuine
upper-half-plane action, used BEFORE differentiating arbitrary outers. -/
theorem complexFunction_mobius_pullback_eventually
    (g : SL(2, ℤ)) (F : ℝ × ℝ → ℂ) (z : UpperHalfPlane) :
    complexFunction (fun p => F (mobiusChart g p)) =ᶠ[𝓝 (z : ℂ)]
      (fun w => complexFunction F (actualMobius g w)) := by
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  unfold complexFunction
  congr 1
  have hp : 0 < (pairOfComplex w).2 := hw
  rw [mobiusChart_eq_actual g hp]
  have hz : chartLift (pairOfComplex w) = (⟨w, hw⟩ : UpperHalfPlane) := by
    rw [chartLift_of_positive hp]
    apply Subtype.ext
    simp [complexOfPair, pairOfComplex]
  rw [hz]
  simpa only [pairOfComplex] using
    (congrArg pairOfComplex (actualMobius_eq_smul g (⟨w, hw⟩ : UpperHalfPlane))).symm

/-- Actual Mobius covariance for arbitrary C1 outer functions, expressed
in the same literal coordinate slice derivatives as the actual Green form. -/
theorem chartDirichlet_comp_mobiusChart
    (g : SL(2, ℤ)) (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) (hp : 0 < p.2)
    (hF : ContDiffAt ℝ 1 F (mobiusChart g p))
    (hG : ContDiffAt ℝ 1 G (mobiusChart g p)) :
    chartDirichlet (fun q => F (mobiusChart g q)) (fun q => G (mobiusChart g q)) p =
      (Complex.normSq (factor g (complexOfPair p)) : ℂ) * chartDirichlet F G (mobiusChart g p) := by
  let z : UpperHalfPlane := ⟨complexOfPair p, hp⟩
  have hz : pairOfComplex (z : ℂ) = p := rfl
  have hgp : pairOfComplex (actualMobius g z) = mobiusChart g p := by
    have h := mobiusChart_eq_actual g hp
    rw [chartLift_of_positive hp] at h
    simpa only [pairOfComplex, actualMobius_eq_smul] using h.symm
  have hpair : ContDiff ℝ 1 pairOfComplex := Complex.reCLM.contDiff.prodMk Complex.imCLM.contDiff
  have hFc : DifferentiableAt ℝ (complexFunction F) (actualMobius g z) := by
    have hFp : ContDiffAt ℝ 1 F (pairOfComplex (actualMobius g z)) := by rwa [hgp]
    exact (hFp.comp _ hpair.contDiffAt).differentiableAt (by norm_num)
  have hGc : DifferentiableAt ℝ (complexFunction G) (actualMobius g z) := by
    have hGp : ContDiffAt ℝ 1 G (pairOfComplex (actualMobius g z)) := by rwa [hgp]
    exact (hGp.comp _ hpair.contDiffAt).differentiableAt (by norm_num)
  calc
    _ = centredDirichlet (complexFunction (fun q => F (mobiusChart g q)))
        (complexFunction (fun q => G (mobiusChart g q))) z := by
      rw [centredDirichlet_complexFunction_eq_chartDirichlet, hz]
    _ = centredDirichlet (fun w => complexFunction F (actualMobius g w))
        (fun w => complexFunction G (actualMobius g w)) z :=
      centredDirichlet_congr_of_eventuallyEq _ _ _ _ _
        (complexFunction_mobius_pullback_eventually g F z)
        (complexFunction_mobius_pullback_eventually g G z)
    _ = (Complex.normSq (factor g z) : ℂ) *
        centredDirichlet (complexFunction F) (complexFunction G) (actualMobius g z) :=
      centredDirichlet_actualMobius_pullback g z _ _ hFc hGc
    _ = _ := by rw [centredDirichlet_complexFunction_eq_chartDirichlet, hgp]

/-- Exact compensation by the ACTUAL transformed imaginary coordinate. -/
theorem hyperbolicChartDirichlet_comp_mobiusChart
    (g : SL(2, ℤ)) (F G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) (hp : 0 < p.2)
    (hF : ContDiffAt ℝ 1 F (mobiusChart g p))
    (hG : ContDiffAt ℝ 1 G (mobiusChart g p)) :
    hyperbolicChartDirichlet (fun q => F (mobiusChart g q)) (fun q => G (mobiusChart g q)) p =
      hyperbolicChartDirichlet F G (mobiusChart g p) := by
  let z : UpperHalfPlane := ⟨complexOfPair p, hp⟩
  have hheight : (p.2 : ℂ) ^ 2 * (Complex.normSq (factor g (complexOfPair p)) : ℂ) =
      ((mobiusChart g p).2 : ℂ) ^ 2 := by
    have h := height_sq_mul_normSq_factor g z
    have hg := mobiusChart_eq_actual g hp
    rw [chartLift_of_positive hp] at hg
    have hi : (mobiusChart g p).2 = (g • z).im := congrArg Prod.snd hg
    rw [hi]
    exact_mod_cast h
  unfold hyperbolicChartDirichlet
  rw [chartDirichlet_comp_mobiusChart g F G p hp hF hG, ← mul_assoc, hheight]

theorem hyperbolicChartDirichlet_comp_gamma0
    (N : ℕ) (γ : CongruenceSubgroup.Gamma0 N) (F G : ℝ × ℝ → ℂ)
    (p : ℝ × ℝ) (hp : 0 < p.2)
    (hF : ContDiffAt ℝ 1 F (mobiusChart (γ : SL(2, ℤ)) p))
    (hG : ContDiffAt ℝ 1 G (mobiusChart (γ : SL(2, ℤ)) p)) :
    hyperbolicChartDirichlet (fun q => F (mobiusChart (γ : SL(2, ℤ)) q))
      (fun q => G (mobiusChart (γ : SL(2, ℤ)) q)) p =
        hyperbolicChartDirichlet F G (mobiusChart (γ : SL(2, ℤ)) p) :=
  hyperbolicChartDirichlet_comp_mobiusChart (γ : SL(2, ℤ)) F G p hp hF hG

/-- The self-pairing is the genuine sum of two nonnegative gradient
squares, with no eigenfunction or formal energy assumption. -/
theorem chartDirichlet_self_eq (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    chartDirichlet F F p =
      ((Complex.normSq (sliceDx F p) + Complex.normSq (sliceDy F p) : ℝ) : ℂ) := by
  simp only [chartDirichlet, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_add]

theorem chartDirichlet_self_re_nonneg (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    0 ≤ (chartDirichlet F F p).re := by
  rw [chartDirichlet_self_eq]
  exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem hyperbolicChartDirichlet_self_re_nonneg (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    0 ≤ (hyperbolicChartDirichlet F F p).re := by
  simp only [hyperbolicChartDirichlet, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (sq_nonneg _) (chartDirichlet_self_re_nonneg F p)

end
end ImbalancedChen.Part3.ActualMobiusDirichletCovariance20261025a
