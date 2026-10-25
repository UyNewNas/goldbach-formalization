import ImbalancedChen.Part3ActualMobiusConformalTwoJet
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

General C2 outer-function chain rule, actual Mobius two-jet trace, and
hyperbolic height compensation prove equivariance of the EXISTING
chartMaass under the EXISTING mobiusChart at every positive-height point.
This is not an eigenfunction computation and no chain/equivariance target
is among the premises. The outer chart function may be arbitrary complex
valued C2. Quotient operator closure/spectral conclusions remain OPEN.
-/

namespace ImbalancedChen.Part3.ActualMobiusMaassEquivariance20261025a

noncomputable section
open Complex Filter Topology Set Matrix
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.ActualMobiusConformalTwoJet20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a

/-- Genuine local real second-derivative chain rule along a curve. The
derivative data are ordinary first derivatives, not a Laplacian premise. -/
theorem second_curve_chain (F : ℂ → ℂ) (c v : ℝ → ℂ) (x : ℝ) (a : ℂ)
    (hF : ContDiffAt ℝ 2 F (c x))
    (hc : ∀ᶠ t : ℝ in 𝓝 x, HasDerivAt c (v t) t)
    (hv : HasDerivAt v a x) :
    deriv (deriv (fun t : ℝ => F (c t))) x =
      (fderiv ℝ (fderiv ℝ F) (c x) (v x)) (v x) + fderiv ℝ F (c x) a := by
  have hc0 := hc.self_of_nhds
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) (c x) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDc : HasDerivAt (fun t : ℝ => fderiv ℝ F (c t))
      (fderiv ℝ (fderiv ℝ F) (c x) (v x)) x :=
    hDF.hasFDerivAt.comp_hasDerivAt x hc0
  have hprod := hDc.clm_apply hv
  have hlocal : ∀ᶠ t : ℝ in 𝓝 x, ContDiffAt ℝ 2 F (c t) :=
    hc0.continuousAt (hF.eventually (by norm_num))
  have heq : deriv (fun t : ℝ => F (c t)) =ᶠ[𝓝 x]
      (fun t : ℝ => (fderiv ℝ F (c t)) (v t)) := by
    filter_upwards [hc, hlocal] with t hct hFt
    exact (hFt.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t hct |>.deriv
  exact (hprod.congr_of_eventuallyEq heq.symm).deriv

def centredSecond (F : ℂ → ℂ) (z v : ℂ) : ℂ :=
  deriv (deriv (fun t : ℝ => F (z + (t : ℂ) * v))) 0

def centredMaass (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  -((z.im : ℂ) ^ 2 * (centredSecond F z 1 + centredSecond F z Complex.I))

private theorem straight_hasDerivAt (z v : ℂ) (t : ℝ) :
    HasDerivAt (fun r : ℝ => z + (r : ℂ) * v) v t := by
  have h : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  convert (h.mul_const v).const_add z using 1 <;> simp

theorem centredSecond_eq_hessian (F : ℂ → ℂ) (z v : ℂ)
    (hF : ContDiffAt ℝ 2 F z) :
    centredSecond F z v = (fderiv ℝ (fderiv ℝ F) z v) v := by
  have h := second_curve_chain F (fun t : ℝ => z + (t : ℂ) * v)
    (fun _ : ℝ => v) 0 0
    (by simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hF)
    (Eventually.of_forall (straight_hasDerivAt z v)) (hasDerivAt_const 0 v)
  simpa only [centredSecond, Complex.ofReal_zero, zero_mul, add_zero, map_zero, add_zero] using h

theorem centredSecond_actualMobius_pullback
    (g : SL(2, ℤ)) (z : UpperHalfPlane) (F : ℂ → ℂ)
    (hF : ContDiffAt ℝ 2 F (actualMobius g z)) (v : ℂ) :
    centredSecond (fun w => F (actualMobius g w)) z v =
      (fderiv ℝ (fderiv ℝ F) (actualMobius g z) (factor g z * v)) (factor g z * v) +
        fderiv ℝ F (actualMobius g z) (curvature g z * v * v) := by
  have hpos : ∀ᶠ t : ℝ in 𝓝 0, 0 < ((z : ℂ) + (t : ℂ) * v).im := by
    have hc : Continuous (fun t : ℝ => ((z : ℂ) + (t : ℂ) * v).im) := by fun_prop
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
      hc.continuousAt.eventually (Ioi_mem_nhds z.im_pos)
  have hc : ∀ᶠ t : ℝ in 𝓝 0,
      HasDerivAt (linePullback g z v) (lineVelocity g z v t) t := by
    filter_upwards [hpos] with t ht
    exact linePullback_hasDerivAt g z v t ht
  have h := second_curve_chain F (linePullback g z v) (lineVelocity g z v) 0
    (curvature g z * v * v)
    (by simpa only [linePullback, Complex.ofReal_zero, zero_mul, add_zero] using hF)
    hc (lineVelocity_hasDerivAt_zero g z v)
  simpa only [centredSecond, linePullback, lineVelocity, Complex.ofReal_zero,
    zero_mul, add_zero] using h

/-- Full arbitrary C2 pullback equivariance in centred real coordinates,
proved from the actual first/second action derivatives and real Hessian. -/
theorem centredMaass_actualMobius_pullback
    (g : SL(2, ℤ)) (z : UpperHalfPlane) (F : ℂ → ℂ)
    (hF : ContDiffAt ℝ 2 F ((g • z : UpperHalfPlane) : ℂ)) :
    centredMaass (fun w => F (actualMobius g w)) z =
      centredMaass F ((g • z : UpperHalfPlane) : ℂ) := by
  have hFa : ContDiffAt ℝ 2 F (actualMobius g z) := by
    simpa only [actualMobius_eq_smul] using hF
  let B := fderiv ℝ (fderiv ℝ F) (actualMobius g z)
  let D := fderiv ℝ F (actualMobius g z)
  let a := factor g z
  let b := curvature g z
  have hB := real_bilinear_conformal_trace B a
  have hheight : (z.im : ℂ) ^ 2 * (Complex.normSq a : ℂ) = ((g • z).im : ℂ) ^ 2 := by
    exact_mod_cast height_sq_mul_normSq_factor g z
  rw [centredMaass, centredMaass,
    centredSecond_actualMobius_pullback g z F hFa 1,
    centredSecond_actualMobius_pullback g z F hFa Complex.I,
    centredSecond_eq_hessian F _ 1 hF,
    centredSecond_eq_hessian F _ Complex.I hF]
  change -((z.im : ℂ) ^ 2 *
    ((B (a * 1) (a * 1) + D (b * 1 * 1)) +
      (B (a * Complex.I) (a * Complex.I) + D (b * Complex.I * Complex.I)))) = _
  simp only [mul_one, mul_assoc, Complex.I_sq, mul_neg, mul_one, map_neg]
  calc
    _ = -((z.im : ℂ) ^ 2 * (B a a + B (a * Complex.I) (a * Complex.I))) := by ring
    _ = -((z.im : ℂ) ^ 2 * ((Complex.normSq a : ℂ) * (B 1 1 + B Complex.I Complex.I))) := by rw [hB]
    _ = -(((g • z).im : ℂ) ^ 2 * (B 1 1 + B Complex.I Complex.I)) := by
      rw [← mul_assoc, hheight]
    _ = _ := by simp only [B, actualMobius_eq_smul]

def pairOfComplex (z : ℂ) : ℝ × ℝ := (z.re, z.im)
def complexFunction (F : ℝ × ℝ → ℂ) (z : ℂ) : ℂ := F (pairOfComplex z)

private theorem pairOfComplex_contDiff : ContDiff ℝ 2 pairOfComplex := by
  exact Complex.reCLM.contDiff.prodMk Complex.imCLM.contDiff

private theorem second_const_add (f : ℝ → ℂ) (a : ℝ) :
    deriv (deriv (fun t : ℝ => f (a + t))) 0 = deriv (deriv f) a := by
  have heq : deriv (fun t : ℝ => f (a + t)) = (fun t : ℝ => deriv f (a + t)) := by
    funext t
    exact deriv_comp_const_add f a t
  rw [heq, deriv_comp_const_add]
  simp

/-- This centred-coordinate operator is exactly the EXISTING chartMaass,
not a new substitute operator. No regularity is needed for translations. -/
theorem centredMaass_complexFunction_eq_chartMaass (F : ℝ × ℝ → ℂ) (z : ℂ) :
    centredMaass (complexFunction F) z = chartMaass F (pairOfComplex z) := by
  have hx : (fun t : ℝ => complexFunction F (z + (t : ℂ) * 1)) =
      (fun t : ℝ => F (z.re + t, z.im)) := by
    funext t
    simp [complexFunction, pairOfComplex]
  have hy : (fun t : ℝ => complexFunction F (z + (t : ℂ) * Complex.I)) =
      (fun t : ℝ => F (z.re, z.im + t)) := by
    funext t
    simp [complexFunction, pairOfComplex, Complex.mul_re, Complex.mul_im]
  unfold centredMaass centredSecond
  rw [hx, hy, second_const_add, second_const_add]
  rfl

private theorem centredMaass_congr_of_eventuallyEq
    (F G : ℂ → ℂ) (z : ℂ) (h : F =ᶠ[𝓝 z] G) :
    centredMaass F z = centredMaass G z := by
  have hs (v : ℂ) : centredSecond F z v = centredSecond G z v := by
    have hc : Continuous (fun t : ℝ => z + (t : ℂ) * v) := by fun_prop
    have ht : Tendsto (fun t : ℝ => z + (t : ℂ) * v) (𝓝 0) (𝓝 z) := by
      simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hc.continuousAt (x := 0)
    exact (h.comp_tendsto ht).deriv.deriv_eq
  unfold centredMaass
  rw [hs 1, hs Complex.I]

/-- Exact local equality between the rational chart pullback and the
actual upper-half-plane action, before differentiating. -/
private theorem complexFunction_mobius_eventually
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

/-- Equivariance of the ACTUAL previously defined negative hyperbolic
chart Laplacian under the ACTUAL previously defined Mobius chart. -/
theorem chartMaass_comp_mobiusChart
    (g : SL(2, ℤ)) (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) (hp : 0 < p.2)
    (hF : ContDiffAt ℝ 2 F (mobiusChart g p)) :
    chartMaass (fun q => F (mobiusChart g q)) p =
      chartMaass F (mobiusChart g p) := by
  let z : UpperHalfPlane := ⟨complexOfPair p, hp⟩
  have hz : pairOfComplex (z : ℂ) = p := by rfl
  have hgp : pairOfComplex ((g • z : UpperHalfPlane) : ℂ) = mobiusChart g p := by
    have heq := mobiusChart_eq_actual g hp
    rw [chartLift_of_positive hp] at heq
    exact heq.symm
  have hFc : ContDiffAt ℝ 2 (complexFunction F) ((g • z : UpperHalfPlane) : ℂ) := by
    have hFp : ContDiffAt ℝ 2 F (pairOfComplex ((g • z : UpperHalfPlane) : ℂ)) := by
      rw [hgp]
      exact hF
    exact hFp.comp _ pairOfComplex_contDiff.contDiffAt
  calc
    _ = centredMaass (complexFunction (fun q => F (mobiusChart g q))) (z : ℂ) := by
      rw [centredMaass_complexFunction_eq_chartMaass, hz]
    _ = centredMaass (fun w => complexFunction F (actualMobius g w)) (z : ℂ) :=
      centredMaass_congr_of_eventuallyEq _ _ _ (complexFunction_mobius_eventually g F z)
    _ = centredMaass (complexFunction F) ((g • z : UpperHalfPlane) : ℂ) :=
      centredMaass_actualMobius_pullback g z (complexFunction F) hFc
    _ = chartMaass F (mobiusChart g p) := by
      rw [centredMaass_complexFunction_eq_chartMaass, hgp]

/-- Gamma0 is the literal subgroup of integral determinant-one matrices;
the existing action receives the same chart identity without relabelling
a whole-plane Hilbert-space operator as an automorphic operator. -/
theorem chartMaass_comp_gamma0
    (N : ℕ) (γ : CongruenceSubgroup.Gamma0 N) (F : ℝ × ℝ → ℂ)
    (p : ℝ × ℝ) (hp : 0 < p.2)
    (hF : ContDiffAt ℝ 2 F (mobiusChart (γ : SL(2, ℤ)) p)) :
    chartMaass (fun q => F (mobiusChart (γ : SL(2, ℤ)) q)) p =
      chartMaass F (mobiusChart (γ : SL(2, ℤ)) p) :=
  chartMaass_comp_mobiusChart (γ : SL(2, ℤ)) F p hp hF

private theorem finiteChartFunction_contDiff {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    ContDiff ℝ 2 (finiteChartFunction s T) := by
  apply ContDiff.sum
  intro i _hi
  exact ((T i).horizontal_smooth.comp contDiff_fst).mul
    ((T i).vertical_smooth.comp contDiff_snd)

/-- Concrete term identity for the actual effective-Gamma0 translated
CompactTensor chart. The RHS is the existing actual seed Laplacian,
evaluated after the actual matrix action. No commutation is postulated. -/
theorem chartMaass_translatedFiniteTensorChart
    (N : ℕ) (q : effectiveGamma0 N) {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (p : ℝ × ℝ) (hp : 0 < p.2) :
    chartMaass (translatedFiniteTensorChart N q s T) p =
      finiteCoreLaplacian s T (effectiveMatrixAction N q (chartLift p)) := by
  let g : SL(2, ℤ) := effectiveRepresentative N q
  change chartMaass (fun r => finiteChartFunction s T (mobiusChart g r)) p = _
  rw [chartMaass_comp_mobiusChart g (finiteChartFunction s T) p hp
    (finiteChartFunction_contDiff s T).contDiffAt, mobiusChart_eq_actual g hp]
  simpa only [Complex.measurableEquivRealProd_apply] using
    (finiteCoreLaplacian_eq_chart s T (effectiveMatrixAction N q (chartLift p))).symm

end
end ImbalancedChen.Part3.ActualMobiusMaassEquivariance20261025a
