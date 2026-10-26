import ImbalancedChen.Part3ZeroCuspActualSmoothCompactPullback

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO FORMAL CREDIT.

Actual complex action derivatives of the REAL normalized zeroSL matrix
supply its conformal two-jet. The genuine real outer-Hessian chain and
actual hyperbolic height compensation then prove covariance of the
EXISTING chartMaass and upperMaass under the literal zero chart. No
covariance, eigenrelation or transformed-output identification is a premise.
-/

noncomputable section

namespace ImbalancedChen.Part3.ZeroCuspActualMaassCovariance20261026b

open Set Complex Filter Topology Matrix Matrix.SpecialLinearGroup
open scoped UpperHalfPlane
open ImbalancedChen.Part3.InfinityZeroArithmetic20261025a
open ImbalancedChen.Part3.ZeroCuspActualSmoothCompactPullback20261026b
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.ActualMobiusConformalTwoJet20261025a (real_bilinear_conformal_trace)
open ImbalancedChen.Part3.ActualMobiusMaassEquivariance20261025a
open ImbalancedChen.Part3.ActualGamma0MaassDescent20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz

def zeroGL (N : ℕ) (hN : 0 < N) : GL (Fin 2) ℝ :=
  SpecialLinearGroup.mapGL ℝ (zeroSL N hN)

/-- The actual real action, locally extended by ofComplex for derivatives. -/
def zeroActualMobius (N : ℕ) (hN : 0 < N) (w : ℂ) : ℂ :=
  ((zeroGL N hN • UpperHalfPlane.ofComplex w : UpperHalfPlane) : ℂ)

def zeroFactor (N : ℕ) (hN : 0 < N) (w : ℂ) : ℂ :=
  1 / UpperHalfPlane.denom (zeroGL N hN) w ^ 2

def zeroCurvature (N : ℕ) (hN : 0 < N) (w : ℂ) : ℂ :=
  -(2 * ((zeroGL N hN) 1 0 : ℂ)) / UpperHalfPlane.denom (zeroGL N hN) w ^ 3

theorem zeroActualMobius_eq_smul (N : ℕ) (hN : 0 < N) (z : UpperHalfPlane) :
    zeroActualMobius N hN z = ((zeroSL N hN • z : UpperHalfPlane) : ℂ) := by
  simp [zeroActualMobius, zeroGL, UpperHalfPlane.ofComplex_apply]

theorem zeroActualMobius_hasDerivAt (N : ℕ) (hN : 0 < N) (z : UpperHalfPlane) :
    HasDerivAt (zeroActualMobius N hN) (zeroFactor N hN z) (z : ℂ) := by
  have hdet : (zeroGL N hN).val.det = 1 := by simp [zeroGL]
  have h := UpperHalfPlane.hasStrictDerivAt_smul
    (g := zeroGL N hN) (by rw [hdet]; norm_num) z
  simpa only [zeroActualMobius, zeroFactor, hdet, Complex.ofReal_one] using h.hasDerivAt

theorem zeroFactor_hasDerivAt (N : ℕ) (hN : 0 < N) (z : UpperHalfPlane) :
    HasDerivAt (zeroFactor N hN) (zeroCurvature N hN z) (z : ℂ) := by
  have hd := UpperHalfPlane.denom_ne_zero (zeroGL N hN) z
  have hden : HasDerivAt (fun w : ℂ => UpperHalfPlane.denom (zeroGL N hN) w)
      ((zeroGL N hN) 1 0 : ℂ) (z : ℂ) := by
    simpa only [UpperHalfPlane.denom] using
      ((hasDerivAt_id (z : ℂ)).const_mul ((zeroGL N hN) 1 0 : ℂ)).add_const
        ((zeroGL N hN) 1 1 : ℂ)
  convert (hden.pow 2).inv (pow_ne_zero 2 hd) using 1
  · simp only [zeroFactor, one_div]
  · dsimp [zeroCurvature]
    field_simp [hd]
    <;> ring

def zeroLine (N : ℕ) (hN : 0 < N) (z v : ℂ) (t : ℝ) : ℂ :=
  zeroActualMobius N hN (z + (t : ℂ) * v)

def zeroVelocity (N : ℕ) (hN : 0 < N) (z v : ℂ) (t : ℝ) : ℂ :=
  zeroFactor N hN (z + (t : ℂ) * v) * v

theorem zeroLine_hasDerivAt (N : ℕ) (hN : 0 < N) (z v : ℂ)
    (t : ℝ) (ht : 0 < (z + (t : ℂ) * v).im) :
    HasDerivAt (zeroLine N hN z v) (zeroVelocity N hN z v t) t := by
  have hp : HasDerivAt (fun w : ℂ => z + w * v) v (t : ℂ) := by
    convert ((hasDerivAt_id (t : ℂ)).mul_const v).const_add z using 1 <;> ring
  have h := (zeroActualMobius_hasDerivAt N hN ⟨z + (t : ℂ) * v, ht⟩).comp (t : ℂ) hp
  simpa only [zeroLine, zeroVelocity] using h.comp_ofReal

theorem zeroVelocity_hasDerivAt_zero (N : ℕ) (hN : 0 < N)
    (z : UpperHalfPlane) (v : ℂ) :
    HasDerivAt (zeroVelocity N hN z v) (zeroCurvature N hN z * v * v) 0 := by
  have hp : HasDerivAt (fun w : ℂ => (z : ℂ) + w * v) v 0 := by
    convert ((hasDerivAt_id (0 : ℂ)).mul_const v).const_add (z : ℂ) using 1 <;> ring
  have hf : HasDerivAt (zeroFactor N hN) (zeroCurvature N hN z) ((z : ℂ) + (0 : ℂ) * v) := by
    simpa only [zero_mul, add_zero] using zeroFactor_hasDerivAt N hN z
  have h := (hf.comp (0 : ℂ) hp).comp_ofReal.mul_const v
  simpa only [zeroVelocity] using h

theorem zero_height_sq_mul_normSq_factor (N : ℕ) (hN : 0 < N) (z : UpperHalfPlane) :
    z.im ^ 2 * Complex.normSq (zeroFactor N hN z) = (zeroSL N hN • z).im ^ 2 := by
  have him : (zeroSL N hN • z).im =
      z.im / Complex.normSq (UpperHalfPlane.denom (zeroGL N hN) (z : ℂ)) := by
    simpa [zeroGL] using z.im_smul_eq_div_normSq (zeroGL N hN)
  have hn : Complex.normSq (zeroFactor N hN z) =
      1 / Complex.normSq (UpperHalfPlane.denom (zeroGL N hN) (z : ℂ)) ^ 2 := by
    simp [zeroFactor, Complex.normSq_div, map_pow]
  rw [hn, him, div_pow]
  ring

/-- The actual real outer-function second chain, including its acceleration. -/
theorem centredSecond_zeroActualMobius (N : ℕ) (hN : 0 < N)
    (z : UpperHalfPlane) (F : ℂ → ℂ)
    (hF : ContDiffAt ℝ 2 F (zeroActualMobius N hN z)) (v : ℂ) :
    centredSecond (fun w => F (zeroActualMobius N hN w)) z v =
      (fderiv ℝ (fderiv ℝ F) (zeroActualMobius N hN z) (zeroFactor N hN z * v))
        (zeroFactor N hN z * v) +
      fderiv ℝ F (zeroActualMobius N hN z) (zeroCurvature N hN z * v * v) := by
  have hpos : ∀ᶠ t : ℝ in 𝓝 0, 0 < ((z : ℂ) + (t : ℂ) * v).im := by
    have hc : Continuous (fun t : ℝ => ((z : ℂ) + (t : ℂ) * v).im) := by fun_prop
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
      hc.continuousAt.eventually (Ioi_mem_nhds z.im_pos)
  have hc : ∀ᶠ t : ℝ in 𝓝 0,
      HasDerivAt (zeroLine N hN z v) (zeroVelocity N hN z v t) t := by
    filter_upwards [hpos] with t ht
    exact zeroLine_hasDerivAt N hN z v t ht
  have h := second_curve_chain F (zeroLine N hN z v) (zeroVelocity N hN z v) 0
    (zeroCurvature N hN z * v * v)
    (by simpa only [zeroLine, Complex.ofReal_zero, zero_mul, add_zero] using hF)
    hc (zeroVelocity_hasDerivAt_zero N hN z v)
  simpa only [centredSecond, zeroLine, zeroVelocity, Complex.ofReal_zero, zero_mul, add_zero] using h

/-- The acceleration trace cancels; the genuine Hessian trace and actual
height formula identify the existing negative hyperbolic expression. -/
theorem centredMaass_zeroActualMobius (N : ℕ) (hN : 0 < N)
    (z : UpperHalfPlane) (F : ℂ → ℂ)
    (hF : ContDiffAt ℝ 2 F ((zeroSL N hN • z : UpperHalfPlane) : ℂ)) :
    centredMaass (fun w => F (zeroActualMobius N hN w)) z =
      centredMaass F ((zeroSL N hN • z : UpperHalfPlane) : ℂ) := by
  have hFa : ContDiffAt ℝ 2 F (zeroActualMobius N hN z) := by
    simpa only [zeroActualMobius_eq_smul] using hF
  let B := fderiv ℝ (fderiv ℝ F) (zeroActualMobius N hN z)
  let D := fderiv ℝ F (zeroActualMobius N hN z)
  let a := zeroFactor N hN z
  let b := zeroCurvature N hN z
  have hheight : (z.im : ℂ) ^ 2 * (Complex.normSq a : ℂ) = ((zeroSL N hN • z).im : ℂ) ^ 2 := by
    exact_mod_cast zero_height_sq_mul_normSq_factor N hN z
  rw [centredMaass, centredMaass,
    centredSecond_zeroActualMobius N hN z F hFa 1,
    centredSecond_zeroActualMobius N hN z F hFa Complex.I,
    centredSecond_eq_hessian F _ 1 hF,
    centredSecond_eq_hessian F _ Complex.I hF]
  change -((z.im : ℂ) ^ 2 *
    ((B (a * 1) (a * 1) + D (b * 1 * 1)) +
      (B (a * Complex.I) (a * Complex.I) + D (b * Complex.I * Complex.I)))) = _
  simp only [mul_one, mul_assoc, Complex.I_sq, mul_neg, mul_one, map_neg]
  calc
    _ = -((z.im : ℂ) ^ 2 * (B a a + B (a * Complex.I) (a * Complex.I))) := by ring
    _ = -((z.im : ℂ) ^ 2 * ((Complex.normSq a : ℂ) * (B 1 1 + B Complex.I Complex.I))) := by
      rw [real_bilinear_conformal_trace]
    _ = -(((zeroSL N hN • z).im : ℂ) ^ 2 * (B 1 1 + B Complex.I Complex.I)) := by
      rw [← mul_assoc, hheight]
    _ = _ := by simp only [B, zeroActualMobius_eq_smul]

private theorem centredMaass_zero_germ (F G : ℂ → ℂ) (z : ℂ)
    (h : F =ᶠ[𝓝 z] G) : centredMaass F z = centredMaass G z := by
  have hs (v : ℂ) : centredSecond F z v = centredSecond G z v := by
    have hc : Continuous (fun t : ℝ => z + (t : ℂ) * v) := by fun_prop
    have ht : Tendsto (fun t : ℝ => z + (t : ℂ) * v) (𝓝 0) (𝓝 z) := by
      simpa only [Complex.ofReal_zero, zero_mul, add_zero] using hc.continuousAt (x := 0)
    exact (h.comp_tendsto ht).deriv.deriv_eq
  unfold centredMaass
  rw [hs 1, hs Complex.I]

private theorem zero_complex_chart_germ (N : ℕ) (hN : 0 < N)
    (F : ℝ × ℝ → ℂ) (z : UpperHalfPlane) :
    complexFunction (fun p => F (zeroRealChart N hN p)) =ᶠ[𝓝 (z : ℂ)]
      (fun w => complexFunction F (zeroActualMobius N hN w)) := by
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  unfold complexFunction
  congr 1
  have hp : 0 < (pairOfComplex w).2 := hw
  rw [zeroRealChart_eq_actual N hN hp]
  have hz : chartLift (pairOfComplex w) = (⟨w, hw⟩ : UpperHalfPlane) := by
    rw [chartLift_of_positive hp]
    apply Subtype.ext
    simp [complexOfPair, pairOfComplex]
  rw [hz]
  simpa only [pairOfComplex] using
    (congrArg pairOfComplex (zeroActualMobius_eq_smul N hN (⟨w, hw⟩ : UpperHalfPlane))).symm

theorem chartMaass_comp_zeroRealChart (N : ℕ) (hN : 0 < N)
    (F : ℝ × ℝ → ℂ) (p : ℝ × ℝ) (hp : 0 < p.2)
    (hF : ContDiffAt ℝ 2 F (zeroRealChart N hN p)) :
    chartMaass (fun q => F (zeroRealChart N hN q)) p =
      chartMaass F (zeroRealChart N hN p) := by
  let z : UpperHalfPlane := ⟨complexOfPair p, hp⟩
  have hz : pairOfComplex (z : ℂ) = p := rfl
  have hgp : pairOfComplex ((zeroSL N hN • z : UpperHalfPlane) : ℂ) = zeroRealChart N hN p := by
    have heq := zeroRealChart_eq_actual N hN hp
    rw [chartLift_of_positive hp] at heq
    exact heq.symm
  have hpair : ContDiff ℝ 2 pairOfComplex := Complex.reCLM.contDiff.prodMk Complex.imCLM.contDiff
  have hFc : ContDiffAt ℝ 2 (complexFunction F) ((zeroSL N hN • z : UpperHalfPlane) : ℂ) := by
    have hFp : ContDiffAt ℝ 2 F (pairOfComplex ((zeroSL N hN • z : UpperHalfPlane) : ℂ)) := by
      rw [hgp]
      exact hF
    exact hFp.comp _ hpair.contDiffAt
  calc
    _ = centredMaass (complexFunction (fun q => F (zeroRealChart N hN q))) (z : ℂ) := by
      rw [centredMaass_complexFunction_eq_chartMaass, hz]
    _ = centredMaass (fun w => complexFunction F (zeroActualMobius N hN w)) (z : ℂ) :=
      centredMaass_zero_germ _ _ _ (zero_complex_chart_germ N hN F z)
    _ = centredMaass (complexFunction F) ((zeroSL N hN • z : UpperHalfPlane) : ℂ) :=
      centredMaass_zeroActualMobius N hN z (complexFunction F) hFc
    _ = chartMaass F (zeroRealChart N hN p) := by
      rw [centredMaass_complexFunction_eq_chartMaass, hgp]

/-- Native upperMaass covariance under the literal REAL zero chart. -/
theorem upperMaass_zeroSeedPullback (N : ℕ) (hN : 0 < N)
    (f : UpperHalfPlane → ℂ) (hf : ContDiffOn ℝ 2 (extendUpper f) positiveChart)
    (z : UpperHalfPlane) :
    upperMaass (zeroSeedPullback N hN f) z = upperMaass f (zeroSL N hN • z) := by
  let p : ℝ × ℝ := (z.re, z.im)
  have hp : 0 < p.2 := z.im_pos
  have hopen : IsOpen positiveChart := isOpen_lt continuous_const continuous_snd
  have hlocal : extendUpper (zeroSeedPullback N hN f) =ᶠ[𝓝 p]
      (fun q => extendUpper f (zeroRealChart N hN q)) := by
    filter_upwards [hopen.mem_nhds hp] with q hq
    exact extendUpper_zeroSeedPullback N hN f hq
  have hq := zeroRealChart_mapsTo_positive N hN hp
  have hgeom := chartMaass_comp_zeroRealChart N hN (extendUpper f) p hp
    ((hf _ hq).contDiffAt (hopen.mem_nhds hq))
  change chartMaass (extendUpper (zeroSeedPullback N hN f)) p = _
  rw [chartMaass_eq_of_eventuallyEq hlocal, hgeom, zeroRealChart_eq_actual N hN hp, chartLift_pair]
  rfl

end ImbalancedChen.Part3.ZeroCuspActualMaassCovariance20261026b
