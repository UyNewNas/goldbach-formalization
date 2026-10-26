import ImbalancedChen.Part3MobiusStrongFirstJetL2Errors
import ImbalancedChen.Part3ActualMobiusDirichletCovariance
import ImbalancedChen.Part3ArbitraryCompactFirstGradientIBP

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The two real-coordinate derivatives of an actual smooth Mobius pullback
are the literal transpose-Jacobian raw jets, separately in both directions.
Actual compact smooth weak tests then give native first-order identities.
No weak derivative or covariance premise is used. This is the smooth
identity whose genuine L2 closure supplies the raw H1 chain rule.
-/

namespace ImbalancedChen.Part3.MobiusSmoothFirstJetWeakTests20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups UpperHalfPlane
open Gamma0CompactTensorPoincareC2Core20261025a ActualMobiusConformalTwoJet20261025a
open ActualMobiusMaassEquivariance20261025a ActualMobiusDirichletCovariance20261025a
open ActualMobiusPairChartL2Transport20261026b MaassWeakOperatorCore20261024zz
open Gamma0CompactGreenProductL120261025a OneCompactFirstGradientIBP20261025a
open CompactC2ProductMollifier20261026a ArbitraryCompactFirstGradientIBP20261026b

theorem centredFirst_chart_x (F : Plane → ℂ) (z : ℂ) :
    centredFirst (complexFunction F) z 1 = sliceDx F (pairOfComplex z) := by
  have heq : (fun t : ℝ => complexFunction F (z+(t : ℂ)*1)) =
      fun t : ℝ => F (z.re+t,z.im) := by
    funext t
    simp [complexFunction,pairOfComplex]
  unfold centredFirst
  rw [heq,deriv_comp_const_add]
  simp only [add_zero,sliceDx,pairOfComplex]

theorem centredFirst_chart_y (F : Plane → ℂ) (z : ℂ) :
    centredFirst (complexFunction F) z Complex.I = sliceDy F (pairOfComplex z) := by
  have heq : (fun t : ℝ => complexFunction F (z+(t : ℂ)*Complex.I)) =
      fun t : ℝ => F (z.re,z.im+t) := by
    funext t
    simp [complexFunction,pairOfComplex,Complex.mul_re,Complex.mul_im]
  unfold centredFirst
  rw [heq,deriv_comp_const_add]
  simp only [add_zero,sliceDy,pairOfComplex]

theorem centredFirst_local_congr {F G : ℂ → ℂ} {z : ℂ}
    (he : F =ᶠ[𝓝 z] G) (v : ℂ) : centredFirst F z v = centredFirst G z v := by
  have hc : Continuous (fun t : ℝ => z+(t : ℂ)*v) := by fun_prop
  have ht : Tendsto (fun t : ℝ => z+(t : ℂ)*v) (𝓝 0) (𝓝 z) := by
    simpa only [Complex.ofReal_zero,zero_mul,add_zero] using hc.continuousAt (x := 0)
  exact (he.comp_tendsto ht).deriv_eq

theorem mobius_pullback_C2 (g : SL(2, ℤ)) {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F) :
    ContDiffOn ℝ 2 (fun p => F (mobiusChart g p)) positiveChart := by
  intro p hp
  exact (((hF.of_le (by simp)).contDiffAt).comp p (mobiusChart_contDiffAt g hp)).contDiffWithinAt

theorem complexFunction_fderiv_basis {F : Plane → ℂ} (hF : ContDiff ℝ ∞ F)
    (w a : ℂ) :
    fderiv ℝ (complexFunction F) w a =
      a.re • directional ex F (pairOfComplex w)+a.im • directional ey F (pairOfComplex w) := by
  have hpair : ContDiff ℝ ∞ pairOfComplex :=
    Complex.reCLM.contDiff.prodMk Complex.imCLM.contDiff
  have hd : DifferentiableAt ℝ (complexFunction F) w :=
    (hF.comp hpair).differentiable (by simp) w
  have hdF : DifferentiableOn ℝ F positiveChart :=
    (hF.differentiable (by simp)).differentiableOn
  have hx : fderiv ℝ (complexFunction F) w 1 = directional ex F (pairOfComplex w) := by
    rw [← centredFirst_eq_fderiv _ _ _ hd,centredFirst_chart_x]
    exact ((hF.differentiable (by simp) (pairOfComplex w)).hasFDerivAt.comp_hasDerivAt _
      ((hasDerivAt_id w.re).prodMk (hasDerivAt_const w.re w.im))).deriv
  have hy : fderiv ℝ (complexFunction F) w Complex.I = directional ey F (pairOfComplex w) := by
    rw [← centredFirst_eq_fderiv _ _ _ hd,centredFirst_chart_y]
    exact ((hF.differentiable (by simp) (pairOfComplex w)).hasFDerivAt.comp_hasDerivAt _
      ((hasDerivAt_const w.im w.re).prodMk (hasDerivAt_id w.im))).deriv
  have ha : a = a.re • (1 : ℂ)+a.im • Complex.I := by
    simpa only [Complex.real_smul,mul_one] using (Complex.re_add_im a).symm
  rw [ha,map_add,map_smul,map_smul,hx,hy]

theorem mobius_smooth_first_chain (g : SL(2, ℤ)) {F : Plane → ℂ}
    (hF : ContDiff ℝ ∞ F) {p : Plane} (hp : 0 < p.2) :
    directional ex (fun q => F (mobiusChart g q)) p =
      pairRawJetX g (directional ex F) (directional ey F) p ∧
    directional ey (fun q => F (mobiusChart g q)) p =
      pairRawJetY g (directional ex F) (directional ey F) p := by
  let z : UpperHalfPlane := ⟨complexOfPair p,hp⟩
  have hz : pairOfComplex (z : ℂ) = p := rfl
  have hcomp := mobius_pullback_C2 g hF
  have hdc := hcomp.differentiableOn (by norm_num)
  have hpair : ContDiff ℝ ∞ pairOfComplex :=
    Complex.reCLM.contDiff.prodMk Complex.imCLM.contDiff
  have hd : DifferentiableAt ℝ (complexFunction F) (actualMobius g z) :=
    (hF.comp hpair).differentiable (by simp) _
  have hchain (v : ℂ) :
      centredFirst (complexFunction (fun q => F (mobiusChart g q))) z v =
        fderiv ℝ (complexFunction F) (actualMobius g z) (factor g z*v) := by
    rw [centredFirst_local_congr (complexFunction_mobius_pullback_eventually g F z) v]
    exact centredFirst_actualMobius_pullback g z (complexFunction F) hd v
  constructor
  · rw [← sliceDx_eq_fderiv _ hdc hp]
    change sliceDx (fun q => F (mobiusChart g q)) p = _
    rw [← hz,← centredFirst_chart_x,hchain,complexFunction_fderiv_basis hF]
    simp only [mul_one,pair_actualMobius g z.im_pos,hz,pairRawJetX]
    rfl
  · rw [← sliceDy_eq_fderiv _ hdc hp]
    change sliceDy (fun q => F (mobiusChart g q)) p = _
    rw [← hz,← centredFirst_chart_y,hchain,complexFunction_fderiv_basis hF]
    simp only [Complex.mul_I_re,Complex.mul_I_im,pair_actualMobius g z.im_pos,hz,pairRawJetY]
    rfl

theorem mobius_smooth_weak_tests (g : SL(2, ℤ)) {F ψ : Plane → ℂ}
    (hF : ContDiff ℝ ∞ F) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ positiveChart) :
    ((∫ p, star (ψ p)*pairRawJetX g (directional ex F) (directional ey F) p) =
      -(∫ p, star (directional ex ψ p)*F (mobiusChart g p))) ∧
    ((∫ p, star (ψ p)*pairRawJetY g (directional ex F) (directional ey F) p) =
      -(∫ p, star (directional ey ψ p)*F (mobiusChart g p))) := by
  have hcomp := mobius_pullback_C2 g hF
  have hx := plane_arbitrary_compact_first ex hψ hc hs hcomp
  have hy := plane_arbitrary_compact_first ey hψ hc hs hcomp
  have heX : (∫ p, star (ψ p)*directional ex (fun q => F (mobiusChart g q)) p) =
      ∫ p, star (ψ p)*pairRawJetX g (directional ex F) (directional ey F) p := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by
      by_cases hp : 0 < p.2
      · rw [(mobius_smooth_first_chain g hF hp).1]
      · have hz : ψ p = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hp (hs ht))
        simp only [hz,star_zero,zero_mul])
  have heY : (∫ p, star (ψ p)*directional ey (fun q => F (mobiusChart g q)) p) =
      ∫ p, star (ψ p)*pairRawJetY g (directional ex F) (directional ey F) p := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by
      by_cases hp : 0 < p.2
      · rw [(mobius_smooth_first_chain g hF hp).2]
      · have hz : ψ p = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hp (hs ht))
        simp only [hz,star_zero,zero_mul])
  rw [heX] at hx
  rw [heY] at hy
  exact ⟨by simpa only [neg_neg] using congrArg Neg.neg hx.symm,
    by simpa only [neg_neg] using congrArg Neg.neg hy.symm⟩

end
end ImbalancedChen.Part3.MobiusSmoothFirstJetWeakTests20261026b
