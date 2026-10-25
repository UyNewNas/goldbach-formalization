import ImbalancedChen.Part3ActualModularSmoothCutoffL2Tail
import ImbalancedChen.Part3ActualPoincareDirichletTrace

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Actual local derivative structure of the constructed smooth cusp cutoff.
At every point its germ is either the constant one or one actual Mobius
pullback of the native height cutoff. This is proved from actual high-cusp
disjointness and the established high-seed local finiteness. Thus native
hyperbolic gradient energy is controlled by the single-cusp derivative
constant, without summing unproved cross terms or assuming a global
gradient estimate. No form-core or closed-form membership is asserted.
-/

namespace ImbalancedChen.Part3.ActualModularCutoffGradient20261025a

noncomputable section
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane ENNReal
open Gamma0ParabolicCosetRows20261025a Gamma0ParabolicEffectiveDecomposition20261025a
open Gamma0ActualHighCuspTail20261025a Gamma0ActualParabolicUnfolding20261025a
open GammaInfinityTranslationStrip20261025a ActualCuspStripCutoff20261025a
open ActualParabolicHighSeedLocalFinite20261025a ActualModularSmoothCuspCutoff20261025a
open Gamma0CompactTensorPoincareC2Core20261025a Gamma0CompactGreenProductL120261025a
open ActualGamma0MaassDescent20261025a ActualMobiusDirichletCovariance20261025a
open ActualPoincareDirichletTrace20261025a

theorem parabolic_height_continuous (N : ℕ) (q : GammaInfinityCosets N) :
    Continuous (fun z : UpperHalfPlane => (parabolicRepresentative N q • z).im) := by
  apply UpperHalfPlane.continuous_im.comp
  change Continuous (fun z : UpperHalfPlane =>
    (SpecialLinearGroup.mapGL ℝ (parabolicRepresentative N q : SL(2, ℤ))) • z)
  exact continuous_const_smul _

/-- Genuine germ dichotomy. The threshold one is below the profile's
threshold Y, providing the room needed at points of the compact part. -/
theorem highTrace_germ_alternatives (N : ℕ) (Y : ℝ) (hY : 1 < Y)
    (z : UpperHalfPlane) :
    (highTrace N Y =ᶠ[𝓝 z] (fun _ => 0)) ∨
      ∃ q : GammaInfinityCosets N,
        highTrace N Y =ᶠ[𝓝 z]
          (fun w => highProfile Y (parabolicRepresentative N q • w).im) := by
  have hYpos : 0 < Y := lt_trans (by norm_num) hY
  by_cases hex : ∃ q : GammaInfinityCosets N, 1 < (parabolicRepresentative N q • z).im
  · obtain ⟨q, hq⟩ := hex
    right
    refine ⟨q, ?_⟩
    filter_upwards [continuousAt_const.eventually_lt
      (parabolic_height_continuous N q).continuousAt hq] with w hw
    apply tsum_eq_single q
    intro r hr
    by_contra hn
    have hh := highProfile_nonzero_height Y hYpos (parabolicRepresentative N r • w) hn
    have heq := two_high_images_same_coset N (parabolicRepresentative N r)
      (parabolicRepresentative N q) w (hY.trans hh) hw
    exact hr (by simpa only [parabolicRepresentative_class] using heq)
  · left
    obtain ⟨U, hU, S, hS⟩ := highTrace_locally_eq_finsetSum N Y hYpos z
    have hnear : ∀ᶠ w in 𝓝 z, ∀ q ∈ S,
        (parabolicRepresentative N q • w).im < Y := by
      apply (Filter.eventually_all_finset S).mpr
      intro q _
      have hq : (parabolicRepresentative N q • z).im ≤ 1 :=
        le_of_not_gt (fun h => hex ⟨q, h⟩)
      exact (parabolic_height_continuous N q).continuousAt.eventually_lt
        continuousAt_const (hq.trans_lt hY)
    filter_upwards [Filter.eventually_of_mem hU hS, hnear] with w hw hnearw
    rw [hw]
    apply Finset.sum_eq_zero
    intro q hq
    exact highProfile_eq_zero Y hYpos _ (parabolicRepresentative N q • w).im_pos.le
      (hnearw q hq).le

theorem globalCutoff_germ_alternatives (Y : ℝ) (hY : 1 < Y) (z : UpperHalfPlane) :
    (globalCutoff Y =ᶠ[𝓝 z] (fun _ => 1)) ∨
      ∃ q : GammaInfinityCosets 1,
        globalCutoff Y =ᶠ[𝓝 z]
          (fun w => heightCutoff Y (parabolicRepresentative 1 q • w).im) := by
  rcases highTrace_germ_alternatives 1 Y hY z with hz | ⟨q, hq⟩
  · left
    filter_upwards [hz] with w hw
    simp only [globalCutoff, hw, sub_zero]
  · right
    refine ⟨q, ?_⟩
    filter_upwards [hq] with w hw
    dsimp [globalCutoff]
    rw [hw]
    unfold highProfile
    ring

def complexGlobalChart (Y : ℝ) (p : ℝ × ℝ) : ℂ := (globalCutoff Y (chartLift p) : ℂ)
def heightChart (Y : ℝ) (p : ℝ × ℝ) : ℂ := (heightCutoff Y p.2 : ℂ)

theorem heightChart_cinfty (Y : ℝ) : ContDiff ℝ ∞ (heightChart Y) :=
  Complex.ofRealCLM.contDiff.comp ((heightCutoff_cinfty Y).comp contDiff_snd)

theorem complexGlobalChart_cinfty (Y : ℝ) (hY : 0 < Y) :
    ContDiffOn ℝ ∞ (complexGlobalChart Y) positiveChart :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn (globalCutoff_chart_cinfty Y hY)

/-- Native coordinate-gradient density, with exactly the same literal
slice derivatives as the actual quotient Dirichlet form. -/
def cutoffEnergyH (Y : ℝ) (z : UpperHalfPlane) : ℝ :=
  (hyperbolicChartDirichlet (complexGlobalChart Y) (complexGlobalChart Y) (z.re, z.im)).re

theorem cutoffEnergyH_nonneg (Y : ℝ) (z : UpperHalfPlane) : 0 ≤ cutoffEnergyH Y z :=
  hyperbolicChartDirichlet_self_re_nonneg _ _

theorem complex_height_deriv (Y y : ℝ) :
    deriv (fun t : ℝ => (heightCutoff Y t : ℂ)) y = (deriv (heightCutoff Y) y : ℂ) :=
  ((heightCutoff_cinfty Y).differentiable (by simp) y).hasDerivAt.ofReal_comp.deriv

theorem heightChart_energy (Y : ℝ) (p : ℝ × ℝ) :
    (hyperbolicChartDirichlet (heightChart Y) (heightChart Y) p).re =
      p.2^2 * (deriv (heightCutoff Y) p.2)^2 := by
  rw [hyperbolicChartDirichlet, chartDirichlet_self_eq]
  simp [sliceDx, sliceDy, heightChart, complex_height_deriv, Complex.normSq_ofReal]

/-- The true global gradient is locally the gradient of one transformed
height profile, or zero. Cross terms have been eliminated geometrically. -/
theorem cutoffEnergyH_zero_or_height (Y : ℝ) (hY : 1 < Y) (z : UpperHalfPlane) :
    cutoffEnergyH Y z = 0 ∨ ∃ q : GammaInfinityCosets 1,
      cutoffEnergyH Y z = (parabolicRepresentative 1 q • z).im^2 *
        (deriv (heightCutoff Y) (parabolicRepresentative 1 q • z).im)^2 := by
  let p : ℝ × ℝ := (z.re, z.im)
  have hp : 0 < p.2 := z.im_pos
  rcases globalCutoff_germ_alternatives Y hY z with hzero | ⟨q, hq⟩
  · left
    have hg : complexGlobalChart Y =ᶠ[𝓝 p] (fun _ => (1 : ℂ)) := by
      have hc := (chartLift_continuousAt_positive hp).eventually
        (by simpa only [p, chartLift_pair] using hzero)
      filter_upwards [hc] with r hr
      simp only [complexGlobalChart, hr, Complex.ofReal_one]
    rw [cutoffEnergyH,
      hyperbolicChartDirichlet_congr_of_eventuallyEq hg hg]
    simp [hyperbolicChartDirichlet, chartDirichlet, sliceDx, sliceDy]
  · right
    let g : SL(2, ℤ) := parabolicRepresentative 1 q
    have hg : complexGlobalChart Y =ᶠ[𝓝 p] (fun r => heightChart Y (mobiusChart g r)) := by
      have hc := (chartLift_continuousAt_positive hp).eventually
        (by simpa only [p, chartLift_pair] using hq)
      filter_upwards [hc, positiveChart_isOpen.mem_nhds hp] with r hr hrpos
      change (globalCutoff Y (chartLift r) : ℂ) = _
      rw [hr, heightChart, mobiusChart_eq_actual g hrpos]
    refine ⟨q, ?_⟩
    rw [cutoffEnergyH, hyperbolicChartDirichlet_congr_of_eventuallyEq hg hg,
      hyperbolicChartDirichlet_comp_mobiusChart g _ _ p hp
        ((heightChart_cinfty Y).of_le (by simp)).contDiffAt
        ((heightChart_cinfty Y).of_le (by simp)).contDiffAt,
      heightChart_energy, mobiusChart_eq_actual g hp]
    simp only [p, chartLift_pair, g]

/-- The native scalar energy bound is global in the horizontal coordinate;
an actual integer translation supplies the width-one strip witness. -/
theorem height_energy_le_high_indicator (Y : ℝ) (hY : 0 < Y) (z : UpperHalfPlane) :
    ENNReal.ofReal (z.im^2 * (deriv (heightCutoff Y) z.im)^2) ≤
      ENNReal.ofReal cutoffEnergyConstant * highSeed Y z := by
  obtain ⟨k, hk, _⟩ := unique_translate_mem_strip z
  have hb := cutoff_vertical_energy_pointwise (w := 1) hY (translate k z) hk
  simp only [translate_im] at hb
  by_cases hy : Y ≤ z.im
  · have hm : translate k z ∈ highWidthStrip 1 Y := ⟨hk, by simpa only [translate_im] using hy⟩
    rw [Set.indicator_of_mem hm] at hb
    have hs : highSeed Y z = 1 := Set.indicator_of_mem hy _
    rw [hs, mul_one]
    exact ENNReal.ofReal_le_ofReal hb
  · have hm : translate k z ∉ highWidthStrip 1 Y := by
      intro hh
      exact hy (by simpa only [translate_im] using hh.2)
    rw [Set.indicator_of_notMem hm] at hb
    have hs : highSeed Y z = 0 := Set.indicator_of_notMem hy _
    rw [hs, mul_zero]
    exact (ENNReal.ofReal_le_ofReal hb).trans_eq (by simp)

/-- Pointwise ACTUAL hyperbolic gradient bound for the global cutoff.
Its right side is the genuine parabolic high-cusp trace, already unfolded
against the canonical quotient measure by the existing primitive. -/
theorem cutoffEnergyH_le_high_trace (Y : ℝ) (hY : 1 < Y) (z : UpperHalfPlane) :
    ENNReal.ofReal (cutoffEnergyH Y z) ≤
      ENNReal.ofReal cutoffEnergyConstant * parabolicTraceNN 1 (highSeed Y) z := by
  rcases cutoffEnergyH_zero_or_height Y hY z with hz | ⟨q, hq⟩
  · rw [hz]
    simp
  · rw [hq]
    exact (height_energy_le_high_indicator Y (lt_trans (by norm_num) hY) _).trans
      (mul_le_mul_left' (ENNReal.le_tsum q) _)

theorem complexGlobalChart_comp_mobius_germ (Y : ℝ) (g : SL(2, ℤ))
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    (fun r => complexGlobalChart Y (mobiusChart g r)) =ᶠ[𝓝 p] complexGlobalChart Y := by
  filter_upwards [positiveChart_isOpen.mem_nhds hp] with r hr
  simp only [complexGlobalChart, mobiusChart_eq_actual g hr, chartLift_pair,
    globalCutoff_sl2_invariant]

/-- Invariance of the ACTUAL derivative density, proved by Mobius
covariance and the constructed cutoff's genuine invariance. -/
theorem cutoffEnergyH_sl2_invariant (Y : ℝ) (hY : 0 < Y)
    (g : SL(2, ℤ)) (z : UpperHalfPlane) : cutoffEnergyH Y (g • z) = cutoffEnergyH Y z := by
  let p : ℝ × ℝ := (z.re, z.im)
  have hp : 0 < p.2 := z.im_pos
  have him : 0 < (mobiusChart g p).2 := by
    rw [mobiusChart_eq_actual g hp]
    simp only [p, chartLift_pair]
    exact (g • z).im_pos
  have hG : ContDiffOn ℝ 1 (complexGlobalChart Y) positiveChart :=
    (complexGlobalChart_cinfty Y hY).of_le (by simp)
  have hGa : ContDiffAt ℝ 1 (complexGlobalChart Y) (mobiusChart g p) :=
    (hG _ him).contDiffAt (positiveChart_isOpen.mem_nhds him)
  have hc := hyperbolicChartDirichlet_comp_mobiusChart g
    (complexGlobalChart Y) (complexGlobalChart Y) p hp hGa hGa
  rw [hyperbolicChartDirichlet_congr_of_eventuallyEq
    (complexGlobalChart_comp_mobius_germ Y g p hp)
    (complexGlobalChart_comp_mobius_germ Y g p hp)] at hc
  rw [mobiusChart_eq_actual g hp] at hc
  simp only [p, chartLift_pair] at hc
  exact (congrArg Complex.re hc).symm

theorem cutoffEnergyH_continuous (Y : ℝ) (hY : 0 < Y) : Continuous (cutoffEnergyH Y) := by
  have hG : ContDiffOn ℝ 1 (complexGlobalChart Y) positiveChart :=
    (complexGlobalChart_cinfty Y hY).of_le (by simp)
  have hpair : Continuous (fun z : UpperHalfPlane => (z.re, z.im)) :=
    UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im
  have hDx : Continuous (fun z : UpperHalfPlane =>
      sliceDx (complexGlobalChart Y) (z.re, z.im)) :=
    (sliceDx_continuousOn_of_C1 _ hG).comp_continuous hpair (fun z => z.im_pos)
  have hDy : Continuous (fun z : UpperHalfPlane =>
      sliceDy (complexGlobalChart Y) (z.re, z.im)) :=
    (sliceDy_continuousOn_of_C1 _ hG).comp_continuous hpair (fun z => z.im_pos)
  have heq : cutoffEnergyH Y = fun z : UpperHalfPlane =>
      z.im^2 * (‖sliceDx (complexGlobalChart Y) (z.re, z.im)‖^2 +
        ‖sliceDy (complexGlobalChart Y) (z.re, z.im)‖^2) := by
    funext z
    rw [cutoffEnergyH, hyperbolicChartDirichlet, chartDirichlet_self_eq]
    simp [Complex.normSq_eq_norm_sq]
  rw [heq]
  exact (UpperHalfPlane.continuous_im.pow 2).mul ((hDx.norm.pow 2).add (hDy.norm.pow 2))

end
end ImbalancedChen.Part3.ActualModularCutoffGradient20261025a
