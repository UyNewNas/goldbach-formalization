import ImbalancedChen.Part3ActualModularCutoffEnergyBudget
import ImbalancedChen.Part3ActualCuspStripCutoffGraph

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The existing native upperMaass of the constructed actual modular cutoff
is locally zero or ONE actual transformed height-cutoff Maass output.
This follows from the genuine cutoff germ and native Mobius second-chain
covariance. The actual second derivative bound supplies a high-cusp
majorant; genuine quotient descent and finite-cover integration give its
squared L2 norm <= C_graph * actual index/Y. No graph-domain membership,
finite-tensor core membership, global cutoff, or Delta estimate is input.
-/

namespace ImbalancedChen.Part3.ActualModularCutoffMaassBudget20261025a

noncomputable section
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane ENNReal
open MaassWeakOperatorCore20261024zz Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0CompactGreenProductL120261025a ActualPoincareMaassLocalFinite20261025a
open ActualMobiusMaassEquivariance20261025a ActualGamma0MaassDescent20261025a
open Gamma0ParabolicCosetRows20261025a Gamma0ParabolicEffectiveDecomposition20261025a
open GammaInfinityTranslationStrip20261025a ActualCuspStripCutoff20261025a
open ActualCuspStripCutoffGraph20261025a Gamma0ActualHighCuspTail20261025a
open Gamma0ActualParabolicUnfolding20261025a ActualParabolicHighSeedLocalFinite20261025a
open ActualModularSmoothCuspCutoff20261025a ActualModularSmoothCutoffL2Tail20261025a
open ActualModularCutoffGradient20261025a Gamma0QuotientCellPushforward20261025a
open Gamma0CarrierMeasurableInverse20261025a Gamma0QuotientConullTransport20261025a
open Gamma0ModularFiniteCoverMeasure20261025a

def complexGlobalH (Y : ℝ) (z : UpperHalfPlane) : ℂ := (globalCutoff Y z : ℂ)

theorem extendGlobal_germ (Y : ℝ) {p : ℝ × ℝ} (hp : 0 < p.2) :
    extendUpper (complexGlobalH Y) =ᶠ[𝓝 p] complexGlobalChart Y := by
  filter_upwards [positiveChart_isOpen.mem_nhds hp] with r hr
  rw [extendUpper_chartLift _ r hr]
  rfl

theorem extendGlobal_C2 (Y : ℝ) (hY : 0 < Y) :
    ContDiffOn ℝ 2 (extendUpper (complexGlobalH Y)) positiveChart := by
  have hG : ContDiffOn ℝ 2 (complexGlobalChart Y) positiveChart :=
    (complexGlobalChart_cinfty Y hY).of_le (by simp)
  apply hG.congr
  intro p hp
  exact (extendUpper_chartLift (complexGlobalH Y) p hp).symm

theorem complexGlobalH_invariant (N : ℕ) (Y : ℝ)
    (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane) :
    complexGlobalH Y (g • z) = complexGlobalH Y z :=
  congrArg (fun a : ℝ => (a : ℂ)) (globalCutoff_sl2_invariant Y (g : SL(2, ℤ)) z)

theorem chartMaass_heightChart (Y : ℝ) (z : UpperHalfPlane) :
    chartMaass (heightChart Y) (z.re, z.im) = upperMaass (complexCutoffH Y) z := by
  change chartMaass (heightChart Y) (z.re, z.im) =
    chartMaass (extendUpper (complexCutoffH Y)) (z.re, z.im)
  exact (chartMaass_eq_of_eventuallyEq (extend_complexCutoff_germ Y z.im_pos)).symm

/-- Actual native Delta has the same proved single-germ structure as
the gradient. This is an equality of upperMaass outputs. -/
theorem upperMaass_global_zero_or_height (Y : ℝ) (hY : 1 < Y) (z : UpperHalfPlane) :
    upperMaass (complexGlobalH Y) z = 0 ∨
      ∃ q : GammaInfinityCosets 1,
        upperMaass (complexGlobalH Y) z =
          upperMaass (complexCutoffH Y) (parabolicRepresentative 1 q • z) := by
  let p : ℝ × ℝ := (z.re, z.im)
  have hp : 0 < p.2 := z.im_pos
  rcases globalCutoff_germ_alternatives Y hY z with hzero | ⟨q, hq⟩
  · left
    have hg : complexGlobalChart Y =ᶠ[𝓝 p] (fun _ => (1 : ℂ)) := by
      have hc := (chartLift_continuousAt_positive hp).eventually
        (by simpa only [p, chartLift_pair] using hzero)
      filter_upwards [hc] with r hr
      simp only [complexGlobalChart, hr, Complex.ofReal_one]
    change chartMaass (extendUpper (complexGlobalH Y)) p = 0
    rw [chartMaass_eq_of_eventuallyEq (extendGlobal_germ Y hp),
      chartMaass_eq_of_eventuallyEq hg]
    simp [chartMaass]
  · right
    let g : SL(2, ℤ) := parabolicRepresentative 1 q
    have hg : complexGlobalChart Y =ᶠ[𝓝 p] (fun r => heightChart Y (mobiusChart g r)) := by
      have hc := (chartLift_continuousAt_positive hp).eventually
        (by simpa only [p, chartLift_pair] using hq)
      filter_upwards [hc, positiveChart_isOpen.mem_nhds hp] with r hr hrpos
      change (globalCutoff Y (chartLift r) : ℂ) = _
      rw [hr, heightChart, mobiusChart_eq_actual g hrpos]
    refine ⟨q, ?_⟩
    change chartMaass (extendUpper (complexGlobalH Y)) p = _
    rw [chartMaass_eq_of_eventuallyEq (extendGlobal_germ Y hp),
      chartMaass_eq_of_eventuallyEq hg,
      chartMaass_comp_mobiusChart g (heightChart Y) p hp
        ((heightChart_cinfty Y).of_le (by simp)).contDiffAt,
      mobiusChart_eq_actual g hp]
    simp only [p, chartLift_pair, g]
    exact chartMaass_heightChart Y _

theorem heightMaass_square_le_high_indicator (Y : ℝ) (hY : 0 < Y) (z : UpperHalfPlane) :
    ENNReal.ofReal (‖upperMaass (complexCutoffH Y) z‖^2) ≤
      ENNReal.ofReal cutoffGraphConstant * highSeed Y z := by
  obtain ⟨k, hk, _⟩ := unique_translate_mem_strip z
  have hb := upperMaass_complexCutoff_norm_sq_pointwise (w := 1) hY (translate k z) hk
  have htranslate : upperMaass (complexCutoffH Y) (translate k z) =
      upperMaass (complexCutoffH Y) z := by
    simp only [upperMaass_complexCutoff, translate_im]
  rw [htranslate] at hb
  by_cases hy : Y ≤ z.im
  · have hm : translate k z ∈ highWidthStrip 1 Y :=
      ⟨hk, by simpa only [translate_im] using hy⟩
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

/-- The native Maass graph density is dominated before integration by
the TRUE high-cusp parabolic trace; no pointwise Delta premise is used. -/
theorem upperMaass_global_square_le_high_trace (Y : ℝ) (hY : 1 < Y) (z : UpperHalfPlane) :
    ENNReal.ofReal (‖upperMaass (complexGlobalH Y) z‖^2) ≤
      ENNReal.ofReal cutoffGraphConstant * parabolicTraceNN 1 (highSeed Y) z := by
  rcases upperMaass_global_zero_or_height Y hY z with hz | ⟨q, hq⟩
  · rw [hz]
    simp
  · rw [hq]
    exact (heightMaass_square_le_high_indicator Y (lt_trans (by norm_num) hY) _).trans
      (mul_le_mul_left' (ENNReal.le_tsum q) _)

theorem upperMaass_global_continuous (Y : ℝ) (hY : 0 < Y) :
    Continuous (upperMaass (complexGlobalH Y)) := by
  have hc := chartMaass_continuousOn _ (extendGlobal_C2 Y hY)
  exact hc.comp_continuous
    (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im) (fun z => z.im_pos)

/-- Use the EXISTING quotientMaass descent, specialized to the actually
constructed cutoff and its proved chart smoothness/invariance. -/
def quotientCutoffMaass (N : ℕ) (Y : ℝ) (hY : 0 < Y) : Gamma0OrbitSpace N → ℂ :=
  quotientMaass N (complexGlobalH Y) (extendGlobal_C2 Y hY) (complexGlobalH_invariant N Y)

@[simp] theorem quotientCutoffMaass_projection (N : ℕ) (Y : ℝ) (hY : 0 < Y)
    (z : UpperHalfPlane) :
    quotientCutoffMaass N Y hY (orbitProjection N z) = upperMaass (complexGlobalH Y) z := rfl

theorem quotientCutoffMaass_measurable (N : ℕ) (Y : ℝ) (hY : 0 < Y) :
    Measurable (quotientCutoffMaass N Y hY) :=
  measurable_from_quotient.mpr (upperMaass_global_continuous Y hY).measurable

theorem quotientCutoffMaass_eq_level_one (N : ℕ) (Y : ℝ) (hY : 0 < Y) :
    quotientCutoffMaass N Y hY = quotientCutoffMaass 1 Y hY ∘ forgetLevel N := by
  funext q
  refine Quotient.inductionOn q (fun _ => rfl)

theorem quotientCutoffMaass_square_bound_ae (Y : ℝ) (hY : 1 < Y) :
    ∀ᵐ q ∂carrierPushforward 1,
      ENNReal.ofReal (‖quotientCutoffMaass 1 Y (lt_trans (by norm_num) hY) q‖^2) ≤
        ENNReal.ofReal cutoffGraphConstant * quotientHighIndicator 1 Y q := by
  filter_upwards [reducedProjection_range_ae 1] with q hq
  obtain ⟨z, rfl⟩ := hq
  change ENNReal.ofReal (‖upperMaass (complexGlobalH Y) (z : UpperHalfPlane)‖^2) ≤ _
  rw [quotientHighIndicator, parabolicNonnegativePoincare_projection]
  exact upperMaass_global_square_le_high_trace Y hY z

theorem quotientCutoffMaass_level_one_L2_bound (Y : ℝ) (hY : 1 < Y) :
    (∫⁻ q, ENNReal.ofReal (‖quotientCutoffMaass 1 Y (lt_trans (by norm_num) hY) q‖^2)
      ∂carrierPushforward 1) ≤ ENNReal.ofReal cutoffGraphConstant * ENNReal.ofReal (1 / Y) := by
  calc
    _ ≤ ∫⁻ q, ENNReal.ofReal cutoffGraphConstant * quotientHighIndicator 1 Y q
        ∂carrierPushforward 1 := lintegral_mono_ae (quotientCutoffMaass_square_bound_ae Y hY)
    _ = _ := by
      rw [lintegral_const_mul _ (quotientHighIndicator_measurable 1 Y),
        quotientHighIndicator_eq_indicator 1 Y hY,
        lintegral_indicator (quotientHighTail_measurable 1 Y)]
      simp only [lintegral_const, Measure.restrict_apply_univ, one_mul]
      rw [quotientHighTail_volume 1 Y hY]

/-- Actual TOTAL native Maass squared L2 budget, with the exact finite
cover index and the native fixed second-derivative constant. -/
theorem quotientCutoffMaass_L2_bound (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    (∫⁻ q, ENNReal.ofReal (‖quotientCutoffMaass N Y (lt_trans (by norm_num) hY) q‖^2)
      ∂carrierPushforward N) ≤ ENNReal.ofReal cutoffGraphConstant *
        ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) * ENNReal.ofReal (1 / Y) := by
  let F := fun q => ENNReal.ofReal (‖quotientCutoffMaass 1 Y (lt_trans (by norm_num) hY) q‖^2)
  have hF : Measurable F :=
    ((quotientCutoffMaass_measurable 1 Y (lt_trans (by norm_num) hY)).norm.pow_const 2).ennreal_ofReal
  rw [quotientCutoffMaass_eq_level_one]
  change (∫⁻ q, F (forgetLevel N q) ∂carrierPushforward N) ≤ _
  rw [← lintegral_map hF (forgetLevel_measurable N), forgetLevel_map_carrier,
    lintegral_smul_measure]
  calc
    _ ≤ ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) *
        (ENNReal.ofReal cutoffGraphConstant * ENNReal.ofReal (1 / Y)) :=
      mul_le_mul_left' (quotientCutoffMaass_level_one_L2_bound Y hY) _
    _ = _ := by ac_rfl

/-- Affine graph approximation budget for the actual constant/cutoff
pair. This is a representative-level estimate, not graph-domain membership. -/
theorem quotientCutoff_affine_graph_budget (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    (∫⁻ q, ENNReal.ofReal ((1 - quotientCutoff N Y q)^2) ∂carrierPushforward N) +
      (∫⁻ q, ENNReal.ofReal (‖quotientCutoffMaass N Y (lt_trans (by norm_num) hY) q‖^2)
        ∂carrierPushforward N) ≤
      (1 + ENNReal.ofReal cutoffGraphConstant) *
        ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) * ENNReal.ofReal (1 / Y) := by
  calc
    _ ≤ ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) * ENNReal.ofReal (1 / Y) +
        ENNReal.ofReal cutoffGraphConstant *
          ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) * ENNReal.ofReal (1 / Y) :=
      add_le_add (quotientCutoff_L2_error_le N Y hY) (quotientCutoffMaass_L2_bound N Y hY)
    _ = _ := by rw [add_mul, one_mul, add_mul]

end
end ImbalancedChen.Part3.ActualModularCutoffMaassBudget20261025a
