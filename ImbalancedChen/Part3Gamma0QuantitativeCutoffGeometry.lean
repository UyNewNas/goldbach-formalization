import ImbalancedChen.Part3QuantitativeChartCutoffFirstDerivatives
import ImbalancedChen.Part3Gamma0FiniteFourierFeatures
import ImbalancedChen.Part3Gamma0PositiveRectangleRellichCharts

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The NEW fixed-profile quantitative cutoff is one on the literal truncated
modular cell and has genuine support inside a positive-margin rectangle
of width 6 and height 2Y+1. All inverse-class charts use this SAME cutoff.
Actual finite disjoint reconstruction therefore bounds the original
quotient-core error by the sum of these localized Fourier-chart errors.
Neither a partition of unity nor a reconstruction bound is assumed.
The earlier qualitative cutoff is unchanged. No spectral or polynomial
energy estimate is asserted here.
-/

namespace ImbalancedChen.Part3.Gamma0QuantitativeCutoffGeometry20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane BigOperators ENNReal
open QuantitativeChartCutoffFirstDerivatives20261026b
open PositiveRectangleSmoothTensorDensity20261025a
open CuspVerticalHeightCommutator20261026b
open Gamma0FiniteChartReconstruction20261026b Gamma0QuotientChartReconstruction20261026b
open Gamma0ChartCoordinateErrorBudget20261026b Gamma0QuotientCellPushforward20261025a
open Gamma0FiniteFourierFeatures20261026b Gamma0PositiveRectangleRellichCharts20261026b
open PositiveRectangleAffineNormalization20261026b PositiveRectangleNativeHyperbolicL220261026b
open Gamma0LocalFourierTailCharts20261026a ModularFundamentalFiniteMeasure20261024z
open MaassWeakOperatorCore20261024zz ActualGamma0MaassDescent20261025a

def quantitativeRectangle (Y : ℝ) (hY : 1 ≤ Y) : Rectangle where
  left := -3
  bottom := 1/8
  width := 6
  height := 2*Y+1
  bottom_pos := by norm_num
  width_pos := by norm_num
  height_pos := by linarith

def quantitativeMargin (Y : ℝ) : ℝ := 1/(16*(2*Y+1))

theorem quantitativeMargin_pos {Y : ℝ} (hY : 1 ≤ Y) : 0 < quantitativeMargin Y := by
  dsimp [quantitativeMargin]
  positivity

theorem quantitativePlanarCutoff_support_outer (Y : ℝ) (hY : 1 ≤ Y) :
    Function.support (quantitativePlanarCutoff Y) ⊆
      Icc (-(5/2 : ℝ)) (5/2) ×ˢ Icc (1/4) (2*Y) := by
  intro p hp
  have hx0 : horizontalBump (1/2) (by norm_num) p.1 ≠ 0 := by
    intro hx
    exact hp (by simp [quantitativePlanarCutoff, quantitativeHorizontal, hx])
  have hy0 : verticalHeightCutoff (1/2) Y p.2 ≠ 0 := by
    intro hy
    exact hp (by simp [quantitativePlanarCutoff, hy])
  have hx := subset_tsupport (horizontalBump (1/2) (by norm_num)) hx0
  rw [(horizontalBump (1/2) (by norm_num)).tsupport_eq, Metric.mem_closedBall,
    Real.dist_eq, sub_zero, abs_le] at hx
  have hy := verticalHeightCutoff_tsupport (by norm_num : (0 : ℝ)<1/2)
    (zero_lt_one.trans_le hY) (subset_tsupport _ hy0)
  constructor
  · simpa [horizontalBump] using hx
  · simpa only [show (1/2 : ℝ)/2=1/4 by norm_num] using hy

theorem quantitativePlanarCutoff_support_region (Y : ℝ) (hY : 1 ≤ Y) :
    Function.support (quantitativePlanarCutoff Y) ⊆
      region (quantitativeRectangle Y hY) (quantitativeMargin Y) := by
  intro p hp
  have hb := quantitativePlanarCutoff_support_outer Y hY hp
  have hh : 0 < 2*Y+1 := by linarith
  have hd : 0 < 16*(2*Y+1) := by positivity
  have hm : quantitativeMargin Y ≤ 1/16 := by
    dsimp [quantitativeMargin]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hmul : quantitativeMargin Y*(2*Y+1)=1/16 := by
    dsimp [quantitativeMargin]
    field_simp [hh.ne']
    <;> ring
  refine ⟨(quantitativeRectangle Y hY).inverse p, ?_,
    (quantitativeRectangle Y hY).affine_inverse p⟩
  constructor
  · change quantitativeMargin Y ≤ (p.1+3)/6 ∧ (p.1+3)/6 ≤ 1-quantitativeMargin Y
    constructor <;> nlinarith [hb.1.1, hb.1.2]
  · change quantitativeMargin Y ≤ (p.2-1/8)/(2*Y+1) ∧
      (p.2-1/8)/(2*Y+1) ≤ 1-quantitativeMargin Y
    constructor
    · apply (le_div_iff₀ hh).mpr
      nlinarith [hb.2.1]
    · apply (div_le_iff₀ hh).mpr
      nlinarith [hb.2.2]

theorem extendUpper_quantitativeUpperCutoff (Y : ℝ) (hY : 1 ≤ Y) :
    extendUpper (quantitativeUpperCutoff Y) = quantitativePlanarCutoff Y := by
  funext p
  by_cases hp : 0 < p.2
  · simp only [extendUpper, dif_pos hp, quantitativeUpperCutoff]
    rfl
  · have hz : quantitativePlanarCutoff Y p=0 := by
      by_contra hn
      have hh := (quantitativePlanarCutoff_support_outer Y hY hn).2.1
      exact hp (by linarith)
    simp only [extendUpper, dif_neg hp, hz]

theorem quantitativeUpperCutoff_C2 (Y : ℝ) (hY : 1 ≤ Y) :
    ContDiffOn ℝ 2 (extendUpper (quantitativeUpperCutoff Y)) positiveChart := by
  rw [extendUpper_quantitativeUpperCutoff Y hY]
  exact ((quantitativePlanarCutoff_smooth Y).of_le (by simp)).contDiffOn

theorem quantitativeUpperCutoff_support_region (Y : ℝ) (hY : 1 ≤ Y) :
    Function.support (extendUpper (quantitativeUpperCutoff Y)) ⊆
      region (quantitativeRectangle Y hY) (quantitativeMargin Y) := by
  rw [extendUpper_quantitativeUpperCutoff Y hY]
  exact quantitativePlanarCutoff_support_region Y hY

def quantitativeCutoffSeed (Y : ℝ) (hY : 1 ≤ Y) :
    RectangleSeed (quantitativeRectangle Y hY) (quantitativeMargin Y) :=
  ⟨quantitativePlanarCutoff Y, (quantitativePlanarCutoff_smooth Y).of_le (by simp),
    quantitativePlanarCutoff_support_region Y hY⟩

theorem quantitativeUpperCutoff_compact (Y : ℝ) (hY : 1 ≤ Y) :
    HasCompactSupport (quantitativeUpperCutoff Y) :=
  nativeFunction_compact (quantitativeMargin_pos hY).le (quantitativeCutoffSeed Y hY)

def quantitativeCutoffCompactSet (Y : ℝ) : Set UpperHalfPlane := tsupport (quantitativeUpperCutoff Y)

theorem quantitativeCutoffCompactSet_isCompact (Y : ℝ) (hY : 1 ≤ Y) :
    IsCompact (quantitativeCutoffCompactSet Y) := quantitativeUpperCutoff_compact Y hY

theorem quantitativeUpperCutoff_continuous (Y : ℝ) : Continuous (quantitativeUpperCutoff Y) :=
  (quantitativePlanarCutoff_smooth Y).continuous.comp
    (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im)

theorem quantitativeUpperCutoff_norm_le_one (Y : ℝ) (z : UpperHalfPlane) :
    ‖quantitativeUpperCutoff Y z‖ ≤ 1 := quantitativePlanarCutoff_norm_le_one Y (z.re,z.im)

theorem quantitativeUpperCutoff_eq_one_on_truncated_cell (Y : ℝ) (hY : 1 ≤ Y)
    {z : UpperHalfPlane} (hz : z ∈ truncatedModularCell Y) :
    quantitativeUpperCutoff Y z=1 := by
  have hx := abs_le.mp (modularFD_real_bound hz.1)
  have hy := (modularFD_half_lt_im hz.1).le
  rw [quantitativeUpperCutoff, quantitativePlanarCutoff, quantitativeHorizontal,
    horizontalBump_eq_one (1/2) (by norm_num) hx,
    verticalHeightCutoff_eq_one (by norm_num : (0 : ℝ)<1/2) (zero_lt_one.trans_le hY) hy hz.2]
  norm_num

def quantitativeClassSeed (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y)
    (f : SmoothFunction) (q : Gamma0FiniteMeasureCarrier20261024z.gamma0Classes N) :
    RectangleSeed (quantitativeRectangle Y hY) (quantitativeMargin Y) :=
  classSeed N (quantitativeRectangle Y hY) (quantitativeMargin_pos hY).le
    (quantitativeUpperCutoff Y) (quantitativeUpperCutoff_C2 Y hY)
    (quantitativeUpperCutoff_support_region Y hY) f q

def quantitativeFourierFeatures (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y) (M : ℕ) :
    Gamma0ActualSmoothQuotientCore20261025a.QuotientL2 N →L[ℂ] FeatureSpace N M :=
  actualFourierFeatures N (quantitativeRectangle Y hY) (quantitativeCutoffCompactSet_isCompact Y hY)
    (quantitativeUpperCutoff Y) (quantitativeUpperCutoff_continuous Y) 1
    (quantitativeUpperCutoff_norm_le_one Y) M

/-- Literal quotient-core reconstruction, paid once on each disjoint cell,
now with the NEW quantitatively controlled chart cutoff. -/
theorem quotient_core_error_le_quantitative_chart_errors (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) (F : Gamma0OrbitSpace N → ℂ) (hF : Measurable F)
    (v : ChartIndex N → UpperHalfPlane → ℂ) (hv : ∀ i, Measurable (v i)) :
    (∫⁻ q in quotientCore N Y, ENNReal.ofReal (‖F q-quotientReconstruct N Y v q‖^2)
      ∂carrierPushforward N) ≤
      ∑ i : ChartIndex N, ∫⁻ z in truncatedModularCell Y,
        ENNReal.ofReal (‖localizedClassChart N (F ∘ orbitProjection N)
          (quantitativeUpperCutoff Y) (chartClass N i) z-v i z‖^2) := by
  apply (quotient_core_error_le_actual_chart_errors N Y F hF v hv).trans_eq
  apply Finset.sum_congr rfl
  intro i _
  apply setLIntegral_congr_fun (truncatedModularCell_measurable Y)
  intro z hz
  rw [localizedClassChart, quantitativeUpperCutoff_eq_one_on_truncated_cell Y hY hz, one_mul]
  rfl

end
end ImbalancedChen.Part3.Gamma0QuantitativeCutoffGeometry20261026b
