import ImbalancedChen.Part3Gamma0ChartCoordinateErrorBudget
import ImbalancedChen.Part3PositiveRectangleAffineNormalization
import ImbalancedChen.Part3PositiveCompactTensorLpApproximation
import ImbalancedChen.Part3Gamma0LocalFourierTailCharts

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An explicit legal compact smooth chart cutoff equals one on the actual
truncated modular fundamental cell. Its zero extension has a proved common
positive rectangle margin in the actual affine Rellich rectangle model.
It therefore fixes EVERY actual finite inverse-class chart on that cell.
The resulting finite quotient reconstruction is exact on its genuine core.

This constructs the cutoff rather than assuming its existence or plateau.
Uniform localized derivative-energy bounds and all-cusp true zero-mode
tail control remain separate obligations; no global embedding is asserted.
-/

namespace ImbalancedChen.Part3.Gamma0TruncatedChartCutoff20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane BigOperators
open PositiveRectangleAffineNormalization20261026b
open PositiveRectangleSmoothTensorDensity20261025a
open PositiveCompactTensorLpApproximation20261025a
open ModularFundamentalFiniteMeasure20261024z
open Gamma0FiniteChartReconstruction20261026b
open Gamma0QuotientChartReconstruction20261026b
open Gamma0QuotientCellPushforward20261025a
open Gamma0LocalFourierTailCharts20261026a
open MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareC2Core20261025a

def chartCutoffTensor (Y : ℝ) (hY : 1 ≤ Y) : SmoothPositiveTensor :=
  cutoffTensor (1/2) (1/2) Y (by norm_num) (by norm_num) (by linarith)

def planarCutoff (Y : ℝ) (hY : 1 ≤ Y) : Plane → ℂ :=
  planeTensor (chartCutoffTensor Y hY)

def upperCutoff (Y : ℝ) (hY : 1 ≤ Y) (z : UpperHalfPlane) : ℂ :=
  planarCutoff Y hY (z.re, z.im)

def cutoffRectangle (Y : ℝ) (hY : 1 ≤ Y) : Rectangle where
  left := -3
  bottom := 1/8
  width := 6
  height := Y+1
  bottom_pos := by norm_num
  width_pos := by norm_num
  height_pos := by linarith

def cutoffMargin (Y : ℝ) : ℝ := 1 / (16 * (Y+1))

theorem cutoffMargin_pos {Y : ℝ} (hY : 1 ≤ Y) : 0 < cutoffMargin Y := by
  dsimp [cutoffMargin]
  positivity

theorem planarCutoff_smooth (Y : ℝ) (hY : 1 ≤ Y) :
    ContDiff ℝ 2 (planarCutoff Y hY) := by
  let T := chartCutoffTensor Y hY
  have hs : ContDiff ℝ ∞ (fun p : Plane => T.horizontal p.1 * T.vertical p.2) :=
    (T.horizontal_smooth.comp contDiff_fst).mul (T.vertical_smooth.comp contDiff_snd)
  exact (Complex.ofRealCLM.contDiff.comp hs).of_le (by simp)

theorem planarCutoff_support_outer (Y : ℝ) (hY : 1 ≤ Y) :
    Function.support (planarCutoff Y hY) ⊆
      (Icc (-(5/2 : ℝ)) (5/2) ×ˢ Icc (1/4) (Y+1/4)) := by
  intro p hp
  have h := cutoff_nonzero_mem_outer (1/2) (1/2) Y
    (by norm_num) (by norm_num) (by linarith) hp
  simpa only [outerRectangle, PositiveRectangleSmoothTensorDensity20261025a.rectangle,
    show (1/2 : ℝ)+2 = 5/2 by norm_num,
    show (1/2 : ℝ)/2 = 1/4 by norm_num] using h

theorem extendUpper_upperCutoff (Y : ℝ) (hY : 1 ≤ Y) :
    extendUpper (upperCutoff Y hY) = planarCutoff Y hY := by
  funext p
  by_cases hp : 0 < p.2
  · simp only [extendUpper, dif_pos hp, upperCutoff]
    rfl
  · have hz : planarCutoff Y hY p = 0 := by
      by_contra hn
      have h := (planarCutoff_support_outer Y hY hn).2.1
      exact hp (by linarith)
    simp only [extendUpper, dif_neg hp, hz]

/-- The entire literal cutoff support has one proved positive margin in
the supplier's actual affine rectangle. The margin may depend on Y. -/
theorem planarCutoff_support_region (Y : ℝ) (hY : 1 ≤ Y) :
    Function.support (planarCutoff Y hY) ⊆
      region (cutoffRectangle Y hY) (cutoffMargin Y) := by
  intro p hp
  have hb := planarCutoff_support_outer Y hY hp
  have hheight : 0 < Y+1 := by linarith
  have hden : 0 < 16*(Y+1) := by positivity
  have hsmall : cutoffMargin Y ≤ 1/16 := by
    dsimp [cutoffMargin]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hproduct : cutoffMargin Y * (Y+1) = 1/16 := by
    dsimp [cutoffMargin]
    field_simp [hheight.ne']
    <;> ring
  refine ⟨(cutoffRectangle Y hY).inverse p, ?_,
    (cutoffRectangle Y hY).affine_inverse p⟩
  constructor
  · change cutoffMargin Y ≤ (p.1+3)/6 ∧ (p.1+3)/6 ≤ 1-cutoffMargin Y
    constructor <;> nlinarith [hb.1.1, hb.1.2]
  · change cutoffMargin Y ≤ (p.2-1/8)/(Y+1) ∧
      (p.2-1/8)/(Y+1) ≤ 1-cutoffMargin Y
    constructor
    · apply (le_div_iff₀ hheight).mpr
      nlinarith [hb.2.1]
    · apply (div_le_iff₀ hheight).mpr
      nlinarith [hb.2.2]

theorem upperCutoff_C2 (Y : ℝ) (hY : 1 ≤ Y) :
    ContDiffOn ℝ 2 (extendUpper (upperCutoff Y hY)) positiveChart := by
  rw [extendUpper_upperCutoff]
  exact (planarCutoff_smooth Y hY).contDiffOn

theorem upperCutoff_support_region (Y : ℝ) (hY : 1 ≤ Y) :
    Function.support (extendUpper (upperCutoff Y hY)) ⊆
      region (cutoffRectangle Y hY) (cutoffMargin Y) := by
  rw [extendUpper_upperCutoff]
  exact planarCutoff_support_region Y hY

/-- Actual fundamental-domain geometry supplies BOTH coordinate bounds.
No assumed compact-set plateau or single-cusp approximation is used. -/
theorem upperCutoff_eq_one_on_truncated_cell (Y : ℝ) (hY : 1 ≤ Y)
    {z : UpperHalfPlane} (hz : z ∈ truncatedModularCell Y) :
    upperCutoff Y hY z = 1 := by
  have hx := abs_le.mp (modularFD_real_bound hz.1)
  have hy := (modularFD_half_lt_im hz.1).le
  have hp : (z.re,z.im) ∈
      PositiveRectangleSmoothTensorDensity20261025a.rectangle (1/2) (1/2) Y :=
    ⟨hx, hy, hz.2⟩
  have heq := congrFun (congrArg
    (fun f : C(PositiveRectangleSmoothTensorDensity20261025a.rectangle
      (1/2) (1/2) Y, ℂ) => (f : _ → ℂ))
    (restrict_cutoffTensor (1/2) (1/2) Y (by norm_num) (by norm_num) (by linarith)))
    ⟨(z.re,z.im), hp⟩
  exact heq

/-- The very same common cutoff fixes every genuine finite Gamma0 chart
on the common truncated cell. -/
theorem localized_chart_eq_pullback_on_cell (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y)
    (f : UpperHalfPlane → ℂ) (i : ChartIndex N) {z : UpperHalfPlane}
    (hz : z ∈ truncatedModularCell Y) :
    localizedClassChart N f (upperCutoff Y hY) (chartClass N i) z =
      f (chartMatrix N i • z) := by
  rw [localizedClassChart, upperCutoff_eq_one_on_truncated_cell Y hY hz, one_mul]
  rfl

/-- The constructed localized charts reconstruct the original function
exactly on the whole genuine finite core, with all overlaps assigned once. -/
theorem reconstruct_localized_charts (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y)
    (f : UpperHalfPlane → ℂ) :
    reconstruct N Y (fun i =>
      localizedClassChart N f (upperCutoff Y hY) (chartClass N i)) =
        (core N Y).indicator f := by
  classical
  funext z
  by_cases hz : z ∈ core N Y
  · obtain ⟨i, hi⟩ := mem_iUnion.mp ((chartPieces_cover N Y).symm ▸ hz)
    rw [reconstruct_on_piece N Y _ i hi, indicator_of_mem hz,
      localized_chart_eq_pullback_on_cell N Y hY f i (chartPiece_subset N Y i hi)]
    simp only [chartCoordinate, smul_inv_smul]
  · rw [reconstruct_outside_core N Y _ hz, indicator_of_notMem hz]

end
end ImbalancedChen.Part3.Gamma0TruncatedChartCutoff20261026b
