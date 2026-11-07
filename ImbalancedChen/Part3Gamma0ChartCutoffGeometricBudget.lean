import ImbalancedChen.Part3Gamma0TruncatedChartCutoff
import ImbalancedChen.Part3PositiveRectangleNativeHyperbolicL2
import ImbalancedChen.Part3Gamma0LocalizedChartIntegralBudget

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The constructed chart cutoff has genuine compact native support, global
norm at most one, and a proved finite nonnegative geometric gradient bound
on that actual support. Every localized inverse-class chart has support
inside this same compact set, before choosing an automorphic function.
No input bound on the automorphic chart energy is introduced here.
-/

namespace ImbalancedChen.Part3.Gamma0ChartCutoffGeometricBudget20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open Gamma0TruncatedChartCutoff20261026b
open PositiveRectangleAffineNormalization20261026b
open PositiveRectangleNativeHyperbolicL220261026b
open PositiveCompactTensorLpApproximation20261025a
open Gamma0LocalFourierTailCharts20261026a
open Gamma0LocalizedChartIntegralBudget20261026b
open ActualPoincareGradientEnergyBudget20261025a

def cutoffSeed (Y : ℝ) (hY : 1 ≤ Y) :
    RectangleSeed (cutoffRectangle Y hY) (cutoffMargin Y) :=
  ⟨planarCutoff Y hY, planarCutoff_smooth Y hY, planarCutoff_support_region Y hY⟩

theorem upperCutoff_compact (Y : ℝ) (hY : 1 ≤ Y) :
    HasCompactSupport (upperCutoff Y hY) :=
  nativeFunction_compact (cutoffMargin_pos hY).le (cutoffSeed Y hY)

def cutoffCompactSet (Y : ℝ) (hY : 1 ≤ Y) : Set UpperHalfPlane :=
  tsupport (upperCutoff Y hY)

theorem cutoffCompactSet_isCompact (Y : ℝ) (hY : 1 ≤ Y) :
    IsCompact (cutoffCompactSet Y hY) := upperCutoff_compact Y hY

theorem upperCutoff_norm_le_one (Y : ℝ) (hY : 1 ≤ Y) (z : UpperHalfPlane) :
    ‖upperCutoff Y hY z‖ ≤ 1 :=
  cutoff_norm_le_one (1/2) (1/2) Y (by norm_num) (by norm_num) (by linarith) (z.re,z.im)

theorem exists_cutoffGradientConstant (Y : ℝ) (hY : 1 ≤ Y) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ cutoffCompactSet Y hY,
      chartEnergy (MaassWeakOperatorCore20261024zz.extendUpper (upperCutoff Y hY))
        (z.re,z.im) ≤ D := by
  have hc := native_chartEnergy_continuous (upperCutoff Y hY) (upperCutoff_C2 Y hY)
  obtain ⟨b, hb⟩ := (cutoffCompactSet_isCompact Y hY).bddAbove_image hc.continuousOn
  refine ⟨max b 0, le_max_right _ _, ?_⟩
  intro z hz
  exact (hb ⟨z, hz, rfl⟩).trans (le_max_left _ _)

/-- A fixed finite constant depending only on Y and the explicit cutoff,
chosen before any member of the quotient energy family. -/
def cutoffGradientConstant (Y : ℝ) (hY : 1 ≤ Y) : ℝ :=
  Classical.choose (exists_cutoffGradientConstant Y hY)

theorem cutoffGradientConstant_nonneg (Y : ℝ) (hY : 1 ≤ Y) :
    0 ≤ cutoffGradientConstant Y hY :=
  (Classical.choose_spec (exists_cutoffGradientConstant Y hY)).1

theorem cutoffGradientConstant_bound (Y : ℝ) (hY : 1 ≤ Y)
    {z : UpperHalfPlane} (hz : z ∈ cutoffCompactSet Y hY) :
    chartEnergy (MaassWeakOperatorCore20261024zz.extendUpper (upperCutoff Y hY))
      (z.re,z.im) ≤ cutoffGradientConstant Y hY :=
  (Classical.choose_spec (exists_cutoffGradientConstant Y hY)).2 z hz

theorem localized_chart_tsupport_subset (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y)
    (f : UpperHalfPlane → ℂ)
    (q : Gamma0FiniteMeasureCarrier20261024z.gamma0Classes N) :
    tsupport (localizedClassChart N f (upperCutoff Y hY) q) ⊆ cutoffCompactSet Y hY := by
  change tsupport ((upperCutoff Y hY) *
    (fun z => f (Gamma0FiniteMeasureCarrier20261024z.inverseClassRep N q • z))) ⊆ _
  exact tsupport_mul_subset_left

/-- One compact native support works for every actual finite chart and
every input function; compactness is inherited from the constructed rho. -/
theorem localized_chart_compact (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y)
    (f : UpperHalfPlane → ℂ)
    (q : Gamma0FiniteMeasureCarrier20261024z.gamma0Classes N) :
    HasCompactSupport (localizedClassChart N f (upperCutoff Y hY) q) := by
  exact (cutoffCompactSet_isCompact Y hY).of_isClosed_subset isClosed_tsupport
    (localized_chart_tsupport_subset N Y hY f q)

end
end ImbalancedChen.Part3.Gamma0ChartCutoffGeometricBudget20261026b
