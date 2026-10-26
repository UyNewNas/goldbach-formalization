import ImbalancedChen.Part3PositiveRectangleNativeDerivativeEnergy
import ImbalancedChen.Part3Gamma0ChartCutoffGeometricBudget
import ImbalancedChen.Part3Gamma0FixedCoreRellich

/-! SOURCE_ONLY / UNCOMPILED / zero formal credit.
The constructed cutoff has B=1 and a proved fixed own-gradient constant.
Actual quotient form energy now yields the actualSeed physical H1 bound
for every genuine finite class, with no hChartBudget premise. Consequently
bounded ORIGINAL smooth energy-core families are totally bounded on the
actual fixed quotient core. Completed-domain passage is separate. -/

namespace ImbalancedChen.Part3.Gamma0QuotientFormChartBudgets20261026b
noncomputable section
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane BigOperators
open Gamma0QuotientCellPushforward20261025a
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0FiniteMeasureCarrier20261024z
open Gamma0FiniteChartReconstruction20261026b
open Gamma0FixedCoreRellich20261026b
open Gamma0TruncatedChartCutoff20261026b
open Gamma0ChartCutoffGeometricBudget20261026b
open Gamma0LocalizedChartIntegralBudget20261026b
open PositiveRectangleNativeDerivativeEnergy20261026b
open PositiveRectangleAffineNormalization20261026b
open PositiveRectanglePhysicalRellich20261026b
open PositiveRectangleNativeHyperbolicL220261026b
open Gamma0LocalFourierTailCharts20261026a
open Gamma0CompactTensorPoincareC2Core20261025a
open ActualPoincareGradientEnergyBudget20261025a
open MaassWeakOperatorCore20261024zz

local instance (N : ℕ) [NeZero N] : Fintype (gamma0Classes N) :=
  (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex

def coreSmoothQuotient (N : ℕ) [NeZero N] (u : EnergyCore N) : SmoothQuotient N where
  function := chosenQuotientRepresentative N u
  measurable := measurable_from_quotient.mpr (coreRepresentative_continuous N u).measurable
  memLp := (u : QuotientL2 N).memLp.ae_eq (chosenRepresentative_spec N u).1
  smooth := (coreRepresentative_cinfty N u).of_le (by norm_num)

def actualCoreSeed (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y)
    (u : EnergyCore N) (q : gamma0Classes N) :
    RectangleSeed (cutoffRectangle Y hY) (cutoffMargin Y) :=
  Gamma0PositiveRectangleRellichCharts20261026b.classSeed N (cutoffRectangle Y hY)
    (cutoffMargin_pos hY).le (upperCutoff Y hY) (upperCutoff_C2 Y hY)
    (upperCutoff_support_region Y hY)
    ⟨coreRepresentative N u,(coreRepresentative_cinfty N u).of_le (by norm_num)⟩ q

def localFormBudgetConstant (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y)
    (q : gamma0Classes N) : ℝ :=
  (((cutoffRectangle Y hY).bottom+(cutoffRectangle Y hY).height)^2+1) *
    (chartOverlap N (cutoffCompactSet Y hY) q : ℝ) * (3+2*cutoffGradientConstant Y hY)

theorem localFormBudgetConstant_nonneg (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y)
    (q : gamma0Classes N) : 0 ≤ localFormBudgetConstant N Y hY q := by
  have hD := cutoffGradientConstant_nonneg Y hY
  unfold localFormBudgetConstant
  positivity

/-- The actual physical H1 budget is derived from the ORIGINAL quotient
shifted form norm. No assumed chart mass or derivative supplier occurs. -/
theorem actualCoreSeed_h1_bound (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y)
    (u : EnergyCore N) (q : gamma0Classes N) :
    ‖physical (actualCoreSeed N Y hY u q)‖^2 + energy (actualCoreSeed N Y hY u q) ≤
      localFormBudgetConstant N Y hY q * ‖u‖^2 := by
  let f := localizedClassChart N (coreRepresentative N u) (upperCutoff Y hY) q
  let s := actualCoreSeed N Y hY u q
  have hf : ContDiffOn ℝ 2 (extendUpper f) positiveChart :=
    localizedClassChart_C2 N (coreRepresentative N u) (upperCutoff Y hY)
      ((coreRepresentative_cinfty N u).of_le (by norm_num)) (upperCutoff_C2 Y hY) q
  have hfc : HasCompactSupport f := localized_chart_compact N Y hY (coreRepresentative N u) q
  have hm : Integrable (fun z : UpperHalfPlane => ‖f z‖^2) :=
    ((native_C2_continuous f hf).norm.pow 2).integrable_of_hasCompactSupport
      (hfc.norm.comp_left (g := fun t : ℝ => t^2) (by simp))
  have hg : Integrable (fun z : UpperHalfPlane => chartEnergy (extendUpper f) (z.re,z.im)) :=
    (native_chartEnergy_continuous f hf).integrable_of_hasCompactSupport
      (native_chartEnergy_compact f hfc)
  have hr := native_mass_energy_restrict_support f (cutoffCompactSet Y hY)
    (localized_chart_tsupport_subset N Y hY (coreRepresentative N u) q)
  rw [integral_add hm hg] at hr
  have he := physical_h1_le_native_mass_energy (cutoffMargin_pos hY).le s
  have hnative : nativeFunction s = f := by
    funext z
    exact ActualGamma0MaassDescent20261025a.extendUpper_pair _ z
  have hplane : s.function = extendUpper f := rfl
  rw [hnative,hplane,← hr] at he
  have hb := localizedChartH1Mass_energy_bound N (cutoffCompactSet_isCompact Y hY) u
    (upperCutoff Y hY) (upperCutoff_C2 Y hY) q 1 (cutoffGradientConstant Y hY)
    (by norm_num) (cutoffGradientConstant_nonneg Y hY)
    (fun z _ => upperCutoff_norm_le_one Y hY z)
    (fun z hz => cutoffGradientConstant_bound Y hY hz)
  have hmul := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ ((cutoffRectangle Y hY).bottom+(cutoffRectangle Y hY).height)^2+1 by positivity)
  apply he.trans
  simpa only [localFormBudgetConstant,one_pow,mul_one,mul_assoc] using hmul

def uniformFormBudgetConstant (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y) : ℝ :=
  ∑ q : gamma0Classes N, localFormBudgetConstant N Y hY q

theorem uniformFormBudgetConstant_nonneg (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y) :
    0 ≤ uniformFormBudgetConstant N Y hY :=
  Finset.sum_nonneg (fun q _ => localFormBudgetConstant_nonneg N Y hY q)

theorem coreSmoothQuotient_mem_localEnergyFamily (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) (A : ℝ) (u : EnergyCore N) (hu : ‖u‖^2 ≤ A) :
    coreSmoothQuotient N u ∈ localEnergyFamily N Y hY (uniformFormBudgetConstant N Y hY*A) := by
  intro i
  have h := actualCoreSeed_h1_bound N Y hY u (chartClass N i)
  have hC : localFormBudgetConstant N Y hY (chartClass N i) ≤ uniformFormBudgetConstant N Y hY :=
    Finset.single_le_sum (fun q _ => localFormBudgetConstant_nonneg N Y hY q)
      (Finset.mem_univ (chartClass N i))
  have h1 := mul_le_mul_of_nonneg_right hC (sq_nonneg ‖u‖)
  have h2 := mul_le_mul_of_nonneg_left hu (uniformFormBudgetConstant_nonneg N Y hY)
  change ‖physical (actualSeed N Y hY (coreSmoothQuotient N u) i)‖^2 +
    energy (actualSeed N Y hY (coreSmoothQuotient N u) i) ≤ _
  exact h.trans (h1.trans h2)

/-- Fixed-truncation compactness now has ONLY the original quotient
energy-core norm bound as automorphic input. The former localEnergyFamily
condition is produced by the actual form-gradient and cutoff arguments. -/
theorem actual_quotient_core_energy_ball_totallyBounded (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) (A : ℝ) (hA : 0 ≤ A) :
    TotallyBounded ((fun u : EnergyCore N => coreL2 N Y (coreSmoothQuotient N u)) ''
      {u : EnergyCore N | ‖u‖^2 ≤ A}) := by
  apply (fixed_core_energy_family_totallyBounded N Y hY
    (uniformFormBudgetConstant N Y hY*A)
    (mul_nonneg (uniformFormBudgetConstant_nonneg N Y hY) hA)).subset
  rintro v ⟨u,hu,rfl⟩
  exact ⟨coreSmoothQuotient N u,coreSmoothQuotient_mem_localEnergyFamily N Y hY A u hu,rfl⟩

end
end ImbalancedChen.Part3.Gamma0QuotientFormChartBudgets20261026b
