import ImbalancedChen.Part3GammaCompactSeedH1EnergyTransfer
import ImbalancedChen.Part3Gamma0WholeChartCoordinateWeakEquation
import ImbalancedChen.Part3MaassWeightedCoordinateL2

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The canonical compact-seed H1 budget is converted to ordinary coordinate
first jets. A fixed positive support floor pays precisely a^-2 in the
mass term. The Dirichlet term has no height loss: its y² cancels the
canonical density. Thus support-preserving ordinary H1 approximation
controls the actual quotient energy completion with one fixed constant.
-/

namespace ImbalancedChen.Part3.GammaFiniteSeedCoordinateH1Budget20261026b
noncomputable section
open Set Function Filter MeasureTheory
open scoped UpperHalfPlane ContDiff
open CanonicalTensorHyperbolicLaplacianForm20261024z MaassWeightedCoordinateL220261024zz
open MaassWeakOperatorCore20261024zz Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0CompactTensorPoincareC2Core20261025a Gamma0CompactUpperChartExtension20261025a
open Gamma0SmoothCompactTensorCore20261025a Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualSmoothQuotientMaassGraph20261025a Gamma0ActualEnergyCompletion20261025a
open ProductConvolutionSecondDerivatives20261026a Gamma0CompactGlobalOverlap20261025a
open GammaCompactSeedDirichletBudget20261026b GammaCompactSeedH1EnergyTransfer20261026b
open Gamma0WholeChartCoordinateWeakEquation20261026b ActualPoincareGradientEnergyBudget20261025a

def coordinateGradientSq (F : (ℝ × ℝ) → ℂ) (p : ℝ × ℝ) : ℝ :=
  ‖sliceDx F p‖^2 + ‖sliceDy F p‖^2

theorem canonical_seed_mass_coordinate (a : UpperHalfPlane → ℂ) :
    (∫ z : UpperHalfPlane, ‖a z‖^2) =
      ∫ p : ℝ × ℝ, (p.2⁻¹)^2 * ‖extendUpper a p‖^2 := by
  have h := canonical_real_integral_eq_chart (fun p => ‖extendUpper a p‖^2)
  have hzero : ∀ p ∉ upperChart, (p.2⁻¹)^2 * ‖extendUpper a p‖^2 = 0 := by
    intro p hp
    simp [extendUpper, hp]
  calc
    _ = ∫ p : ℝ × ℝ, ‖extendUpper a p‖^2 ∂chartMeasure := by
      simpa only [Complex.measurableEquivRealProd_apply, extendUpper_pair] using h
    _ = ∫ p in upperChart, (p.2⁻¹)^2 * ‖extendUpper a p‖^2 := by
      rw [chartMeasure, integral_withDensity_eq_integral_smul chartWeight_measurable]
      rfl
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero hzero

theorem inverse_square_mass_le {F : (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) {a : ℝ} (ha : 0 < a)
    (hs : ∀ p ∈ tsupport F, a ≤ p.2) :
    (∫ p : ℝ × ℝ, (p.2⁻¹)^2 * ‖F p‖^2) ≤ a⁻¹^2 * ∫ p : ℝ × ℝ, ‖F p‖^2 := by
  have hi := (hF.continuous.memLp_of_hasCompactSupport hc (p := (2 : ℝ≥0∞))).integrable_norm_pow
    (by decide : (2 : ℕ) ≠ 0)
  have hbound (p : ℝ × ℝ) : (p.2⁻¹)^2 * ‖F p‖^2 ≤ (a⁻¹)^2 * ‖F p‖^2 := by
    by_cases hp : p ∈ tsupport F
    · have hyp : 0 < p.2 := ha.trans_le (hs p hp)
      have hinv : p.2⁻¹ ≤ a⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le ha (hs p hp)
      have hsq := mul_self_le_mul_self (inv_pos.mpr hyp).le hinv
      exact mul_le_mul_of_nonneg_right (by simpa only [pow_two] using hsq) (sq_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hp]
  have hiw : Integrable (fun p : ℝ × ℝ => (p.2⁻¹)^2 * ‖F p‖^2) := by
    apply (hi.const_mul ((a⁻¹)^2)).mono'
      (((measurable_snd.inv.pow_const 2).aestronglyMeasurable).mul
        (hF.continuous.norm.pow 2).aestronglyMeasurable)
    exact Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact hbound p
  rw [← integral_const_mul]
  exact integral_mono hiw (hi.const_mul ((a⁻¹)^2)) hbound

/-- Exact Dirichlet coordinate transport: the support floor is needed
only for support geometry, not as an extra coefficient in this identity. -/
theorem canonical_seed_gradient_coordinate {F : (ℝ × ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hs : tsupport F ⊆ upperChart) :
    (∫ z : UpperHalfPlane, chartEnergy F (z.re,z.im)) =
      ∫ p : ℝ × ℝ, coordinateGradientSq F p := by
  have h := canonical_real_integral_eq_chart (chartEnergy F)
  rw [chartMeasure, integral_withDensity_eq_integral_smul chartWeight_measurable] at h
  have hcancel : (∫ p in upperChart, chartWeight p • chartEnergy F p) =
      ∫ p in upperChart, coordinateGradientSq F p := by
    apply setIntegral_congr_fun upperChart_measurable
    intro p hp
    have hc : (p.2⁻¹)^2 * p.2^2 = (1 : ℝ) := by
      rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hp), one_pow]
    change (p.2⁻¹)^2 * (p.2^2 * _) = _
    rw [← mul_assoc, hc, one_mul]
    rfl
  have hzero : ∀ p ∉ upperChart, coordinateGradientSq F p = 0 := by
    intro p hp
    have hout : p ∉ tsupport F := fun h => hp (hs h)
    have hx : sliceDx F p = directional xDirection F p := (directional_x_eq_slice hF p).symm
    have hy : sliceDy F p = directional yDirection F p := (directional_y_eq_slice hF p).symm
    simp only [coordinateGradientSq, hx, hy, directional, fderiv_of_notMem_tsupport hout,
      ContinuousLinearMap.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  rw [hcancel, setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at h
  simpa only [Complex.measurableEquivRealProd_apply] using h

/-- The original finite seed now has an ordinary first-jet budget.
Its one compact support container and one positive floor are fixed
before any approximant or subtraction seed is chosen. -/
theorem finite_seed_coordinate_energy_bound (N : ℕ) [NeZero N] (s : SmoothSeed)
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hsK : finiteCompactTensorSupportK Finset.univ (seedTensors s) ⊆ K)
    {a : ℝ} (ha : 0 < a) (hfloor : ∀ z ∈ K, a ≤ z.im) :
    ‖(seedCoreElement N s : EnergyCore N)‖^2 ≤ (compactOverlapBound N K : ℝ) *
      ((a⁻¹)^2 * (∫ p : ℝ × ℝ, ‖finiteChartFunction Finset.univ (seedTensors s) p‖^2) +
        ∫ p : ℝ × ℝ, coordinateGradientSq (finiteChartFunction Finset.univ (seedTensors s)) p) := by
  let F := finiteCoreFunction Finset.univ (seedTensors s)
  have hc : HasCompactSupport F := HasCompactSupport.of_support_subset_isCompact
    (finiteCompactTensorSupportK_isCompact Finset.univ (seedTensors s))
    (finiteCoreFunction_support_subset Finset.univ (seedTensors s))
  have htc : tsupport F ⊆ K :=
    closure_minimal ((finiteCoreFunction_support_subset Finset.univ (seedTensors s)).trans hsK)
      hK.isClosed
  have hsm := finiteSmoothChart_contDiff Finset.univ s.2
  have hext : extendUpper F = finiteChartFunction Finset.univ (seedTensors s) :=
    extendUpper_finiteCoreFunction _ _
  have hsmExt : ContDiff ℝ ∞ (extendUpper F) := by
    rw [hext]
    exact hsm
  have hsup : tsupport (extendUpper F) ⊆ upperChart := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := extendUpper_support_image F hc hp
    exact z.im_pos
  have hheight : ∀ p ∈ tsupport (extendUpper F), a ≤ p.2 := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := extendUpper_support_image F hc hp
    exact hfloor z (htc hz)
  have hm := inverse_square_mass_le hsmExt (extendUpper_hasCompactSupport F hc) ha hheight
  have hmass := canonical_seed_mass_coordinate F
  have hgrad := canonical_seed_gradient_coordinate hsmExt hsup
  have hbudget := finite_seed_shifted_energy_norm_sq_le N s hK hsK
  change ‖(seedCoreElement N s : EnergyCore N)‖^2 ≤ (compactOverlapBound N K : ℝ) *
    ((∫ z : UpperHalfPlane, ‖F z‖^2) + ∫ z : UpperHalfPlane, chartEnergy (extendUpper F) (z.re,z.im))
    at hbudget
  rw [hmass, hgrad] at hbudget
  apply hbudget.trans
  rw [← hext]
  exact mul_le_mul_of_nonneg_left (add_le_add_right hm _) (Nat.cast_nonneg _)

end
end ImbalancedChen.Part3.GammaFiniteSeedCoordinateH1Budget20261026b
