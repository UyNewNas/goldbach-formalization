import ImbalancedChen.Part3PositiveZeroModeLogHeightCutoff
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Positive scalar zero-mode uniqueness on the FULL positive-height line.
The actual equation -y^2 f''+a f=0 with a>0 and global physical L2(dy/y^2)
mass forces f=0. Constructed smooth logheight cutoffs, the proved physical
Caccioppoli estimate, actual global mass domination and exhaustion supply
the proof. No Euler basis, growth condition, energy estimate or range-
density conclusion is assumed. The final theorem accepts genuine C2
regularity and the actual scalar ODE, deriving the native jets internally.

This scalar theorem does NOT identify the quotient-vector horocycle mean
with an admissible global physical L2 solution. That actual quotient
global-mean L2/admissibility bridge remains OPEN; no automorphic deficiency
range density or restricted resolvent reduction is inferred here.
-/
namespace ImbalancedChen.Part3.PositiveZeroModeGlobalL2Uniqueness20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open PositiveZeroModePhysicalCaccioppoli20261026b
open PositiveZeroModeLogHeightCutoff20261026b
open RadialWeightedCutoffDensity20261025a

def physicalMassDensity (f : ℝ → ℂ) (y : ℝ) : ℝ := Complex.normSq (f y) / y^2

theorem physicalMassDensity_nonneg (f : ℝ → ℂ) (y : ℝ) : 0 ≤ physicalMassDensity f y :=
  div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)

/-- Literal dy/y^2 measure on the positive real-height carrier. -/
def physicalZeroModeDensity (y : ℝ) : ℝ≥0 := ⟨(y⁻¹)^2, sq_nonneg _⟩

def physicalZeroModeMeasure : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).withDensity
    (fun y => (physicalZeroModeDensity y : ℝ≥0∞))

theorem physicalZeroModeDensity_measurable : Measurable physicalZeroModeDensity := by
  unfold physicalZeroModeDensity
  fun_prop

/-- Actual physical MemLp supplies the global integrable squared mass;
it is not introduced as an assumed energy conclusion. -/
theorem physicalMassDensity_integrable_of_memLp {f : ℝ → ℂ}
    (hf : MemLp f 2 physicalZeroModeMeasure) :
    IntegrableOn (physicalMassDensity f) (Ioi (0 : ℝ)) := by
  have hs : Integrable (fun y => Complex.normSq (f y)) physicalZeroModeMeasure := by
    simpa only [Complex.normSq_eq_norm_sq] using
      (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hw := (integrable_withDensity_iff_integrable_smul₀
    physicalZeroModeDensity_measurable.aemeasurable).mp hs
  change IntegrableOn (fun y => (y⁻¹)^2 * Complex.normSq (f y)) (Ioi (0 : ℝ)) at hw
  convert hw using 1
  funext y
  simp only [physicalMassDensity, div_eq_mul_inv, inv_pow]
  ring

private theorem localized_mass_interval_eq_global (n : ℕ) (f : ℝ → ℂ) :
    (∫ y in lowerHeightEndpoint n..upperHeightEndpoint n,
      (logHeightCutoff n y)^2 * Complex.normSq (f y) / y^2) =
      ∫ y in Ioi (0 : ℝ), (logHeightCutoff n y)^2 * physicalMassDensity f y := by
  have heq : (fun y => (logHeightCutoff n y)^2 * Complex.normSq (f y) / y^2) =
      (fun y => (logHeightCutoff n y)^2 * physicalMassDensity f y) := by
    funext y
    dsimp [physicalMassDensity]
    ring
  rw [heq, intervalIntegral.integral_of_le (heightEndpoints_le n)]
  have hzeroI : ∀ y : ℝ, y ∉ Ioc (lowerHeightEndpoint n) (upperHeightEndpoint n) →
      (logHeightCutoff n y)^2 * physicalMassDensity f y = 0 := by
    intro y hy
    by_cases hlo : y ≤ lowerHeightEndpoint n
    · rw [logHeightCutoff_zero_left n y hlo, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    · have hhi : upperHeightEndpoint n ≤ y :=
        le_of_not_ge (fun h => hy ⟨lt_of_not_ge hlo, h⟩)
      rw [logHeightCutoff_zero_right n y hhi, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
  have hzeroP : ∀ y : ℝ, y ∉ Ioi (0 : ℝ) →
      (logHeightCutoff n y)^2 * physicalMassDensity f y = 0 := by
    intro y hy
    rw [logHeightCutoff_zero_left n y ((le_of_not_gt hy).trans (lowerHeightEndpoint_pos n).le),
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzeroI,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzeroP]

/-- The constructed physical cutoffs pay their errors using the input's
OWN global dy/y^2 mass, with a genuinely vanishing universal rate. -/
theorem global_physical_cutoff_mass_bound {a : ℝ} {f : ℝ → ℂ}
    (hf : PositiveHeightSolution a f)
    (hmass : IntegrableOn (physicalMassDensity f) (Ioi (0 : ℝ))) (n : ℕ) :
    a * (∫ y in Ioi (0 : ℝ), (logHeightCutoff n y)^2 * physicalMassDensity f y) ≤
      (derivativeConstant / cutoffRadius n)^2 * (∫ y in Ioi (0 : ℝ), physicalMassDensity f y) := by
  have hC := physical_positive_zeroMode_Caccioppoli hf (lowerHeightEndpoint_pos n)
    (heightEndpoints_le n) (logHeightCutoff n) ((logHeightCutoff_cinfty n).of_le (by simp))
    (logHeightCutoff_zero_left n _ le_rfl) (logHeightCutoff_zero_right n _ le_rfl)
  rw [localized_mass_interval_eq_global] at hC
  obtain ⟨_hMi, hEi⟩ := physical_cutoff_terms_integrable hf (lowerHeightEndpoint_pos n)
    (heightEndpoints_le n) (logHeightCutoff n) ((logHeightCutoff_cinfty n).of_le (by simp))
  have hsub : Ioc (lowerHeightEndpoint n) (upperHeightEndpoint n) ⊆ Ioi (0 : ℝ) :=
    fun y hy => (lowerHeightEndpoint_pos n).trans hy.1
  have hMi : IntervalIntegrable (physicalMassDensity f) volume
      (lowerHeightEndpoint n) (upperHeightEndpoint n) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (heightEndpoints_le n)).mpr (hmass.mono_set hsub)
  have hErr : (∫ y in lowerHeightEndpoint n..upperHeightEndpoint n,
      (deriv (logHeightCutoff n) y)^2 * Complex.normSq (f y)) ≤
      (derivativeConstant / cutoffRadius n)^2 *
        (∫ y in Ioi (0 : ℝ), physicalMassDensity f y) := by
    calc
      _ ≤ ∫ y in lowerHeightEndpoint n..upperHeightEndpoint n,
          (derivativeConstant / cutoffRadius n)^2 * physicalMassDensity f y := by
        apply intervalIntegral.integral_mono_on (heightEndpoints_le n) hEi (hMi.const_mul _)
        intro y hy
        have hy' : y ∈ Icc (lowerHeightEndpoint n) (upperHeightEndpoint n) := by
          simpa only [uIcc_of_le (heightEndpoints_le n)] using hy
        exact logHeightCutoff_error_density_bound n f ((lowerHeightEndpoint_pos n).trans_le hy'.1)
      _ = (derivativeConstant / cutoffRadius n)^2 *
          (∫ y in lowerHeightEndpoint n..upperHeightEndpoint n, physicalMassDensity f y) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        rw [intervalIntegral.integral_of_le (heightEndpoints_le n)]
        exact setIntegral_mono_set hmass
          (Filter.Eventually.of_forall (physicalMassDensity_nonneg f))
          (Filter.Eventually.of_forall (fun y hy => hsub hy))
  exact hC.trans hErr

theorem localized_physical_mass_tendsto (f : ℝ → ℂ)
    (hmass : IntegrableOn (physicalMassDensity f) (Ioi (0 : ℝ))) :
    Tendsto (fun n : ℕ => ∫ y in Ioi (0 : ℝ),
      (logHeightCutoff n y)^2 * physicalMassDensity f y) atTop
      (𝓝 (∫ y in Ioi (0 : ℝ), physicalMassDensity f y)) := by
  apply tendsto_integral_of_dominated_convergence (physicalMassDensity f)
  · intro n
    exact (((logHeightCutoff_cinfty n).continuous.aestronglyMeasurable.pow 2).mul
      hmass.aestronglyMeasurable)
  · exact hmass
  · intro n
    apply Filter.Eventually.of_forall
    intro y
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (sq_nonneg _) (physicalMassDensity_nonneg f y))]
    exact (mul_le_mul_of_nonneg_right (logHeightCutoff_sq_le_one n y)
      (physicalMassDensity_nonneg f y)).trans_eq (one_mul _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_logHeightCutoff_eq_one y hy] with n hn
    simp only [hn, one_pow, one_mul]

/-- Global mass vanishes by positive coercivity and actual smooth
exhaustion at BOTH height ends. No derivative-L2 premise is used. -/
theorem positive_zeroMode_global_mass_zero {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : PositiveHeightSolution a f)
    (hmass : IntegrableOn (physicalMassDensity f) (Ioi (0 : ℝ))) :
    (∫ y in Ioi (0 : ℝ), physicalMassDensity f y) = 0 := by
  have hleft := (tendsto_const_nhds (x := a)).mul (localized_physical_mass_tendsto f hmass)
  have hright := logHeightCutoff_error_rate_tendsto.mul
    (tendsto_const_nhds (x := ∫ y in Ioi (0 : ℝ), physicalMassDensity f y))
  have hle : a * (∫ y in Ioi (0 : ℝ), physicalMassDensity f y) ≤ 0 := by
    simpa only [zero_mul] using le_of_tendsto_of_tendsto hleft hright
      (Filter.Eventually.of_forall (global_physical_cutoff_mass_bound hf hmass))
  have hnonneg : 0 ≤ ∫ y in Ioi (0 : ℝ), physicalMassDensity f y :=
    integral_nonneg (physicalMassDensity_nonneg f)
  nlinarith

theorem positive_zeroMode_integrable_mass_unique {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : PositiveHeightSolution a f)
    (hmass : IntegrableOn (physicalMassDensity f) (Ioi (0 : ℝ))) :
    ∀ y : ℝ, 0 < y → f y = 0 := by
  have hzero : physicalMassDensity f =ᵐ[(volume : Measure ℝ).restrict (Ioi (0 : ℝ))] 0 :=
    (integral_eq_zero_iff_of_nonneg (physicalMassDensity_nonneg f) hmass).mp
      (positive_zeroMode_global_mass_zero ha hf hmass)
  have hfc : ContinuousOn f (Ioi (0 : ℝ)) :=
    fun y hy => (hf y hy).1.continuousAt.continuousWithinAt
  have hmc : ContinuousOn (physicalMassDensity f) (Ioi (0 : ℝ)) :=
    (Complex.continuous_normSq.comp_continuousOn hfc).div (continuousOn_id.pow 2)
      (fun y hy => pow_ne_zero 2 (ne_of_gt hy))
  have heq := eqOn_open_of_ae_eq hzero isOpen_Ioi hmc continuousOn_const
  intro y hy
  have hnorm : Complex.normSq (f y) = 0 := by
    have h := heq hy
    change Complex.normSq (f y) / y^2 = 0 at h
    exact (div_eq_zero_iff.mp h).resolve_right (pow_ne_zero 2 hy.ne')
  exact Complex.normSq_eq_zero.mp hnorm

theorem positive_zeroMode_memLp_unique {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hf : PositiveHeightSolution a f) (hL2 : MemLp f 2 physicalZeroModeMeasure) :
    ∀ y : ℝ, 0 < y → f y = 0 :=
  positive_zeroMode_integrable_mass_unique ha hf (physicalMassDensity_integrable_of_memLp hL2)

/-- Genuine C2+scalar-ODE endpoint. Its native derivative jets are
constructed from actual C2 regularity and the actual physical equation. -/
theorem positive_zeroMode_C2_memLp_unique {a : ℝ} (ha : 0 < a) (f : ℝ → ℂ)
    (hC2 : ContDiffOn ℝ 2 f (Ioi (0 : ℝ))) (hL2 : MemLp f 2 physicalZeroModeMeasure)
    (hODE : ∀ y : ℝ, 0 < y →
      (-((y : ℂ)^2)) * deriv (deriv f) y + (a : ℂ) * f y = 0) :
    ∀ y : ℝ, 0 < y → f y = 0 := by
  apply positive_zeroMode_memLp_unique ha _ hL2
  intro y hy
  have hcy : ContDiffAt ℝ 2 f y := (hC2 y hy).contDiffAt (isOpen_Ioi.mem_nhds hy)
  have hdf : DifferentiableAt ℝ (deriv f) y :=
    (hcy.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  refine ⟨(hcy.differentiableAt (by norm_num)).hasDerivAt, ?_⟩
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have he : deriv (deriv f) y = (a : ℂ) * f y / (y : ℂ)^2 :=
    (eq_div_iff (pow_ne_zero 2 hyC)).mpr (by linear_combination -(hODE y hy))
  have hv : deriv (deriv f) y = (((a / y^2 : ℝ) : ℂ) * f y) := by
    rw [he, Complex.ofReal_div, Complex.ofReal_pow]
    ring
  exact hdf.hasDerivAt.congr_deriv hv

end
end ImbalancedChen.Part3.PositiveZeroModeGlobalL2Uniqueness20261026b
