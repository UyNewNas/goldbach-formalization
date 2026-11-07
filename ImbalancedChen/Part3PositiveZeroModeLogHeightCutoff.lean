import ImbalancedChen.Part3PositiveZeroModePhysicalCaccioppoli
import ImbalancedChen.Part3RadialScaledSmoothCutoff
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Construct smooth physical-height cutoffs by composing the existing clean
symmetric real-line bump cutoff with log y. The zero extension through
y=0 is smooth because the cutoff vanishes below its positive exponential
lower endpoint. Both positive-height endpoints vanish, the cutoff tends
pointwise to one on y>0, and its ACTUAL derivative is bounded by
C/((n+1)y). The physical cutoff-error density is bounded by the square
of C/(n+1) times the original dy/y^2 mass density.
No held zero-mode log-operator or Liouville source is imported.
-/
namespace ImbalancedChen.Part3.PositiveZeroModeLogHeightCutoff20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open RadialWeightedCutoffDensity20261025a

def lowerHeightEndpoint (n : ℕ) : ℝ := Real.exp (-2 * cutoffRadius n)
def upperHeightEndpoint (n : ℕ) : ℝ := Real.exp (2 * cutoffRadius n)

theorem lowerHeightEndpoint_pos (n : ℕ) : 0 < lowerHeightEndpoint n := Real.exp_pos _
theorem heightEndpoints_le (n : ℕ) : lowerHeightEndpoint n ≤ upperHeightEndpoint n :=
  Real.exp_le_exp.mpr (by linarith [cutoffRadius_pos n])

private theorem cutoff_zero_of_abs_ge (n : ℕ) (r : ℝ) (hr : 2 * cutoffRadius n ≤ |r|) :
    cutoff n r = 0 := by
  apply baseBump.zero_of_le_dist
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (cutoffRadius_pos n)]
  exact (le_div_iff₀ (cutoffRadius_pos n)).mpr hr

def logHeightCutoff (n : ℕ) (y : ℝ) : ℝ := if 0 < y then cutoff n (Real.log y) else 0

theorem logHeightCutoff_zero_left (n : ℕ) (y : ℝ) (hy : y ≤ lowerHeightEndpoint n) :
    logHeightCutoff n y = 0 := by
  by_cases hypos : 0 < y
  · rw [logHeightCutoff, if_pos hypos]
    apply cutoff_zero_of_abs_ge
    have hl : Real.log y ≤ -2 * cutoffRadius n := by
      simpa only [lowerHeightEndpoint, Real.log_exp] using Real.log_le_log hypos hy
    linarith [neg_le_abs (Real.log y)]
  · simp only [logHeightCutoff, if_neg hypos]

theorem logHeightCutoff_zero_right (n : ℕ) (y : ℝ) (hy : upperHeightEndpoint n ≤ y) :
    logHeightCutoff n y = 0 := by
  have hypos : 0 < y := (Real.exp_pos (2 * cutoffRadius n)).trans_le hy
  rw [logHeightCutoff, if_pos hypos]
  apply cutoff_zero_of_abs_ge
  have hl : 2 * cutoffRadius n ≤ Real.log y := by
    simpa only [upperHeightEndpoint, Real.log_exp] using
      Real.log_le_log (Real.exp_pos (2 * cutoffRadius n)) hy
  exact hl.trans (le_abs_self _)

theorem logHeightCutoff_cinfty (n : ℕ) : ContDiff ℝ ∞ (logHeightCutoff n) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : 0 < y
  · have heq : logHeightCutoff n =ᶠ[𝓝 y] (fun t => cutoff n (Real.log t)) := by
      filter_upwards [Ioi_mem_nhds hy] with t ht
      exact if_pos ht
    exact ((cutoff_smooth n).contDiffAt.comp y (Real.contDiffAt_log hy.ne')).congr_of_eventuallyEq heq
  · have hyl : y < lowerHeightEndpoint n := lt_of_le_of_lt (le_of_not_gt hy) (lowerHeightEndpoint_pos n)
    have heq : logHeightCutoff n =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hyl] with t ht
      exact logHeightCutoff_zero_left n t ht.le
    exact contDiffAt_const.congr_of_eventuallyEq heq

theorem logHeightCutoff_compact (n : ℕ) : HasCompactSupport (logHeightCutoff n) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact
    (Icc (lowerHeightEndpoint n) (upperHeightEndpoint n)))
  intro y hy
  by_cases hlo : lowerHeightEndpoint n ≤ y
  · exact logHeightCutoff_zero_right n y (le_of_not_ge (fun hhi => hy ⟨hlo, hhi⟩))
  · exact logHeightCutoff_zero_left n y (le_of_not_ge hlo)

theorem logHeightCutoff_range (n : ℕ) (y : ℝ) :
    0 ≤ logHeightCutoff n y ∧ logHeightCutoff n y ≤ 1 := by
  by_cases hy : 0 < y
  · simpa only [logHeightCutoff, if_pos hy] using cutoff_range n (Real.log y)
  · simp only [logHeightCutoff, if_neg hy, le_refl, zero_le_one, and_self]

theorem logHeightCutoff_sq_le_one (n : ℕ) (y : ℝ) : (logHeightCutoff n y)^2 ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := logHeightCutoff_range n y
  nlinarith

theorem eventually_logHeightCutoff_eq_one (y : ℝ) (hy : 0 < y) :
    ∀ᶠ n : ℕ in atTop, logHeightCutoff n y = 1 := by
  simpa only [logHeightCutoff, if_pos hy] using eventually_cutoff_eq_one (Real.log y)

theorem logHeightCutoff_deriv (n : ℕ) {y : ℝ} (hy : 0 < y) :
    deriv (logHeightCutoff n) y = deriv (cutoff n) (Real.log y) * y⁻¹ := by
  have heq : logHeightCutoff n =ᶠ[𝓝 y] (fun t => cutoff n (Real.log t)) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact if_pos ht
  have hd := ((cutoff_smooth n).differentiable (by simp) (Real.log y)).hasDerivAt.comp y
    (Real.hasDerivAt_log hy.ne')
  rw [heq.deriv_eq, hd.deriv]

theorem logHeightCutoff_deriv_bound (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ‖deriv (logHeightCutoff n) y‖ ≤ (derivativeConstant / cutoffRadius n) / y := by
  rw [logHeightCutoff_deriv n hy, norm_mul, norm_inv, Real.norm_of_nonneg hy.le]
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right
    (cutoff_derivative_bound n (Real.log y)) (inv_nonneg.mpr hy.le)

/-- Exact original physical mass weight after the actual logarithmic
chain derivative: there is no missing y factor. -/
theorem logHeightCutoff_error_density_bound (n : ℕ) (f : ℝ → ℂ) {y : ℝ} (hy : 0 < y) :
    (deriv (logHeightCutoff n) y)^2 * Complex.normSq (f y) ≤
      (derivativeConstant / cutoffRadius n)^2 * (Complex.normSq (f y) / y^2) := by
  have hs := pow_le_pow_left₀ (norm_nonneg (deriv (logHeightCutoff n) y))
    (logHeightCutoff_deriv_bound n hy) 2
  have hsq : (deriv (logHeightCutoff n) y)^2 ≤
      ((derivativeConstant / cutoffRadius n) / y)^2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using hs
  calc
    _ ≤ ((derivativeConstant / cutoffRadius n) / y)^2 * Complex.normSq (f y) :=
      mul_le_mul_of_nonneg_right hsq (Complex.normSq_nonneg _)
    _ = _ := by field_simp [hy.ne']; ring

theorem logHeightCutoff_error_rate_tendsto :
    Tendsto (fun n : ℕ => (derivativeConstant / cutoffRadius n)^2) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => derivativeConstant / cutoffRadius n) atTop (𝓝 0) := by
    simpa only [cutoffRadius, div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_const_nhds (x := derivativeConstant)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hlim.pow 2

end
end ImbalancedChen.Part3.PositiveZeroModeLogHeightCutoff20261026b
