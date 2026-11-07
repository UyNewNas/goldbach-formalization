import ImbalancedChen.Part3RadialClosedHilbertFormRiesz
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

A concrete symmetric smooth exhaustion of the whole real line. Its
cutoff derivative has the actual bound C/(n+1), where C is constructed
from the fixed bump's compact derivative support. Both real ends are
cut off. The L2 multiplier convergence is proved by dominated convergence
against the input's own squared norm, not assumed as an approximation.
-/
namespace ImbalancedChen.Part3.RadialWeightedCutoffDensity20261025a

noncomputable section
open MeasureTheory Filter Set
open RadialSchrodingerL2Form20261025a

def baseBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def cutoffRadius (n : ℕ) : ℝ := (n : ℝ) + 1

theorem cutoffRadius_pos (n : ℕ) : 0 < cutoffRadius n := by
  dsimp [cutoffRadius]
  positivity

def cutoff (n : ℕ) (r : ℝ) : ℝ := baseBump (r / cutoffRadius n)

theorem cutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (cutoff n) :=
  baseBump.contDiff.comp (contDiff_id.div_const _)

theorem cutoff_range (n : ℕ) (r : ℝ) : 0 ≤ cutoff n r ∧ cutoff n r ≤ 1 :=
  ⟨baseBump.nonneg, baseBump.le_one⟩

theorem cutoff_eq_one (n : ℕ) (r : ℝ) (hr : |r| ≤ cutoffRadius n) :
    cutoff n r = 1 := by
  apply baseBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_div,
    abs_of_pos (cutoffRadius_pos n)]
  exact (div_le_one (cutoffRadius_pos n)).2 hr

theorem cutoff_compact (n : ℕ) : HasCompactSupport (cutoff n) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact
    (Icc (-2 * cutoffRadius n) (2 * cutoffRadius n)))
  intro r hr
  apply baseBump.zero_of_le_dist
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (cutoffRadius_pos n)]
  apply (le_div_iff₀ (cutoffRadius_pos n)).2
  have hnot : ¬(-2 * cutoffRadius n ≤ r ∧ r ≤ 2 * cutoffRadius n) := hr
  have habs := abs_le (a := r) (b := 2 * cutoffRadius n)
  have hlt : 2 * cutoffRadius n < |r| := by
    apply lt_of_not_ge
    intro h
    exact hnot (by simpa only [neg_mul] using habs.mp h)
  exact hlt.le

theorem eventually_cutoff_eq_one (r : ℝ) :
    ∀ᶠ n : ℕ in atTop, cutoff n r = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt |r|
  filter_upwards [eventually_ge_atTop N] with n hn
  apply cutoff_eq_one
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  dsimp [cutoffRadius]
  linarith

theorem tendsto_cutoff (r : ℝ) :
    Tendsto (fun n : ℕ => cutoff n r) atTop (nhds 1) :=
  tendsto_const_nhds.congr' (eventually_cutoff_eq_one r).symm

/-- The bump derivative bound is obtained from its actual compact support. -/
theorem exists_base_derivative_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℝ, ‖deriv (baseBump : ℝ → ℝ) r‖ ≤ C := by
  have hc : Continuous (deriv (baseBump : ℝ → ℝ)) :=
    (contDiff_infty_iff_deriv.mp (baseBump.contDiff : ContDiff ℝ ∞ (baseBump : ℝ → ℝ))).2.continuous
  obtain ⟨C, hC⟩ := baseBump.hasCompactSupport.deriv.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro r
  by_cases hr : r ∈ tsupport (deriv (baseBump : ℝ → ℝ))
  · exact (hC r hr).trans (le_max_right _ _)
  · rw [image_eq_zero_of_notMem_tsupport hr, norm_zero]
    exact (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)

def derivativeConstant : ℝ := Classical.choose exists_base_derivative_bound

theorem derivativeConstant_ge_one : 1 ≤ derivativeConstant :=
  (Classical.choose_spec exists_base_derivative_bound).1

theorem base_derivative_le (r : ℝ) :
    ‖deriv (baseBump : ℝ → ℝ) r‖ ≤ derivativeConstant :=
  (Classical.choose_spec exists_base_derivative_bound).2 r

theorem cutoff_derivative (n : ℕ) (r : ℝ) :
    deriv (cutoff n) r =
      deriv (baseBump : ℝ → ℝ) (r / cutoffRadius n) / cutoffRadius n := by
  have hd := (contDiff_infty_iff_deriv.mp
    (baseBump.contDiff : ContDiff ℝ ∞ (baseBump : ℝ → ℝ))).1
  have hh := (hd (r / cutoffRadius n)).hasDerivAt.comp r
    ((hasDerivAt_id r).div_const (cutoffRadius n))
  simpa only [cutoff, Function.comp_def, div_eq_mul_inv, one_mul] using hh.deriv

/-- Explicit scaling rate; its constant is independent of n and r. -/
theorem cutoff_derivative_bound (n : ℕ) (r : ℝ) :
    ‖deriv (cutoff n) r‖ ≤ derivativeConstant / cutoffRadius n := by
  rw [cutoff_derivative, norm_div,
    show ‖cutoffRadius n‖ = cutoffRadius n from
      Real.norm_of_nonneg (cutoffRadius_pos n).le]
  exact div_le_div_of_nonneg_right (base_derivative_le _) (cutoffRadius_pos n).le

theorem cutoff_derivative_uniform_bound (n : ℕ) (r : ℝ) :
    ‖deriv (cutoff n) r‖ ≤ derivativeConstant := by
  apply (cutoff_derivative_bound n r).trans
  apply (div_le_iff₀ (cutoffRadius_pos n)).2
  have hC : 0 ≤ derivativeConstant := (by norm_num : (0 : ℝ) ≤ 1).trans derivativeConstant_ge_one
  dsimp [cutoffRadius]
  nlinarith [Nat.cast_nonneg (R := ℝ) n]

theorem tendsto_cutoff_derivative (r : ℝ) :
    Tendsto (fun n : ℕ => deriv (cutoff n) r) atTop (nhds 0) := by
  have hrate : Tendsto (fun n : ℕ => derivativeConstant / cutoffRadius n) atTop (nhds 0) := by
    simpa only [cutoffRadius, div_eq_mul_inv, one_mul, mul_zero] using
      (tendsto_const_nhds (x := derivativeConstant)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply tendsto_norm_nhds_zero_iff.mp
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => cutoff_derivative_bound n r) hrate

/-- A direct L2 dominated-convergence helper proved from squared enorms. -/
theorem tendsto_eLpNorm_zero_of_dominated
    (F : ℕ → ℝ → ℂ) (G : ℝ → ℝ) (hG : MemLp G 2 (volume : Measure ℝ))
    (hF : ∀ n, AEStronglyMeasurable (F n) volume)
    (hbound : ∀ n, ∀ r, ‖F n r‖ ≤ ‖G r‖)
    (hlim : ∀ r, Tendsto (fun n => F n r) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (F n) 2 volume) atTop (nhds 0) := by
  have hm (n : ℕ) : AEMeasurable
      (fun r => ‖F n r‖ₑ ^ (2 : ℝ≥0∞).toReal) volume :=
    (hF n).enorm.pow_const _
  have hb (n : ℕ) : (fun r => ‖F n r‖ₑ ^ (2 : ℝ≥0∞).toReal) ≤ᵐ[volume]
      (fun r => ‖G r‖ₑ ^ (2 : ℝ≥0∞).toReal) := by
    apply Filter.Eventually.of_forall
    intro r
    apply ENNReal.rpow_le_rpow _ ENNReal.toReal_nonneg
    exact_mod_cast hbound n r
  have hg : (∫⁻ r : ℝ, ‖G r‖ₑ ^ (2 : ℝ≥0∞).toReal) ≠ ⊤ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      hG.eLpNorm_lt_top).ne
  have hl : ∀ᵐ r ∂(volume : Measure ℝ),
      Tendsto (fun n => ‖F n r‖ₑ ^ (2 : ℝ≥0∞).toReal) atTop (nhds 0) := by
    apply Filter.Eventually.of_forall
    intro r
    simpa using Filter.Tendsto.ennrpow_const (2 : ℝ≥0∞).toReal (hlim r).enorm
  have hi : Tendsto (fun n => ∫⁻ r, ‖F n r‖ₑ ^ (2 : ℝ≥0∞).toReal)
      atTop (nhds 0) := by
    simpa using tendsto_lintegral_of_dominated_convergence'
      (fun r => ‖G r‖ₑ ^ (2 : ℝ≥0∞).toReal) hm hb hg hl
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  convert ENNReal.continuous_rpow_const.continuousAt.tendsto.comp hi using 1
  norm_num

theorem cutoff_error_bound (n : ℕ) (F : ℝ → ℂ) (r : ℝ) :
    ‖cutoff n r • F r - F r‖ ≤ ‖F r‖ := by
  have heq : cutoff n r • F r - F r = (cutoff n r - 1) • F r := by
    rw [sub_smul, one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith [(cutoff_range n r).2])]
  have hc := (cutoff_range n r).1
  nlinarith [norm_nonneg (F r)]

/-- Actual cutoff multiplication tends to the identity on every radial L2 input. -/
theorem cutoff_multiplier_eLpNorm_tendsto (F : ℝ → ℂ)
    (hF : MemLp F 2 (volume : Measure ℝ)) :
    Tendsto (fun n => eLpNorm (fun r => cutoff n r • F r - F r) 2 volume)
      atTop (nhds 0) := by
  apply tendsto_eLpNorm_zero_of_dominated _ (fun r => ‖F r‖) hF.norm
  · intro n
    exact (((cutoff_smooth n).continuous.aestronglyMeasurable.smul
      hF.aestronglyMeasurable).sub hF.aestronglyMeasurable)
  · intro n r
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using cutoff_error_bound n F r
  · intro r
    simpa using ((tendsto_cutoff r).smul (tendsto_const_nhds (x := F r))).sub
      (tendsto_const_nhds (x := F r))

end
end ImbalancedChen.Part3.RadialWeightedCutoffDensity20261025a
