import ImbalancedChen.Part3ActualModularCutoffMaassBudget
import ImbalancedChen.Part3ActualModularCutoffCompactSupport
import ImbalancedChen.Part3Gamma0ActualConstantMode
import Mathlib.Analysis.SpecificLimits.Basic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Canonical actual quotient L2 objects for the genuine full modular cutoff
on Gamma0(N), and its actual native Maass output. The original tail and
Delta budgets become Hilbert norm estimates and a fixed explicit sequence
Y_n=n+2 converging in the actual graph coordinates to (constant one,0).
This file asserts no core or form membership of the cutoffs.
-/
namespace ImbalancedChen.Part3.GammaConstantCutoffL220261026a

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Gamma0QuotientCellPushforward20261025a
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualConstantMode20261025a
open ActualModularSmoothCutoffL2Tail20261025a
open ActualModularCutoffMaassBudget20261025a
open ActualCuspStripCutoffGraph20261025a

/-- Convert a real square-mass bound into genuine L2 membership. -/
theorem memLp_two_of_square_mass_lt_top {X : Type*} [MeasurableSpace X]
    {mu : Measure X} {f : X → ℂ} (hf : AEStronglyMeasurable f mu)
    (hfin : (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂mu) < ∞) : MemLp f 2 mu := by
  apply (memLp_two_iff_integrable_sq_norm hf).mpr
  refine ⟨hf.norm.pow_const 2, ?_⟩
  change (∫⁻ x, ‖‖f x‖ ^ 2‖ₑ ∂mu) < ∞
  simpa only [Real.enorm_eq_ofReal (sq_nonneg _)] using hfin

/-- Exact Hilbert norm squared in the same actual quotient measure. -/
theorem lp_norm_sq_eq_square_mass {X : Type*} [MeasurableSpace X]
    {mu : Measure X} (u : Lp ℂ 2 mu) :
    ‖u‖ ^ 2 = (∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2) ∂mu).toReal := by
  have hh := congrArg Complex.re (L2.integral_inner_eq_sq_eLpNorm u)
  rw [← L2.inner_def, ← InnerProductSpace.norm_sq_eq_re_inner] at hh
  calc
    _ = (∫⁻ x, (‖u x‖₊ : ℝ≥0∞) ^ (2 : ℝ) ∂mu).toReal := by
      simpa only [Complex.ofReal_re] using hh
    _ = _ := by
      congr 1
      apply lintegral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      rw [ENNReal.rpow_natCast, ENNReal.ofReal_pow (norm_nonneg _) 2,
        ofReal_norm]

local instance quotientFiniteMeasure (N : ℕ) [NeZero N] :
    IsFiniteMeasure (carrierPushforward N) := ⟨carrierPushforward_finite N⟩

theorem cutoff_memLp (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    MemLp (fun q => (quotientCutoff N Y q : ℂ)) 2 (carrierPushforward N) := by
  apply MemLp.of_bound
    ((Complex.measurable_ofReal.comp (quotientCutoff_measurable N Y
      (lt_trans (by norm_num) hY))).aestronglyMeasurable) 1
  apply Filter.Eventually.of_forall
  intro q
  have hb := quotientCutoff_bounds N Y hY.le q
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

def cutoffL2 (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) : QuotientL2 N :=
  (cutoff_memLp N Y hY).toLp (fun q => (quotientCutoff N Y q : ℂ))

theorem cutoffL2_ae (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    (cutoffL2 N Y hY : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      (fun q => (quotientCutoff N Y q : ℂ)) := (cutoff_memLp N Y hY).coeFn_toLp

theorem cutoffMaass_memLp (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    MemLp (quotientCutoffMaass N Y (lt_trans (by norm_num) hY)) 2 (carrierPushforward N) := by
  apply memLp_two_of_square_mass_lt_top
    (quotientCutoffMaass_measurable N Y (lt_trans (by norm_num) hY)).aestronglyMeasurable
  exact (quotientCutoffMaass_L2_bound N Y hY).trans_lt (by finiteness)

def cutoffMaassL2 (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) : QuotientL2 N :=
  (cutoffMaass_memLp N Y hY).toLp
    (quotientCutoffMaass N Y (lt_trans (by norm_num) hY))

theorem cutoffMaassL2_ae (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    (cutoffMaassL2 N Y hY : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      quotientCutoffMaass N Y (lt_trans (by norm_num) hY) :=
  (cutoffMaass_memLp N Y hY).coeFn_toLp

/-- Exact conversion of the true original tail budget, with its original
subgroup index, not a new unspecified norm constant. -/
theorem cutoffL2_sub_constant_norm_sq_le (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    ‖cutoffL2 N Y hY - constantL2 N‖ ^ 2 ≤
      ((CongruenceSubgroup.Gamma0 N).index : ℝ) / Y := by
  rw [lp_norm_sq_eq_square_mass]
  have heq : (fun q => ENNReal.ofReal (‖(cutoffL2 N Y hY - constantL2 N) q‖ ^ 2))
      =ᵐ[carrierPushforward N] (fun q => ENNReal.ofReal ((1 - quotientCutoff N Y q)^2)) := by
    filter_upwards [Lp.coeFn_sub (cutoffL2 N Y hY) (constantL2 N),
      cutoffL2_ae N Y hY, constantL2_ae N] with q hs hc h1
    rw [hs, hc, h1]
    have hr : (quotientCutoff N Y q : ℂ) - 1 = ((quotientCutoff N Y q - 1 : ℝ) : ℂ) := by simp
    rw [hr, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    congr 1
    ring
  rw [lintegral_congr_ae heq]
  have h := ENNReal.toReal_mono (by finiteness) (quotientCutoff_L2_error_le N Y hY)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (le_of_lt (one_div_pos.mpr (lt_trans (by norm_num) hY))),
    div_eq_mul_inv, one_div] using h

theorem cutoffMaassL2_norm_sq_le (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    ‖cutoffMaassL2 N Y hY‖ ^ 2 ≤
      cutoffGraphConstant * ((CongruenceSubgroup.Gamma0 N).index : ℝ) / Y := by
  rw [lp_norm_sq_eq_square_mass]
  have heq : (fun q => ENNReal.ofReal (‖cutoffMaassL2 N Y hY q‖ ^ 2))
      =ᵐ[carrierPushforward N] (fun q => ENNReal.ofReal
        (‖quotientCutoffMaass N Y (lt_trans (by norm_num) hY) q‖ ^ 2)) := by
    filter_upwards [cutoffMaassL2_ae N Y hY] with q hq
    rw [hq]
  rw [lintegral_congr_ae heq]
  have h := ENNReal.toReal_mono (by finiteness) (quotientCutoffMaass_L2_bound N Y hY)
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal, cutoffGraphConstant_nonneg,
    (lt_trans (by norm_num) hY).le, div_eq_mul_inv] using h

/-- Fixed explicit heights; all cusp charts and subgroup classes remain
in the pre-existing global cutoff construction. -/
def cutoffHeight (n : ℕ) : ℝ := (n : ℝ) + 2

theorem cutoffHeight_gt_one (n : ℕ) : 1 < cutoffHeight n := by
  unfold cutoffHeight
  positivity

theorem constant_div_height_tendsto (C : ℝ) :
    Tendsto (fun n => C / cutoffHeight n) atTop (𝓝 0) := by
  have hh : Tendsto cutoffHeight atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  simpa only [div_eq_mul_inv, mul_zero] using
    (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hh))

/-- The squared estimate alone supplies a true Hilbert-space limit. -/
theorem tendsto_of_norm_sq_le_div_height {E : Type*} [NormedAddCommGroup E]
    (u : ℕ → E) (v : E) (C : ℝ)
    (hb : ∀ n, ‖u n - v‖ ^ 2 ≤ C / cutoffHeight n) : Tendsto u atTop (𝓝 v) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  have hs := (constant_div_height_tendsto C).eventually (Iio_mem_nhds (sq_pos_of_pos heps))
  obtain ⟨K, hK⟩ := eventually_atTop.mp hs
  refine ⟨K, ?_⟩
  intro n hn
  rw [dist_eq_norm]
  have hsmall := (hb n).trans_lt (hK n hn)
  nlinarith [norm_nonneg (u n - v)]

theorem cutoffL2_tendsto_constant (N : ℕ) [NeZero N] :
    Tendsto (fun n => cutoffL2 N (cutoffHeight n) (cutoffHeight_gt_one n))
      atTop (𝓝 (constantL2 N)) :=
  tendsto_of_norm_sq_le_div_height _ _ _ (fun n =>
    cutoffL2_sub_constant_norm_sq_le N _ _)

theorem cutoffMaassL2_tendsto_zero (N : ℕ) [NeZero N] :
    Tendsto (fun n => cutoffMaassL2 N (cutoffHeight n) (cutoffHeight_gt_one n)) atTop (𝓝 0) := by
  apply tendsto_of_norm_sq_le_div_height _ _ (cutoffGraphConstant *
    ((CongruenceSubgroup.Gamma0 N).index : ℝ))
  intro n
  simpa only [sub_zero] using cutoffMaassL2_norm_sq_le N (cutoffHeight n) (cutoffHeight_gt_one n)

end
end ImbalancedChen.Part3.GammaConstantCutoffL220261026a

