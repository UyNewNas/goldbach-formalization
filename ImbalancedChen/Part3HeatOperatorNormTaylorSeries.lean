import ImbalancedChen.Part3GenericHeatAllPowersCalculus
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Genuine operator-norm Taylor expansion in positive heat time. Internally
proved factorial heat bounds dominate the actual C-spectrum series by a
geometric series. The true exponential series identifies every evaluation,
including the zero endpoint. Continuous linear CFC transports the actual
Banach-space HasSum to operator norm. No Taylor, analyticity or uniform
high-frequency derivative premise occurs.
-/

namespace ImbalancedChen.Part3.HeatOperatorNormTaylorSeries20261025a
noncomputable section
open Set Filter Topology
open ImbalancedChen.Part3.GenericPositiveResolventHeat20261025a
open ImbalancedChen.Part3.GenericHeatAllPowersCalculus20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (D : ResolventData H)

def timeTaylorScalarTerm (s h : ℝ) (n : ℕ) : C(Spectrum D, ℝ) :=
  ((-h) ^ n / (n.factorial : ℝ)) • heatPowerScalar D s n

theorem timeTaylorScalarTerm_norm_le {s : ℝ} (hs : 0 < s) (h : ℝ) (n : ℕ) :
    ‖timeTaylorScalarTerm D s h n‖ ≤ (|h| / s) ^ n := by
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hφ : ‖heatPowerScalar D s n‖ ≤ (n.factorial : ℝ) / s ^ n := by
    apply (ContinuousMap.norm_le _ (div_nonneg (Nat.cast_nonneg _) (pow_nonneg hs.le n))).2
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (heatPowerScalar_nonneg_le D hs n t).1]
    exact (heatPowerScalar_nonneg_le D hs n t).2
  have hc : ‖(-h) ^ n / (n.factorial : ℝ)‖ = |h| ^ n / (n.factorial : ℝ) := by
    simp only [norm_div, norm_pow, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg n.factorial)]
  calc
    _ = (|h| ^ n / (n.factorial : ℝ)) * ‖heatPowerScalar D s n‖ := by
      rw [timeTaylorScalarTerm, norm_smul, hc]
    _ ≤ (|h| ^ n / (n.factorial : ℝ)) * ((n.factorial : ℝ) / s ^ n) :=
      mul_le_mul_of_nonneg_left hφ (div_nonneg (pow_nonneg (abs_nonneg h) n) hfac.le)
    _ = (|h| / s) ^ n := by
      rw [div_pow]
      field_simp [hs.ne', hfac.ne']
      <;> ring

theorem timeTaylorScalarTerm_summable {s h : ℝ} (hs : 0 < s) (hh : |h| < s / 2) :
    Summable (timeTaylorScalarTerm D s h) := by
  have hr0 : 0 ≤ |h| / s := div_nonneg (abs_nonneg h) hs.le
  have hr1 : |h| / s < 1 := by
    apply (div_lt_one₀ hs).2
    linarith
  exact (summable_geometric_of_lt_one hr0 hr1).of_norm_bounded
    (fun n => timeTaylorScalarTerm_norm_le D hs h n)

theorem hasSum_timeTaylorScalar_eval {s h : ℝ} (hs : 0 < s) (hh : |h| < s / 2)
    (t : Spectrum D) :
    HasSum (fun n : ℕ => timeTaylorScalarTerm D s h n t) (heatScalar D (s + h) t) := by
  have hsh : 0 < s + h := by linarith [neg_abs_le h]
  change HasSum (fun n : ℕ => ((-h) ^ n / (n.factorial : ℝ)) * heatPowerScalar D s n t)
    (heatScalar D (s + h) t)
  by_cases ht : (t : ℝ) = 0
  · simpa only [heatPowerScalar_zero D s _ ht, mul_zero, heatScalar_of_pos D hsh,
      positiveHeatScalar_zero D (s + h) ht] using
      (hasSum_zero : HasSum (fun _n : ℕ => (0 : ℝ)) 0)
  · have htp : 0 < (t : ℝ) := lt_of_le_of_ne
      (spectrum_coordinate_mem_unitInterval D t).1 (Ne.symm ht)
    have he : HasSum (fun n : ℕ => (-h * spectralLambda D t) ^ n / (n.factorial : ℝ))
        (Real.exp (-h * spectralLambda D t)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp _
    have hsum := he.mul_right (heatScalar D s t)
    convert hsum using 1
    · ext n
      rw [heatPowerScalar_apply D hs n htp, mul_pow]
      ring
    · rw [heatScalar_apply_of_pos D hsh htp, heatScalar_apply_of_pos D hs htp,
        ← Real.exp_add]
      congr 1
      ring

/-- Evaluation detects equality of the actual Banach-space sum. This is
an actual HasSum in the continuous-function norm, not pointwise convergence
masquerading as operator-norm convergence. -/
theorem hasSum_timeTaylorScalar {s h : ℝ} (hs : 0 < s) (hh : |h| < s / 2) :
    HasSum (timeTaylorScalarTerm D s h) (heatScalar D (s + h)) := by
  have hsummable := timeTaylorScalarTerm_summable D hs hh
  have heq : (∑' n : ℕ, timeTaylorScalarTerm D s h n) = heatScalar D (s + h) := by
    ext t
    have hev := hsummable.hasSum.mapL (ContinuousMap.evalCLM ℝ t)
    exact hev.unique (hasSum_timeTaylorScalar_eval D hs hh t)
  exact heq ▸ hsummable.hasSum

/-- Exact genuine heat time Taylor series in the Banach operator norm.
The coefficients are the actual lambda^n heat CFC operators. -/
theorem hasSum_heatOperator_timeTaylor {s h : ℝ} (hs : 0 < s) (hh : |h| < s / 2) :
    HasSum (fun n : ℕ => ((-h) ^ n / (n.factorial : ℝ)) • heatPowerOperator D s n)
      (heatOperator D (s + h)) := by
  have hsum := (hasSum_timeTaylorScalar D hs hh).mapL (cfcL D.selfAdjoint)
  change HasSum (fun n : ℕ => cfcMap D (timeTaylorScalarTerm D s h n))
    (cfcMap D (heatScalar D (s + h))) at hsum
  simpa only [timeTaylorScalarTerm, map_smul, heatPowerOperator, heatOperator] using hsum

end
end ImbalancedChen.Part3.HeatOperatorNormTaylorSeries20261025a
