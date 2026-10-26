import ImbalancedChen.Part3Gamma0CompletedFormFixedCoreRellich
import ImbalancedChen.Part3Gamma0ActualWeakRieszResolvent
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! SOURCE_ONLY / UNCOMPILED / zero formal credit.
The actual fixed quotient-core inclusion J_Y is the previously constructed
literal indicator restriction composed with the original J. Actual local
form-ball total boundedness proves J_Y compact. The truncated actual
resolvent is literally J_Y J*, and is therefore compact. No all-cusp
tail, global compactness, or spectral discreteness is assumed. -/

namespace ImbalancedChen.Part3.Gamma0FixedCoreCompactOperator20261026b
noncomputable section
open Set MeasureTheory Metric
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0CompletedFormFixedCoreRellich20261026b
open GenericHilbertAdjointSquare20261025a

theorem fixedCoreInclusion_opNorm_le_one (N : ℕ) [NeZero N] (Y : ℝ) :
    ‖completedCoreRestriction N Y‖ ≤ 1 := by
  apply (completedCoreRestriction N Y).opNorm_le_bound (by norm_num)
  intro e
  simpa only [one_mul] using completedCoreRestriction_norm_le N Y e

/-- Compactness is derived from the actual fixed-core Rellich endpoint
on the ORIGINAL completed form's closed unit ball. -/
theorem actual_fixedCoreInclusion_isCompactOperator (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) : IsCompactOperator (completedCoreRestriction N Y) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    (completedCoreRestriction N Y).toLinearMap (by norm_num : (0 : ℝ) < 1)).mpr
  have he : closedBall (0 : EnergyCompletion N) 1 = {e : EnergyCompletion N | ‖e‖^2 ≤ 1} := by
    ext e
    simp only [mem_closedBall,dist_zero_right,mem_setOf_eq]
    constructor <;> intro h <;> nlinarith [norm_nonneg e]
  simpa only [he] using actual_completed_form_fixed_core_compact_closure N Y hY 1 (by norm_num)

/-- The actual physical bounded resolvent, cut off on the ACTUAL quotient
core. This is an operator on canonical Gamma0 quotient L2. -/
def actualTruncatedResolvent (N : ℕ) [NeZero N] (Y : ℝ) : QuotientL2 N →L[ℂ] QuotientL2 N :=
  (quotientCoreRestrictionCLM N Y).comp (actualGammaResolvent N)

theorem actualTruncatedResolvent_eq_JY_Jadjoint (N : ℕ) [NeZero N] (Y : ℝ) :
    actualTruncatedResolvent N Y = (completedCoreRestriction N Y).comp (physicalProjection N).adjoint := by
  ext f
  rfl

theorem actualTruncatedResolvent_isCompactOperator (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) : IsCompactOperator (actualTruncatedResolvent N Y) := by
  rw [actualTruncatedResolvent_eq_JY_Jadjoint]
  exact (actual_fixedCoreInclusion_isCompactOperator N Y hY).comp_clm (physicalProjection N).adjoint

theorem actualTruncatedResolvent_opNorm_le_one (N : ℕ) [NeZero N] (Y : ℝ) :
    ‖actualTruncatedResolvent N Y‖ ≤ 1 := by
  rw [actualTruncatedResolvent_eq_JY_Jadjoint]
  have hJ : ‖(physicalProjection N).adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact physicalProjection_opNorm_le_one N
  exact ((completedCoreRestriction N Y).opNorm_comp_le (physicalProjection N).adjoint).trans
    (by
      calc
        _ ≤ 1 * 1 := mul_le_mul (fixedCoreInclusion_opNorm_le_one N Y) hJ
          (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num)

end
end ImbalancedChen.Part3.Gamma0FixedCoreCompactOperator20261026b
