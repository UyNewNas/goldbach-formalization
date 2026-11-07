import ImbalancedChen.Part3GammaActualQuotientCutoffMultiplier
import ImbalancedChen.Part3GammaOriginalCutoffCoreEnergyExact

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The proved uniform original-core cutoff energy bound extends the ACTUAL
modular cutoff to every vector in the EXISTING energy completion. Dense
core continuity identifies its physical projection with literal actual
quotient cutoff multiplication. It consequently preserves the existing
physical form domain, without inserting an arbitrary adjoint vector there.
-/

namespace ImbalancedChen.Part3.GammaActualClosedFormCutoffMultiplier20261026b

noncomputable section
open Set Filter MeasureTheory UniformSpace
open scoped Topology UpperHalfPlane
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a Gamma0PhysicalClosedDirichletForm20261025a
open GammaSmoothCoreMultiplierEnergyLift20261026b GammaActualCutoffCoreUniformEnergy20261026b
open GammaActualQuotientCutoffMultiplier20261026b GammaOriginalCutoffCoreEnergyExact20261026b
open ActualCuspStripCutoff20261025a

def actualCutoffEnergyBound : ℝ := Real.sqrt (2+2*cutoffEnergyConstant)

theorem actualCutoffEnergyBound_nonneg : 0 ≤ actualCutoffEnergyBound := Real.sqrt_nonneg _

/-- Fixed-scale cutoff on the existing actual completed form. All bounds
needed by this extension have been proved for the original core. -/
def actualClosedFormCutoff (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    EnergyCompletion N →L[ℂ] EnergyCompletion N :=
  (actualCutoffCoreEnergy N Y (lt_trans (by norm_num) hY)).extendOfNorm
    (coreEmbedding N).toLinearMap

theorem actualClosedFormCutoff_core (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    (u : EnergyCore N) :
    actualClosedFormCutoff N Y hY (coreEmbedding N u) =
      actualCutoffCoreEnergy N Y (lt_trans (by norm_num) hY) u := by
  exact LinearMap.extendOfNorm_eq (coreEmbedding_denseRange N)
    ⟨actualCutoffEnergyBound,actualCutoffCoreEnergy_uniform_bound N Y hY⟩ u

theorem actualClosedFormCutoff_norm_le (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    (e : EnergyCompletion N) :
    ‖actualClosedFormCutoff N Y hY e‖ ≤ actualCutoffEnergyBound*‖e‖ := by
  exact LinearMap.norm_extendOfNorm_apply_le
    (f := actualCutoffCoreEnergy N Y (lt_trans (by norm_num) hY))
    (e := (coreEmbedding N).toLinearMap) (coreEmbedding_denseRange N)
    actualCutoffEnergyBound (actualCutoffCoreEnergy_uniform_bound N Y hY) e

theorem actualClosedFormCutoff_opNorm_le (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    ‖actualClosedFormCutoff N Y hY‖ ≤ actualCutoffEnergyBound :=
  (actualClosedFormCutoff N Y hY).opNorm_le_bound actualCutoffEnergyBound_nonneg
    (actualClosedFormCutoff_norm_le N Y hY)

/-- The abstract extension is the original physical cutoff product on
ALL actual form vectors, proved through the genuine dense core. -/
theorem actualClosedFormCutoff_physical (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    (e : EnergyCompletion N) :
    physicalProjection N (actualClosedFormCutoff N Y hY e) =
      actualQuotientCutoffMultiplier N Y hY (physicalProjection N e) := by
  refine Completion.induction_on e ?_ ?_
  · exact isClosed_eq
      ((physicalProjection N).continuous.comp (actualClosedFormCutoff N Y hY).continuous)
      ((actualQuotientCutoffMultiplier N Y hY).continuous.comp (physicalProjection N).continuous)
  · intro u
    rw [actualClosedFormCutoff_core,physicalProjection_core]
    apply Lp.ext
    exact (coreMultiplierEnergyLift_physical_ae N u _
      (GammaSmoothMultiplierLegalTests20261026a.actualCutoff_isGammaInvariant N Y)
      (GammaSmoothMultiplierLegalTests20261026a.actualCutoff_cinfty Y (lt_trans (by norm_num) hY))).trans
      (actualQuotientCutoffMultiplier_coe_ae N Y hY (physicalCore N u)).symm

/-- The same physical-domain submodule, with its original unique energy
lift; this is not a second Sobolev or operator-domain surrogate. -/
def actualFormCutoffPoint (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    actualEnergyFormDomain N →ₗ[ℂ] actualEnergyFormDomain N :=
  (actualEnergyLift N).symm.toLinearMap.comp
    ((actualClosedFormCutoff N Y hY).toLinearMap.comp (actualEnergyLift N).toLinearMap)

theorem actualFormCutoffPoint_energyLift (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    (u : actualEnergyFormDomain N) :
    actualEnergyLift N (actualFormCutoffPoint N Y hY u) =
      actualClosedFormCutoff N Y hY (actualEnergyLift N u) :=
  (actualEnergyLift N).apply_symm_apply _

theorem actualFormCutoffPoint_physical (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    (u : actualEnergyFormDomain N) :
    (actualFormCutoffPoint N Y hY u : QuotientL2 N) =
      actualQuotientCutoffMultiplier N Y hY (u : QuotientL2 N) := by
  change physicalProjection N (actualClosedFormCutoff N Y hY (actualEnergyLift N u)) = _
  rw [actualClosedFormCutoff_physical,actualEnergyLift_projection]

/-- Genuine form-domain multiplier membership for every existing form
vector, without any boundedness or smoothness premise on that vector. -/
theorem actualQuotientCutoffMultiplier_mem_formDomain
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (u : actualEnergyFormDomain N) :
    actualQuotientCutoffMultiplier N Y hY (u : QuotientL2 N) ∈ actualEnergyFormDomain N := by
  rw [← actualFormCutoffPoint_physical N Y hY u]
  exact (actualFormCutoffPoint N Y hY u).property

end
end ImbalancedChen.Part3.GammaActualClosedFormCutoffMultiplier20261026b
