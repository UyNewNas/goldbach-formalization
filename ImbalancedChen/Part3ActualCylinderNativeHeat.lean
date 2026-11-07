import ImbalancedChen.Part3ActualCylinderPhysicalFriedrichs
import ImbalancedChen.Part3GenericHeatStrongContinuity
import ImbalancedChen.Part3GenericHeatPositiveTimeRegularization

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The true native heat family of the actual physical whole-cylinder
Friedrichs operator. It is constructed by the actual energy resolvent's
continuous functional calculus, before any KL multiplier formula is used.
It is a strongly continuous positive self-adjoint contraction semigroup.
Its strong right-generator graph is exactly the negative SAME physical
Friedrichs graph in both directions. Positive time places every actual
L2 input in that operator's genuine native domain with a proved output
bound. No heat or generator-domain statement is assumed.

The form domain is the genuine compact finite-mode gradient closure.
This is a whole-cylinder assertion, with no Gamma quotient or truncated
cusp realization.
-/

namespace ImbalancedChen.Part3.ActualCylinderNativeHeat20261026b
noncomputable section
open Set Filter Topology
open ActualZeroMeanCylinderFourierUnitary20261026a
open ActualCylinderPhysicalFriedrichs20261026b
open GenericPositiveResolventHeat20261025a
open GenericHeatStrongContinuity20261025a
open GenericPositiveResolventHeatGenerator20261025a
open GenericHeatPositiveTimeRegularization20261025a

def actualCylinderResolventData : ResolventData zeroMeanCylinder where
  R := actualCylinderResolvent
  selfAdjoint := actualCylinderResolvent_selfAdjoint
  nonneg := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr actualCylinderResolvent_positive
  norm_le_one := actualCylinderResolvent_opNorm_le_one
  injective := actualCylinderResolvent_injective

def actualCylinderHeat (s : ℝ) : zeroMeanCylinder →L[ℂ] zeroMeanCylinder :=
  heatOperator actualCylinderResolventData s

theorem actualCylinderHeat_zero : actualCylinderHeat 0 = 1 :=
  heatOperator_zero actualCylinderResolventData

theorem actualCylinderHeat_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    actualCylinderHeat (s + t) = actualCylinderHeat s * actualCylinderHeat t :=
  heatOperator_add actualCylinderResolventData hs ht

theorem actualCylinderHeat_selfAdjoint (s : ℝ) : IsSelfAdjoint (actualCylinderHeat s) :=
  heatOperator_selfAdjoint actualCylinderResolventData s

theorem actualCylinderHeat_positive (s : ℝ) : (actualCylinderHeat s).IsPositive :=
  heatOperator_positive actualCylinderResolventData s

theorem actualCylinderHeat_opNorm (s : ℝ) : ‖actualCylinderHeat s‖ ≤ 1 :=
  heatOperator_opNorm_le_one actualCylinderResolventData s

theorem actualCylinderHeat_norm_le (s : ℝ) (f : zeroMeanCylinder) :
    ‖actualCylinderHeat s f‖ ≤ ‖f‖ :=
  heatOperator_norm_le actualCylinderResolventData s f

theorem actualCylinderHeat_strongly_continuous (f : zeroMeanCylinder) :
    ContinuousOn (fun s : ℝ => actualCylinderHeat s f) (Ici (0 : ℝ)) :=
  continuousOn_heatTrajectory_nonnegative actualCylinderResolventData f

theorem actualCylinderHeat_initial (f : zeroMeanCylinder) :
    Tendsto (fun s : ℝ => actualCylinderHeat s f) (𝓝[>] 0) (𝓝 f) :=
  tendsto_heatOperator_at_zero actualCylinderResolventData f

/-- Exact strong generator domain AND value, in both directions. -/
theorem actualCylinderHeat_generator_iff (u v : zeroMeanCylinder) :
    (u, v) ∈ actualCylinderFriedrichs.graph ↔
      Tendsto (fun s : ℝ => (s : ℂ)⁻¹ • (actualCylinderHeat s u - u))
        (𝓝[>] 0) (𝓝 (-v)) :=
  (actualCylinderFriedrichs_graph_iff_resolvent u v).trans
    ((mem_resolventGraph_iff actualCylinderResolventData (u, v)).symm.trans
      (mem_resolventGraph_iff_heat_difference_quotient actualCylinderResolventData u v))

def actualCylinderHeatOutput (s : ℝ) : zeroMeanCylinder →L[ℂ] zeroMeanCylinder :=
  heatGeneratorOperator actualCylinderResolventData s

theorem actualCylinderHeat_positiveTime_graph {s : ℝ} (hs : 0 < s) (f : zeroMeanCylinder) :
    (actualCylinderHeat s f, actualCylinderHeatOutput s f) ∈ actualCylinderFriedrichs.graph :=
  heatOperator_friedrichs_graph actualCylinderResolventData hs f

def actualCylinderHeatDomainPoint (s : ℝ) (hs : 0 < s) (f : zeroMeanCylinder) :
    actualCylinderFriedrichs.domain :=
  heatDomainVector actualCylinderResolventData s hs f

theorem actualCylinderFriedrichs_heat_apply (s : ℝ) (hs : 0 < s) (f : zeroMeanCylinder) :
    actualCylinderFriedrichs (actualCylinderHeatDomainPoint s hs f) =
      actualCylinderHeatOutput s f :=
  friedrichs_heatDomainVector_apply actualCylinderResolventData s hs f

theorem actualCylinderFriedrichs_heat_norm_le (s : ℝ) (hs : 0 < s) (f : zeroMeanCylinder) :
    ‖actualCylinderFriedrichs (actualCylinderHeatDomainPoint s hs f)‖ ≤ ‖f‖ / s :=
  friedrichs_heatDomainVector_norm_le actualCylinderResolventData s hs f

end
end ImbalancedChen.Part3.ActualCylinderNativeHeat20261026b
