import ImbalancedChen.Part3ActualFriedrichsHeatGenerator

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual heat right-generator graph is exactly the negative actual
Friedrichs graph. The forward derivative was proved by actual scalar-measure
dominated convergence. Conversely the actual bounded resolvent commutes
with every actual heat operator. Applying R to a supplied strong difference
quotient limit and comparing with the already proved derivative at Ru forces
Rv=u-Ru, the literal Friedrichs graph equation. No domain premise is used
in this converse, and no generator-domain identification is assumed.
-/

namespace ImbalancedChen.Part3.ActualFriedrichsHeatGeneratorGraph20261025a

noncomputable section

open Set Filter Topology
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualCompletedEnergyResolvent20261025a
open ImbalancedChen.Part3.ActualResolventScalarMeasure20261025a
open ImbalancedChen.Part3.ActualFriedrichsSelfAdjointOperator20261025a
open ImbalancedChen.Part3.ActualFriedrichsHeatSemigroup20261025a
open ImbalancedChen.Part3.ActualFriedrichsHeatGenerator20261025a

/-- Commutation is proved inside the actual real CFC of the actual R. -/
theorem heatOperator_mul_resolvent (s : ℝ) :
    heatOperator s * actualWeakResolvent = actualWeakResolvent * heatOperator s := by
  calc
    _ = resolventCFC (heatScalar s * spectrumCoordinate) := by
      rw [map_mul, resolventCFC_coordinate]
      rfl
    _ = resolventCFC (spectrumCoordinate * heatScalar s) := by rw [mul_comm]
    _ = _ := by
      rw [map_mul, resolventCFC_coordinate]
      rfl

theorem heatOperator_resolvent_apply (s : ℝ) (u : HyperbolicL2) :
    heatOperator s (actualWeakResolvent u) = actualWeakResolvent (heatOperator s u) :=
  congrArg (fun T : ResolventAlgebra => T u) (heatOperator_mul_resolvent s)

theorem resolvent_heat_difference_quotient (s : ℝ) (u : HyperbolicL2) :
    actualWeakResolvent ((s : ℂ)⁻¹ • (heatOperator s u - u)) =
      (s : ℂ)⁻¹ • (heatOperator s (actualWeakResolvent u) - actualWeakResolvent u) := by
  rw [map_smul, map_sub, ← heatOperator_resolvent_apply]

/-- A strong heat derivative at an arbitrary actual L2 vector forces
membership in the actual Friedrichs domain, with the actual operator value. -/
theorem mem_friedrichsGraph_of_heat_difference_quotient
    {u v : HyperbolicL2}
    (hderiv : Tendsto (fun s : ℝ => (s : ℂ)⁻¹ • (heatOperator s u - u))
      (𝓝[>] 0) (𝓝 (-v))) : (u, v) ∈ friedrichsGraph := by
  have hRlim := (actualWeakResolvent.continuous.tendsto (-v)).comp hderiv
  have hquot : Tendsto
      (fun s : ℝ => (s : ℂ)⁻¹ •
        (heatOperator s (actualWeakResolvent u) - actualWeakResolvent u))
      (𝓝[>] 0) (𝓝 (-actualWeakResolvent v)) := by
    simpa only [Function.comp_def, resolvent_heat_difference_quotient, map_neg] using hRlim
  have hactual := tendsto_heat_difference_quotient_on_friedrichsGraph
    (friedrichs_resolvent_pair u)
  have hvalue : actualWeakResolvent v = u - actualWeakResolvent u :=
    neg_injective (tendsto_nhds_unique hquot hactual)
  apply (mem_friedrichsGraph_iff (u, v)).2
  rw [map_add, hvalue]
  abel

/-- Full actual domain-and-value identification, in both directions. -/
theorem mem_friedrichsGraph_iff_heat_difference_quotient (u v : HyperbolicL2) :
    (u, v) ∈ friedrichsGraph ↔
      Tendsto (fun s : ℝ => (s : ℂ)⁻¹ • (heatOperator s u - u))
        (𝓝[>] 0) (𝓝 (-v)) :=
  ⟨tendsto_heat_difference_quotient_on_friedrichsGraph,
    mem_friedrichsGraph_of_heat_difference_quotient⟩

/-- The genuine strong right-generator graph of the actual heat family. -/
def heatRightGeneratorGraph : Set (HyperbolicL2 × HyperbolicL2) :=
  {p | Tendsto (fun s : ℝ => (s : ℂ)⁻¹ • (heatOperator s p.1 - p.1))
    (𝓝[>] 0) (𝓝 p.2)}

/-- Equality of actual graphs, including domain equality; the negative
sign is the usual heat-generator convention. -/
theorem heatRightGeneratorGraph_eq_negative_friedrichsGraph :
    heatRightGeneratorGraph =
      {p : HyperbolicL2 × HyperbolicL2 | (p.1, -p.2) ∈ friedrichsGraph} := by
  ext p
  simpa only [heatRightGeneratorGraph, mem_setOf_eq, neg_neg] using
    (mem_friedrichsGraph_iff_heat_difference_quotient p.1 (-p.2)).symm

end
end ImbalancedChen.Part3.ActualFriedrichsHeatGeneratorGraph20261025a
