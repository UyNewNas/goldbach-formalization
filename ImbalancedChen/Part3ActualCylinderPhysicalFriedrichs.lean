import ImbalancedChen.Part3ActualCylinderClosedDirichletParseval
import ImbalancedChen.Part3GenericFriedrichsOperator
import ImbalancedChen.Part3GenericWeakFriedrichsAssociation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The actual Friedrichs operator on the entire zero-horizontal-mean
cylinder. Its input is the genuine closed physical gradient core from
Part3ActualCylinderClosedDirichletParseval. The bounded resolvent is the
native adjoint square of that domain's physical value embedding. Its
inverse minus identity is a genuine native unbounded self-adjoint closed
nonnegative operator with dense actual domain. Its exact graph is proved
equivalent to testing the literal closed physical Dirichlet form against
the entire actual energy domain.

No operator graph, form identity, global variational inverse, or KL energy
assertion is an input. This is the whole cylinder and contains no boundary
condition on a truncated cusp and no Gamma quotient assertion.
-/

namespace ImbalancedChen.Part3.ActualCylinderPhysicalFriedrichs20261026b
noncomputable section
open Set
open ActualZeroMeanCylinderFourierUnitary20261026a
open ActualCylinderClosedEnergyHilbertSum20261026b
open ActualCylinderClosedDirichletParseval20261026b
open GenericHilbertAdjointSquare20261025a
open GenericFriedrichsOperator20261025a
open GenericWeakFriedrichsAssociation20261025a

theorem cylinderClosedValue_opNorm_le_one : ‖cylinderClosedValue‖ ≤ 1 := by
  apply cylinderClosedValue.opNorm_le_bound zero_le_one
  intro e
  simpa only [one_mul] using cylinderClosedValue_norm_le e

def actualCylinderResolvent : zeroMeanCylinder →L[ℂ] zeroMeanCylinder :=
  adjointSquare cylinderClosedValue

theorem actualCylinderResolvent_positive : actualCylinderResolvent.IsPositive :=
  adjointSquare_positive cylinderClosedValue

theorem actualCylinderResolvent_selfAdjoint : IsSelfAdjoint actualCylinderResolvent :=
  adjointSquare_selfAdjoint cylinderClosedValue

theorem actualCylinderResolvent_opNorm_le_one : ‖actualCylinderResolvent‖ ≤ 1 :=
  adjointSquare_opNorm_le_one cylinderClosedValue cylinderClosedValue_opNorm_le_one

theorem actualCylinderResolvent_injective : Function.Injective actualCylinderResolvent :=
  adjointSquare_injective cylinderClosedValue cylinderClosedValue_denseRange

theorem actualCylinderResolvent_denseRange : DenseRange actualCylinderResolvent :=
  adjointSquare_denseRange cylinderClosedValue cylinderClosedValue_denseRange

theorem actualCylinderResolvent_firm (f : zeroMeanCylinder) :
    ‖actualCylinderResolvent f‖ ^ 2 ≤ (inner ℂ f (actualCylinderResolvent f)).re :=
  adjointSquare_firm cylinderClosedValue cylinderClosedValue_opNorm_le_one f

def actualCylinderFriedrichs : zeroMeanCylinder →ₗ.[ℂ] zeroMeanCylinder :=
  friedrichsR actualCylinderResolvent

theorem actualCylinderFriedrichs_domain :
    actualCylinderFriedrichs.domain = actualCylinderResolvent.range :=
  friedrichsR_domain actualCylinderResolvent

theorem actualCylinderFriedrichs_selfAdjoint : IsSelfAdjoint actualCylinderFriedrichs :=
  friedrichsR_isSelfAdjoint actualCylinderResolvent actualCylinderResolvent_selfAdjoint
    actualCylinderResolvent_injective

theorem actualCylinderFriedrichs_isClosed : actualCylinderFriedrichs.IsClosed :=
  friedrichsR_isClosed actualCylinderResolvent actualCylinderResolvent_injective

theorem actualCylinderFriedrichs_dense_domain :
    Dense (actualCylinderFriedrichs.domain : Set zeroMeanCylinder) :=
  friedrichsR_dense_domain actualCylinderResolvent actualCylinderResolvent_selfAdjoint
    actualCylinderResolvent_injective

theorem actualCylinderFriedrichs_nonneg (u : actualCylinderFriedrichs.domain) :
    0 ≤ (inner ℂ (u : zeroMeanCylinder) (actualCylinderFriedrichs u)).re :=
  friedrichsR_nonneg actualCylinderResolvent actualCylinderResolvent_injective
    actualCylinderResolvent_firm u

theorem actualCylinderFriedrichs_graph_iff_resolvent (u v : zeroMeanCylinder) :
    (u, v) ∈ actualCylinderFriedrichs.graph ↔ actualCylinderResolvent (u + v) = u :=
  friedrichsR_mem_graph_iff actualCylinderResolvent actualCylinderResolvent_injective

/-- The true native graph is the actual physical weak Dirichlet graph,
including a lift in the closure of genuine compact finite-mode gradients. -/
theorem actualCylinderFriedrichs_graph_iff_closedDirichlet (u v : zeroMeanCylinder) :
    (u, v) ∈ actualCylinderFriedrichs.graph ↔
      ∃ e : cylinderClosedEnergyDomain, cylinderClosedValue e = u ∧
        ∀ d : cylinderClosedEnergyDomain,
          closedDirichletForm d e = inner ℂ (cylinderClosedValue d) v := by
  rw [actualCylinderFriedrichs_graph_iff_resolvent,
    ← weakEnergyRelation_iff_adjointSquare cylinderClosedValue u v]
  constructor
  · rintro ⟨e, he, hweak⟩
    refine ⟨e, he, (closedDirichletForm_weak_iff_shifted_pairing e v).mpr ?_⟩
    simpa only [he] using hweak
  · rintro ⟨e, he, hweak⟩
    refine ⟨e, he, ?_⟩
    have h := (closedDirichletForm_weak_iff_shifted_pairing e v).mp hweak
    simpa only [he] using h

theorem actualCylinderFriedrichs_resolvent_pair (f : zeroMeanCylinder) :
    (actualCylinderResolvent f, f - actualCylinderResolvent f) ∈
      actualCylinderFriedrichs.graph :=
  friedrichsR_resolvent_pair actualCylinderResolvent actualCylinderResolvent_injective f

theorem actualCylinderFriedrichs_resolvent_action (f : zeroMeanCylinder) :
    actualCylinderFriedrichs (resolventPoint actualCylinderResolvent f) =
      f - actualCylinderResolvent f :=
  friedrichsR_apply_image actualCylinderResolvent actualCylinderResolvent_injective f

end
end ImbalancedChen.Part3.ActualCylinderPhysicalFriedrichs20261026b
