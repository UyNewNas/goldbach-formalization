import ImbalancedChen.Part3RadialClosedHilbertFormRiesz
import ImbalancedChen.Part3GenericHilbertAdjointSquare
import ImbalancedChen.Part3GenericFriedrichsOperator
import ImbalancedChen.Part3GenericWeakFriedrichsAssociation
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual radial energy embedding at kappa=1 constructs R=J J*, hence
a genuine positive self-adjoint injective contraction with dense range.
The map J is proved a contraction using the zeroth PiLp2 coordinate of
the real radial energy completion. The native unbounded operator is
R^{-1}-I. Its exact native graph, self-adjointness, dense domain,
closedness and nonnegativity follow from the proved generic Hilbert
inverse-graph theorems instantiated at these actual radial objects.

The actual native graph is also identified with the literal weak radial
derivative/exponential-energy equation, with an actual form-domain lift.
No whole-upper-half-plane space or assumed resolvent is substituted.
-/

namespace ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a

noncomputable section
open Set
open ImbalancedChen.Part3.GenericHilbertAdjointSquare20261025a
open ImbalancedChen.Part3.GenericFriedrichsOperator20261025a
open ImbalancedChen.Part3.GenericWeakFriedrichsAssociation20261025a

def radialUnitShiftResolvent : RadialL2 →L[ℂ] RadialL2 :=
  radialShiftedVariationalInverse 1

theorem radialPhysicalEmbedding_one_opNorm_le_one : ‖radialPhysicalEmbedding 1‖ ≤ 1 := by
  apply (radialPhysicalEmbedding 1).opNorm_le_bound zero_le_one
  intro u
  change ‖((1 : ℝ)⁻¹ : ℂ) • (u : RadialEnergyHilbert) 0‖ ≤ 1 * ‖u‖
  simpa using PiLp.norm_apply_le (u : RadialEnergyHilbert) (0 : Fin 3)

theorem radialUnitShiftResolvent_eq_actual_adjointSquare :
    radialUnitShiftResolvent = adjointSquare (radialPhysicalEmbedding 1) := rfl

theorem radialUnitShiftResolvent_positive : radialUnitShiftResolvent.IsPositive :=
  adjointSquare_positive (radialPhysicalEmbedding 1)

theorem radialUnitShiftResolvent_selfAdjoint : IsSelfAdjoint radialUnitShiftResolvent :=
  adjointSquare_selfAdjoint (radialPhysicalEmbedding 1)

theorem radialUnitShiftResolvent_opNorm_le_one : ‖radialUnitShiftResolvent‖ ≤ 1 :=
  adjointSquare_opNorm_le_one (radialPhysicalEmbedding 1)
    radialPhysicalEmbedding_one_opNorm_le_one

theorem radialUnitShiftResolvent_injective : Function.Injective radialUnitShiftResolvent :=
  adjointSquare_injective (radialPhysicalEmbedding 1)
    (radialPhysicalEmbedding_denseRange 1 (by norm_num))

theorem radialUnitShiftResolvent_denseRange : DenseRange radialUnitShiftResolvent :=
  adjointSquare_denseRange (radialPhysicalEmbedding 1)
    (radialPhysicalEmbedding_denseRange 1 (by norm_num))

theorem radialUnitShiftResolvent_firm (F : RadialL2) :
    ‖radialUnitShiftResolvent F‖ ^ 2 ≤
      (inner ℂ F (radialUnitShiftResolvent F)).re :=
  adjointSquare_firm (radialPhysicalEmbedding 1)
    radialPhysicalEmbedding_one_opNorm_le_one F

def actualRadialFriedrichs : RadialL2 →ₗ.[ℂ] RadialL2 := friedrichsR radialUnitShiftResolvent

theorem actualRadialFriedrichs_graph_iff (u v : RadialL2) :
    (u, v) ∈ actualRadialFriedrichs.graph ↔ radialUnitShiftResolvent (u + v) = u :=
  friedrichsR_mem_graph_iff radialUnitShiftResolvent radialUnitShiftResolvent_injective

theorem actualRadialFriedrichs_domain :
    actualRadialFriedrichs.domain = radialUnitShiftResolvent.range :=
  friedrichsR_domain radialUnitShiftResolvent

theorem actualRadialFriedrichs_isSelfAdjoint : IsSelfAdjoint actualRadialFriedrichs :=
  friedrichsR_isSelfAdjoint radialUnitShiftResolvent
    radialUnitShiftResolvent_selfAdjoint radialUnitShiftResolvent_injective

theorem actualRadialFriedrichs_isClosed : actualRadialFriedrichs.IsClosed :=
  friedrichsR_isClosed radialUnitShiftResolvent radialUnitShiftResolvent_injective

theorem actualRadialFriedrichs_dense_domain :
    Dense (actualRadialFriedrichs.domain : Set RadialL2) :=
  friedrichsR_dense_domain radialUnitShiftResolvent
    radialUnitShiftResolvent_selfAdjoint radialUnitShiftResolvent_injective

theorem actualRadialFriedrichs_nonneg (u : actualRadialFriedrichs.domain) :
    0 ≤ (inner ℂ (u : RadialL2) (actualRadialFriedrichs u)).re :=
  friedrichsR_nonneg radialUnitShiftResolvent radialUnitShiftResolvent_injective
    radialUnitShiftResolvent_firm u

theorem actualRadialFriedrichs_resolvent_pair (F : RadialL2) :
    (radialUnitShiftResolvent F, F - radialUnitShiftResolvent F) ∈
      actualRadialFriedrichs.graph :=
  friedrichsR_resolvent_pair radialUnitShiftResolvent radialUnitShiftResolvent_injective F

/-- This is the literal derivative/exp weak equation on the actual
completed radial form domain, with no shifted physical term remaining. -/
theorem actualRadialFriedrichs_graph_iff_weak_radial_energy (u v : RadialL2) :
    (u, v) ∈ actualRadialFriedrichs.graph ↔
      ∃ e : radialClosedEnergyDomain 1, radialPhysicalEmbedding 1 e = u ∧
        ∀ d : radialClosedEnergyDomain 1,
          inner ℂ (radialClosedDerivative 1 d) (radialClosedDerivative 1 e) +
            inner ℂ (radialClosedExponential 1 d) (radialClosedExponential 1 e) =
              inner ℂ (radialPhysicalEmbedding 1 d) v := by
  rw [actualRadialFriedrichs_graph_iff,
    ← weakEnergyRelation_iff_adjointSquare (radialPhysicalEmbedding 1) u v]
  constructor
  · rintro ⟨e, he, hweak⟩
    refine ⟨e, he, ?_⟩
    intro d
    have h := hweak d
    rw [radialClosedEnergy_inner 1 (by norm_num), he, inner_add_right] at h
    norm_num at h
    linear_combination h
  · rintro ⟨e, he, hweak⟩
    refine ⟨e, he, ?_⟩
    intro d
    rw [radialClosedEnergy_inner 1 (by norm_num), he, inner_add_right]
    norm_num
    linear_combination hweak d

end
end ImbalancedChen.Part3.RadialSchrodingerL2Form20261025a
