import ImbalancedChen.Part3CuspModeNativeClosedForm
import ImbalancedChen.Part3GenericWeakFriedrichsAssociation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The actual physical energy completion has the inherited norm of its three
physical coordinates (f,y*f',a*y*f), with measure dy/y^2. Its coordinate
projection is a contraction. Its native Hilbert adjoint therefore gives
the actual positive self-adjoint contractive resolvent of I+A_phys.

The key equality is proved from the actual physical PiLp inner product:
the abstract shifted-energy weak relation is exactly the already defined
physical weak graph. No radial graph or resolvent equation is a premise.
This supplies the bounded coordinate operator needed for infinite mode sums.
-/

namespace ImbalancedChen.Part3.CuspModePhysicalResolvent20261026b
noncomputable section
open Set
open CuspModeNativeClosedForm20261026a
open WeightedHeightNativeUnitary20261026a
open GenericHilbertAdjointSquare20261025a
open GenericWeakFriedrichsAssociation20261025a

/-- This is the inherited physical energy inner product, rather than
the different radial-coordinate norm under the nonunitary energy shear. -/
theorem physicalClosedEnergy_inner (a : ℝ) (ha : 0 < a)
    (d e : physicalClosedEnergyDomain a ha) :
    inner ℂ d e =
      inner ℂ (physicalClosedEmbedding a ha d) (physicalClosedEmbedding a ha e) +
        physicalClosedForm a ha d e := by
  change inner ℂ (d : PhysicalEnergyHilbert) (e : PhysicalEnergyHilbert) =
    inner ℂ ((d : PhysicalEnergyHilbert) 0) ((e : PhysicalEnergyHilbert) 0) +
      (inner ℂ ((d : PhysicalEnergyHilbert) 1) ((e : PhysicalEnergyHilbert) 1) +
        inner ℂ ((d : PhysicalEnergyHilbert) 2) ((e : PhysicalEnergyHilbert) 2))
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem physicalClosedEmbedding_opNorm_le_one (a : ℝ) (ha : 0 < a) :
    ‖physicalClosedEmbedding a ha‖ ≤ 1 := by
  apply (physicalClosedEmbedding a ha).opNorm_le_bound zero_le_one
  intro e
  change ‖(e : PhysicalEnergyHilbert) 0‖ ≤ 1 * ‖e‖
  simpa using PiLp.norm_apply_le (e : PhysicalEnergyHilbert) (0 : Fin 3)

/-- The genuine physical Riesz lift, on the complete physical energy domain. -/
def physicalRieszLift (a : ℝ) (ha : 0 < a) :
    PhysicalHeightL2 →L[ℂ] physicalClosedEnergyDomain a ha :=
  (physicalClosedEmbedding a ha).adjoint

/-- Constructed from the physical form, with no spectral or graph input. -/
def physicalUnitShiftResolvent (a : ℝ) (ha : 0 < a) :
    PhysicalHeightL2 →L[ℂ] PhysicalHeightL2 :=
  adjointSquare (physicalClosedEmbedding a ha)

theorem physicalRieszLift_weak (a : ℝ) (ha : 0 < a)
    (f : PhysicalHeightL2) (d : physicalClosedEnergyDomain a ha) :
    inner ℂ (physicalClosedEmbedding a ha d)
        (physicalClosedEmbedding a ha (physicalRieszLift a ha f)) +
      physicalClosedForm a ha d (physicalRieszLift a ha f) =
        inner ℂ (physicalClosedEmbedding a ha d) f := by
  rw [← physicalClosedEnergy_inner]
  exact (physicalClosedEmbedding a ha).adjoint_inner_right d f

theorem physicalUnitShiftResolvent_positive (a : ℝ) (ha : 0 < a) :
    (physicalUnitShiftResolvent a ha).IsPositive :=
  adjointSquare_positive (physicalClosedEmbedding a ha)

theorem physicalUnitShiftResolvent_selfAdjoint (a : ℝ) (ha : 0 < a) :
    IsSelfAdjoint (physicalUnitShiftResolvent a ha) :=
  adjointSquare_selfAdjoint (physicalClosedEmbedding a ha)

theorem physicalUnitShiftResolvent_opNorm_le_one (a : ℝ) (ha : 0 < a) :
    ‖physicalUnitShiftResolvent a ha‖ ≤ 1 :=
  adjointSquare_opNorm_le_one (physicalClosedEmbedding a ha)
    (physicalClosedEmbedding_opNorm_le_one a ha)

theorem physicalUnitShiftResolvent_injective (a : ℝ) (ha : 0 < a) :
    Function.Injective (physicalUnitShiftResolvent a ha) :=
  adjointSquare_injective (physicalClosedEmbedding a ha)
    (physicalClosedEmbedding_denseRange a ha)

theorem physicalUnitShiftResolvent_denseRange (a : ℝ) (ha : 0 < a) :
    DenseRange (physicalUnitShiftResolvent a ha) :=
  adjointSquare_denseRange (physicalClosedEmbedding a ha)
    (physicalClosedEmbedding_denseRange a ha)

theorem physicalUnitShiftResolvent_firm (a : ℝ) (ha : 0 < a)
    (f : PhysicalHeightL2) :
    ‖physicalUnitShiftResolvent a ha f‖ ^ 2 ≤
      (inner ℂ f (physicalUnitShiftResolvent a ha f)).re :=
  adjointSquare_firm (physicalClosedEmbedding a ha)
    (physicalClosedEmbedding_opNorm_le_one a ha) f

/-- The actual physical energy pairing proves this equivalence on the
whole closed domain. It is not an assumed per-mode graph identification. -/
theorem physicalWeakEnergyRelation_iff_graph (a : ℝ) (ha : 0 < a)
    (u v : PhysicalHeightL2) :
    WeakEnergyRelation (physicalClosedEmbedding a ha) u v ↔
      (u, v) ∈ (actualModeFriedrichs a ha).graph := by
  rw [actualModeFriedrichs_graph]
  change (∃ e : physicalClosedEnergyDomain a ha,
    physicalClosedEmbedding a ha e = u ∧
      ∀ d : physicalClosedEnergyDomain a ha,
        inner ℂ d e = inner ℂ (physicalClosedEmbedding a ha d) (u + v)) ↔
    ∃ e : physicalClosedEnergyDomain a ha,
      physicalClosedEmbedding a ha e = u ∧
        ∀ d : physicalClosedEnergyDomain a ha,
          physicalClosedForm a ha d e = inner ℂ (physicalClosedEmbedding a ha d) v
  constructor
  · rintro ⟨e, he, hw⟩
    refine ⟨e, he, fun d => ?_⟩
    have h := hw d
    rw [physicalClosedEnergy_inner a ha d e, he, inner_add_right] at h
    linear_combination h
  · rintro ⟨e, he, hw⟩
    refine ⟨e, he, fun d => ?_⟩
    rw [physicalClosedEnergy_inner a ha d e, he, inner_add_right, hw d]

/-- Exact physical resolvent equation for the previously defined native
unbounded operator; no graph or inverse equation is supplied as input. -/
theorem actualModeFriedrichs_graph_iff_resolvent (a : ℝ) (ha : 0 < a)
    (u v : PhysicalHeightL2) :
    (u, v) ∈ (actualModeFriedrichs a ha).graph ↔
      physicalUnitShiftResolvent a ha (u + v) = u := by
  exact (physicalWeakEnergyRelation_iff_graph a ha u v).symm.trans
    (weakEnergyRelation_iff_adjointSquare (physicalClosedEmbedding a ha) u v)

theorem actualModeFriedrichs_resolvent_pair (a : ℝ) (ha : 0 < a)
    (f : PhysicalHeightL2) :
    (physicalUnitShiftResolvent a ha f,
      f - physicalUnitShiftResolvent a ha f) ∈ (actualModeFriedrichs a ha).graph := by
  apply (physicalWeakEnergyRelation_iff_graph a ha _ _).mp
  exact weakEnergyRelation_resolvent (physicalClosedEmbedding a ha) f

theorem actualModeFriedrichs_domain_eq_resolvent_range (a : ℝ) (ha : 0 < a) :
    ((actualModeFriedrichs a ha).domain : Set PhysicalHeightL2) =
      range (physicalUnitShiftResolvent a ha) := by
  ext u
  rw [LinearPMap.mem_domain_iff]
  simp only [← physicalWeakEnergyRelation_iff_graph]
  exact weakEnergyRelation_domain_iff_range (physicalClosedEmbedding a ha) u

theorem actualModeFriedrichs_existsUnique_shifted_solution (a : ℝ) (ha : 0 < a)
    (f : PhysicalHeightL2) :
    ∃! u : PhysicalHeightL2, (u, f - u) ∈ (actualModeFriedrichs a ha).graph := by
  simpa only [← physicalWeakEnergyRelation_iff_graph] using
    existsUnique_shifted_weak_solution (physicalClosedEmbedding a ha) f

end
end ImbalancedChen.Part3.CuspModePhysicalResolvent20261026b
