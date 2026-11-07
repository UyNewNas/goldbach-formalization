import ImbalancedChen.Part3ActualCompletedTensorEnergyForm
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The Friedrichs weak resolvent associated to the actual completed shifted
gradient-energy graph. Its construction is the actual physical projection
composed with its Hilbert adjoint. The adjoint supplies Riesz representation
on the complete actual energy space, with no representation, weak-form or
self-adjointness hypothesis supplied by the caller.

This bounded resolvent is not identified with the previously constructed
minimal differential-operator closure or a Γ₀ automorphic operator.
The completed-energy supplier is frozen source-only mathematical code.
-/

namespace ImbalancedChen.Part3.ActualCompletedEnergyResolvent20261025a

noncomputable section

open MeasureTheory
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.MaassFiniteCoreL2LinearOperator20261025a
open ImbalancedChen.Part3.ActualCompletedTensorEnergyForm20261025a
open ImbalancedChen.Part3.ActualTensorGradientLinearMaps20261025a

abbrev ActualEnergy := completedEnergy

/-- The inherited completed Hilbert form is literally mass plus the two
actual closed gradient pairings, including mixed pairs. -/
theorem completedEnergy_inner_coordinates (u v : ActualEnergy) :
    inner ℂ u v =
      inner ℂ (physicalProjection u) (physicalProjection v) +
        inner ℂ (completedGradient false u) (completedGradient false v) +
        inner ℂ (completedGradient true u) (completedGradient true v) := by
  change inner ℂ (u : EnergyTriple) (v : EnergyTriple) =
    inner ℂ (WithLp.ofLp (u : EnergyTriple)).1 (WithLp.ofLp (v : EnergyTriple)).1 +
      inner ℂ (WithLp.ofLp (WithLp.ofLp (u : EnergyTriple)).2).1
        (WithLp.ofLp (WithLp.ofLp (v : EnergyTriple)).2).1 +
      inner ℂ (WithLp.ofLp (WithLp.ofLp (u : EnergyTriple)).2).2
        (WithLp.ofLp (WithLp.ofLp (v : EnergyTriple)).2).2
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  ring

/-- The genuine energy-space Riesz solution, constructed using the
Hilbert adjoint of the actual physical projection. -/
def energyRieszSolution (f : HyperbolicL2) : ActualEnergy :=
  physicalProjection.adjoint f

/-- The genuine physical weak resolvent. -/
def actualWeakResolvent : HyperbolicL2 →L[ℂ] HyperbolicL2 :=
  physicalProjection.comp physicalProjection.adjoint

theorem actualWeakResolvent_apply (f : HyperbolicL2) :
    actualWeakResolvent f = physicalProjection (energyRieszSolution f) := rfl

theorem actualWeakResolvent_positive : actualWeakResolvent.IsPositive :=
  ContinuousLinearMap.isPositive_self_comp_adjoint physicalProjection

theorem actualWeakResolvent_selfAdjoint : IsSelfAdjoint actualWeakResolvent :=
  actualWeakResolvent_positive.isSelfAdjoint

theorem physicalProjection_opNorm_le_one : ‖physicalProjection‖ ≤ 1 := by
  apply physicalProjection.opNorm_le_bound zero_le_one
  intro u
  simpa only [one_mul] using physicalProjection_norm_le u

theorem energyRieszSolution_norm_le (f : HyperbolicL2) :
    ‖energyRieszSolution f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖physicalProjection.adjoint‖ * ‖f‖ := physicalProjection.adjoint.le_opNorm f
    _ = ‖physicalProjection‖ * ‖f‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right physicalProjection_opNorm_le_one (norm_nonneg f)
    _ = _ := one_mul _

theorem actualWeakResolvent_norm_le (f : HyperbolicL2) :
    ‖actualWeakResolvent f‖ ≤ ‖f‖ :=
  (physicalProjection_norm_le (energyRieszSolution f)).trans (energyRieszSolution_norm_le f)

theorem actualWeakResolvent_opNorm_le_one : ‖actualWeakResolvent‖ ≤ 1 := by
  apply actualWeakResolvent.opNorm_le_bound zero_le_one
  intro f
  simpa only [one_mul] using actualWeakResolvent_norm_le f

/-- The resolvent quadratic form is the squared norm of the actual
completed-energy Riesz solution. -/
theorem actualWeakResolvent_quadratic (f : HyperbolicL2) :
    (inner ℂ f (actualWeakResolvent f)).re = ‖energyRieszSolution f‖ ^ 2 := by
  have he : inner ℂ f (actualWeakResolvent f) =
      inner ℂ (energyRieszSolution f) (energyRieszSolution f) :=
    (physicalProjection.adjoint_inner_left (energyRieszSolution f) f).symm
  rw [he, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.ofReal_re]

theorem physicalAdjoint_eq_zero_iff (f : HyperbolicL2) :
    physicalProjection.adjoint f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    apply (show Dense (Set.range physicalProjection) from
      physicalProjection_denseRange).eq_zero_of_inner_left ℂ
    rintro _ ⟨u, rfl⟩
    rw [← physicalProjection.adjoint_inner_left u f, hf, inner_zero_left]
  · intro hf
    simp [hf]

theorem physicalAdjoint_injective : Function.Injective physicalProjection.adjoint := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply (physicalAdjoint_eq_zero_iff (f - g)).mp
  rw [map_sub, hfg, sub_self]

theorem actualWeakResolvent_injective : Function.Injective actualWeakResolvent := by
  intro f g hfg
  exact physicalAdjoint_injective (physicalProjection_injective hfg)

theorem actualWeakResolvent_ker : actualWeakResolvent.ker = ⊥ :=
  LinearMap.ker_eq_bot.mpr actualWeakResolvent_injective

theorem actualWeakResolvent_denseRange : DenseRange actualWeakResolvent := by
  change Dense (actualWeakResolvent.range : Set HyperbolicL2)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply actualWeakResolvent.range.topologicalClosure_eq_top_iff.mpr
  rw [ContinuousLinearMap.orthogonal_range,
    actualWeakResolvent_selfAdjoint.adjoint_eq, actualWeakResolvent_ker]

/-- The completed actual shifted-energy weak equation. -/
def IsEnergyWeakSolution (f : HyperbolicL2) (u : ActualEnergy) : Prop :=
  ∀ v : ActualEnergy, inner ℂ v u = inner ℂ (physicalProjection v) f

theorem energyRieszSolution_isWeak (f : HyperbolicL2) :
    IsEnergyWeakSolution f (energyRieszSolution f) :=
  fun v => physicalProjection.adjoint_inner_right v f

theorem energyWeakSolution_unique {f : HyperbolicL2} {u : ActualEnergy}
    (hu : IsEnergyWeakSolution f u) : u = energyRieszSolution f := by
  apply ext_inner_left ℂ
  intro v
  exact (hu v).trans (energyRieszSolution_isWeak f v).symm

/-- Testing the genuine completed energy against the actual compact
core. Core density below is proved by the completed graph supplier. -/
def IsCoreTestWeakSolution (f : HyperbolicL2) (u : ActualEnergy) : Prop :=
  ∀ v : actualTensorDomain,
    inner ℂ (coreEmbedding v) u = inner ℂ (v : HyperbolicL2) f

theorem energyRieszSolution_coreWeak (f : HyperbolicL2) :
    IsCoreTestWeakSolution f (energyRieszSolution f) := by
  intro v
  change inner ℂ (coreEmbedding v) (physicalProjection.adjoint f) =
    inner ℂ (v : HyperbolicL2) f
  rw [physicalProjection.adjoint_inner_right, physicalProjection_coreEmbedding]

/-- Explicit actual mass-and-gradient weak equation for the physical
resolvent and its completed actual gradient lift. -/
theorem actual_mass_gradient_weak_equation (f : HyperbolicL2) (v : actualTensorDomain) :
    inner ℂ (v : HyperbolicL2) (actualWeakResolvent f) +
      inner ℂ (actualGradient false v) (completedGradient false (energyRieszSolution f)) +
      inner ℂ (actualGradient true v) (completedGradient true (energyRieszSolution f)) =
      inner ℂ (v : HyperbolicL2) f := by
  have h := energyRieszSolution_coreWeak f v
  rw [completedEnergy_inner_coordinates, physicalProjection_coreEmbedding,
    completedGradient_coreEmbedding, completedGradient_coreEmbedding] at h
  exact h

theorem coreTestWeakSolution_unique {f : HyperbolicL2} {u : ActualEnergy}
    (hu : IsCoreTestWeakSolution f u) : u = energyRieszSolution f := by
  apply (show Dense (Set.range coreEmbedding) from
    coreEmbedding_denseRange).eq_of_inner_right ℂ
  rintro _ ⟨v, rfl⟩
  exact (hu v).trans (energyRieszSolution_coreWeak f v).symm

def IsPhysicalCoreWeakSolution (f w : HyperbolicL2) : Prop :=
  ∃ u : ActualEnergy, physicalProjection u = w ∧ IsCoreTestWeakSolution f u

theorem actualWeakResolvent_isPhysicalWeak (f : HyperbolicL2) :
    IsPhysicalCoreWeakSolution f (actualWeakResolvent f) :=
  ⟨energyRieszSolution f, rfl, energyRieszSolution_coreWeak f⟩

theorem physicalCoreWeakSolution_unique {f w : HyperbolicL2}
    (hw : IsPhysicalCoreWeakSolution f w) : w = actualWeakResolvent f := by
  obtain ⟨u, hphysical, hu⟩ := hw
  rw [← hphysical, coreTestWeakSolution_unique hu]
  rfl

/-- Full actual weak resolvent: unique physical output, actual compact
core weak tests, and the contraction estimate, without an abstract form
or Riesz supplier premise. -/
theorem existsUnique_actualPhysicalWeakSolution (f : HyperbolicL2) :
    ∃! w : HyperbolicL2, IsPhysicalCoreWeakSolution f w ∧ ‖w‖ ≤ ‖f‖ := by
  refine ⟨actualWeakResolvent f,
    ⟨actualWeakResolvent_isPhysicalWeak f, actualWeakResolvent_norm_le f⟩, ?_⟩
  intro w hw
  exact physicalCoreWeakSolution_unique hw.1

end

end ImbalancedChen.Part3.ActualCompletedEnergyResolvent20261025a
