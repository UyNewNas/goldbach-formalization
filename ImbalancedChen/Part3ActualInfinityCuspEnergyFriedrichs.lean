import ImbalancedChen.Part3ActualInfinityCuspRestrictedEnergy
import ImbalancedChen.Part3GenericWeakFriedrichsAssociation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A native densely-defined self-adjoint Friedrichs operator on the closure
of the PHYSICAL IMAGE of the actual infinity-cusp energy space. Density
in this precise Hilbert space is proved, not assumed. The exact graph is
the original Gamma closed Dirichlet pairing restricted to actual cusp
energy tests. Equality of this image closure with the entire infinity
annihilator, equality with the original unrestricted Gamma operator, and
all-cusp spectral completeness remain separate obligations.
-/
namespace ImbalancedChen.Part3.ActualInfinityCuspEnergyFriedrichs20261026b

noncomputable section
open Set MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a
open ActualInfinityCuspAnnihilator20261026b
open ActualInfinityCuspRestrictedEnergy20261026b
open GenericHilbertAdjointSquare20261025a
open GenericWeakFriedrichsAssociation20261025a
open GenericFriedrichsOperator20261025a

/-- No unproved density in the larger cusp annihilator is built into
this actual physical Hilbert subspace. -/
def infinityCuspEnergyImage (N : ℕ) [NeZero N] : Submodule ℂ (QuotientL2 N) :=
  (infinityCuspEnergyInclusion N).range.topologicalClosure

theorem infinityCuspEnergyImage_closed (N : ℕ) [NeZero N] :
    IsClosed (infinityCuspEnergyImage N : Set (QuotientL2 N)) :=
  (infinityCuspEnergyInclusion N).range.isClosed_topologicalClosure

instance infinityCuspEnergyImage_complete (N : ℕ) [NeZero N] :
    CompleteSpace (infinityCuspEnergyImage N) :=
  (infinityCuspEnergyImage_closed N).completeSpace_coe

theorem infinityCuspEnergyImage_le_cusp (N : ℕ) [NeZero N] :
    infinityCuspEnergyImage N ≤ infinityCuspSubspace N := by
  apply (infinityCuspEnergyInclusion N).range.topologicalClosure_minimal
    _ (infinityCuspSubspace_closed N)
  rintro _ ⟨e, rfl⟩
  exact infinityCuspEnergyInclusion_mem N e

def denseCuspEnergyInclusion (N : ℕ) [NeZero N] :
    infinityCuspEnergy N →L[ℂ] infinityCuspEnergyImage N :=
  (infinityCuspEnergyInclusion N).codRestrict (infinityCuspEnergyImage N)
    (fun e => (infinityCuspEnergyInclusion N).range.le_topologicalClosure ⟨e, rfl⟩)

theorem denseCuspEnergyInclusion_norm_le (N : ℕ) [NeZero N]
    (e : infinityCuspEnergy N) : ‖denseCuspEnergyInclusion N e‖ ≤ ‖e‖ :=
  infinityCuspEnergyInclusion_norm_le N e

theorem denseCuspEnergyInclusion_opNorm_le_one (N : ℕ) [NeZero N] :
    ‖denseCuspEnergyInclusion N‖ ≤ 1 := by
  apply (denseCuspEnergyInclusion N).opNorm_le_bound zero_le_one
  intro e
  simpa only [one_mul] using denseCuspEnergyInclusion_norm_le N e

private theorem denseCuspEnergyInclusion_adjoint_eq_zero (N : ℕ) [NeZero N]
    (f : infinityCuspEnergyImage N) (hf : (denseCuspEnergyInclusion N).adjoint f = 0) :
    f = 0 := by
  have hle : infinityCuspEnergyImage N ≤ (innerSL ℂ (f : QuotientL2 N)).ker := by
    apply (infinityCuspEnergyInclusion N).range.topologicalClosure_minimal
      _ (innerSL ℂ (f : QuotientL2 N)).isClosed_ker
    rintro _ ⟨e, rfl⟩
    change inner ℂ (f : QuotientL2 N) (infinityCuspEnergyInclusion N e) = 0
    have h := (denseCuspEnergyInclusion N).adjoint_inner_left e f
    rw [hf, inner_zero_left] at h
    exact h.symm
  have hz : inner ℂ (f : QuotientL2 N) (f : QuotientL2 N) = 0 := hle f.property
  apply Subtype.ext
  exact inner_self_eq_zero.mp hz

/-- Density is obtained from the actual image closure via inner-product
separation, without a density premise on the entire cusp annihilator. -/
theorem denseCuspEnergyInclusion_denseRange (N : ℕ) [NeZero N] :
    DenseRange (denseCuspEnergyInclusion N) := by
  have hinj : Function.Injective (denseCuspEnergyInclusion N).adjoint := by
    intro f g h
    apply sub_eq_zero.mp
    apply denseCuspEnergyInclusion_adjoint_eq_zero N
    rw [map_sub, h, sub_self]
  have hker : (denseCuspEnergyInclusion N).adjoint.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  change Dense ((denseCuspEnergyInclusion N).range : Set (infinityCuspEnergyImage N))
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply (denseCuspEnergyInclusion N).range.topologicalClosure_eq_top_iff.mpr
  rw [ContinuousLinearMap.orthogonal_range, hker]

def denseCuspResolvent (N : ℕ) [NeZero N] :
    infinityCuspEnergyImage N →L[ℂ] infinityCuspEnergyImage N :=
  adjointSquare (denseCuspEnergyInclusion N)

theorem denseCuspResolvent_selfAdjoint (N : ℕ) [NeZero N] :
    IsSelfAdjoint (denseCuspResolvent N) :=
  adjointSquare_selfAdjoint (denseCuspEnergyInclusion N)

theorem denseCuspResolvent_injective (N : ℕ) [NeZero N] :
    Function.Injective (denseCuspResolvent N) :=
  adjointSquare_injective (denseCuspEnergyInclusion N) (denseCuspEnergyInclusion_denseRange N)

theorem denseCuspResolvent_firm (N : ℕ) [NeZero N]
    (f : infinityCuspEnergyImage N) :
    ‖denseCuspResolvent N f‖ ^ 2 ≤ (inner ℂ f (denseCuspResolvent N f)).re :=
  adjointSquare_firm (denseCuspEnergyInclusion N) (denseCuspEnergyInclusion_opNorm_le_one N) f

def infinityCuspEnergyFriedrichs (N : ℕ) [NeZero N] :
    infinityCuspEnergyImage N →ₗ.[ℂ] infinityCuspEnergyImage N :=
  friedrichsR (denseCuspResolvent N)

theorem infinityCuspEnergyFriedrichs_selfAdjoint (N : ℕ) [NeZero N] :
    IsSelfAdjoint (infinityCuspEnergyFriedrichs N) :=
  friedrichsR_isSelfAdjoint (denseCuspResolvent N)
    (denseCuspResolvent_selfAdjoint N) (denseCuspResolvent_injective N)

theorem infinityCuspEnergyFriedrichs_dense_domain (N : ℕ) [NeZero N] :
    Dense ((infinityCuspEnergyFriedrichs N).domain : Set (infinityCuspEnergyImage N)) :=
  friedrichsR_dense_domain (denseCuspResolvent N)
    (denseCuspResolvent_selfAdjoint N) (denseCuspResolvent_injective N)

theorem infinityCuspEnergyFriedrichs_nonneg (N : ℕ) [NeZero N]
    (u : (infinityCuspEnergyFriedrichs N).domain) :
    0 ≤ (inner ℂ (u : infinityCuspEnergyImage N) (infinityCuspEnergyFriedrichs N u)).re :=
  friedrichsR_nonneg (denseCuspResolvent N) (denseCuspResolvent_injective N)
    (denseCuspResolvent_firm N) u

/-- Exact native graph with the original unshifted Gamma form, tested
against ALL genuine constrained completed-energy vectors. -/
theorem infinityCuspEnergyFriedrichs_graph_iff_form (N : ℕ) [NeZero N]
    (u v : infinityCuspEnergyImage N) :
    (u, v) ∈ (infinityCuspEnergyFriedrichs N).graph ↔
      ∃ e : infinityCuspEnergy N, denseCuspEnergyInclusion N e = u ∧
        ∀ d : infinityCuspEnergy N,
          actualDirichletPair N (d : EnergyCompletion N) (e : EnergyCompletion N) =
            inner ℂ (denseCuspEnergyInclusion N d) v := by
  rw [show (infinityCuspEnergyFriedrichs N) = friedrichsR (denseCuspResolvent N) from rfl,
    friedrichsR_mem_graph_iff _ (denseCuspResolvent_injective N)]
  rw [← weakEnergyRelation_iff_adjointSquare (denseCuspEnergyInclusion N)]
  constructor
  · rintro ⟨e, he, htest⟩
    refine ⟨e, he, ?_⟩
    intro d
    have h := htest d
    rw [inner_add_right] at h
    change inner ℂ (d : EnergyCompletion N) (e : EnergyCompletion N) =
      inner ℂ (denseCuspEnergyInclusion N d) u +
        inner ℂ (denseCuspEnergyInclusion N d) v at h
    rw [actualDirichletPair]
    have hphys : inner ℂ (physicalProjection N (d : EnergyCompletion N))
        (physicalProjection N (e : EnergyCompletion N)) =
        inner ℂ (denseCuspEnergyInclusion N d) u := by
      rw [← he]
      rfl
    rw [hphys, h]
    ring
  · rintro ⟨e, he, htest⟩
    refine ⟨e, he, ?_⟩
    intro d
    have h := htest d
    rw [actualDirichletPair] at h
    rw [inner_add_right]
    change inner ℂ (d : EnergyCompletion N) (e : EnergyCompletion N) = _
    have hphys : inner ℂ (physicalProjection N (d : EnergyCompletion N))
        (physicalProjection N (e : EnergyCompletion N)) =
        inner ℂ (denseCuspEnergyInclusion N d) u := by
      rw [← he]
      rfl
    rw [hphys] at h
    linear_combination h

end
end ImbalancedChen.Part3.ActualInfinityCuspEnergyFriedrichs20261026b
