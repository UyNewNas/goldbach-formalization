import ImbalancedChen.Part3MaassFiniteCoreL2Symmetry
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Finite-dimensional weak resolvent for the actual canonical hyperbolic L2
Maass graph. The only operator data are a linear restriction of that actual
graph to the finite trial space. Its graph membership certificate records
actual finite tensor presentations; positivity, coercivity, invertibility
and a resolvent are proved, rather than supplied as assumptions.

This theorem applies to every finite-dimensional trial submodule carrying
such an actual graph restriction. Constructing the linear restriction from
an arbitrary finite tensor generating family is a separate algebraic-core
closure obligation. No closed infinite-dimensional resolvent, dense range,
self-adjoint extension or spectral decomposition is asserted.
-/

namespace ImbalancedChen.Part3.FiniteTensorGalerkinResolvent20261025a

noncomputable section

open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.MaassFiniteCoreL2Symmetry20261025a

variable (V : Submodule ℂ HyperbolicL2) [FiniteDimensional ℂ V]

/-- This is the coordinate Maass operator restricted to actual finite
tensor inputs. The witness is graph membership, not an analytic estimate. -/
def IsActualGraphRestriction (D : V →ₗ[ℂ] HyperbolicL2) : Prop :=
  ∀ u : V, ((u : HyperbolicL2), D u) ∈ finiteTensorL2Graph

/-- The actual differential graph fixes its restriction uniquely; the
primitive graph certificate cannot select an unrelated positive operator. -/
theorem actualGraphRestriction_unique (D E : V →ₗ[ℂ] HyperbolicL2)
    (hD : IsActualGraphRestriction V D) (hE : IsActualGraphRestriction V E) : D = E := by
  ext u
  exact finiteTensorL2Graph_right_unique (hD u) (hE u)

/-- Orthogonal compression of `1 + Maass` to the actual finite test space. -/
def galerkinMap (D : V →ₗ[ℂ] HyperbolicL2) : V →ₗ[ℂ] V :=
  V.orthogonalProjectionOnto.toLinearMap.comp (V.subtype + D)

/-- The forcing belongs to ambient canonical hyperbolic L2; all test
vectors belong to the chosen trial space. This is the actual weak equation. -/
def IsWeakSolution (D : V →ₗ[ℂ] HyperbolicL2) (f : HyperbolicL2) (u : V) : Prop :=
  ∀ v : V, inner ℂ (v : HyperbolicL2) ((u : HyperbolicL2) + D u) =
    inner ℂ (v : HyperbolicL2) f

/-- Actual graph coercivity survives orthogonal compression. -/
theorem galerkinMap_coercive (D : V →ₗ[ℂ] HyperbolicL2)
    (hD : IsActualGraphRestriction V D) (u : V) :
    ‖u‖ ^ 2 ≤ (inner ℂ u (galerkinMap V D u)).re := by
  change ‖u‖ ^ 2 ≤
    (inner ℂ u (V.orthogonalProjectionOnto ((u : HyperbolicL2) + D u))).re
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact finiteTensorL2Graph_shifted_coercive (hD u)

/-- No invertibility premise is used: the actual energy identity kills
the kernel, and finite-dimensional linear algebra gives surjectivity. -/
theorem galerkinMap_bijective (D : V →ₗ[ℂ] HyperbolicL2)
    (hD : IsActualGraphRestriction V D) : Function.Bijective (galerkinMap V D) := by
  have hinj : Function.Injective (galerkinMap V D) := by
    intro u v huv
    have hz : galerkinMap V D (u - v) = 0 := by
      rw [map_sub, huv, sub_self]
    have hc := galerkinMap_coercive V D hD (u - v)
    rw [hz, inner_zero_right, Complex.zero_re] at hc
    have hn : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩

/-- The finite projected equation is equivalent to testing the actual
shifted coordinate Maass graph against every trial vector. -/
theorem weakSolution_iff_projected (D : V →ₗ[ℂ] HyperbolicL2)
    (f : HyperbolicL2) (u : V) :
    IsWeakSolution V D f u ↔ galerkinMap V D u = V.orthogonalProjectionOnto f := by
  constructor
  · intro h
    apply ext_inner_left ℂ
    intro v
    change inner ℂ v (V.orthogonalProjectionOnto ((u : HyperbolicL2) + D u)) =
      inner ℂ v (V.orthogonalProjectionOnto f)
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    exact h v
  · intro h v
    have hi := congrArg (fun w : V => inner ℂ v w) h
    change inner ℂ v (V.orthogonalProjectionOnto ((u : HyperbolicL2) + D u)) =
      inner ℂ v (V.orthogonalProjectionOnto f) at hi
    simpa only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] using hi

/-- The physical L2 norm of an actual Galerkin solution is at most the
ambient L2 forcing norm; no norm bound is supplied by the caller. -/
theorem weakSolution_norm_le (D : V →ₗ[ℂ] HyperbolicL2)
    (hD : IsActualGraphRestriction V D) (f : HyperbolicL2) (u : V)
    (hu : IsWeakSolution V D f u) : ‖(u : HyperbolicL2)‖ ≤ ‖f‖ := by
  have hc := finiteTensorL2Graph_shifted_coercive (hD u)
  rw [hu u] at hc
  have hi := re_inner_le_norm (𝕜 := ℂ) (u : HyperbolicL2) f
  by_cases hz : ‖(u : HyperbolicL2)‖ = 0
  · simpa only [hz] using norm_nonneg f
  · have hp : 0 < ‖(u : HyperbolicL2)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_left hp).mp
    nlinarith

/-- Finite-dimensional Ritz/Galerkin weak solvability on an actual graph
restriction, with uniqueness and the contraction estimate. -/
theorem existsUnique_weakSolution (D : V →ₗ[ℂ] HyperbolicL2)
    (hD : IsActualGraphRestriction V D) (f : HyperbolicL2) :
    ∃! u : V, IsWeakSolution V D f u ∧ ‖(u : HyperbolicL2)‖ ≤ ‖f‖ := by
  have hb := galerkinMap_bijective V D hD
  obtain ⟨u, hu⟩ := hb.2 (V.orthogonalProjectionOnto f)
  have hw : IsWeakSolution V D f u := (weakSolution_iff_projected V D f u).2 hu
  refine ⟨u, ⟨hw, weakSolution_norm_le V D hD f u hw⟩, ?_⟩
  intro v hv
  apply hb.1
  exact ((weakSolution_iff_projected V D f v).1 hv.1).trans hu.symm

end
end ImbalancedChen.Part3.FiniteTensorGalerkinResolvent20261025a
