import ImbalancedChen.Part3Gamma0FixedCoreCompactOperator
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! SOURCE_ONLY / UNCOMPILED / zero formal credit.
A literal finite net of the actual J_Y unit-ball image spans a finite
dimensional subspace of canonical Gamma0 quotient L2. Its actual orthogonal
projection yields an operator-norm finite-rank approximation of J_Y.
No finite-rank or abstract approximation-property theorem is a premise. -/

namespace ImbalancedChen.Part3.Gamma0FixedCoreFiniteNetProjection20261026b
noncomputable section
open Set Metric MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0CompletedFormFixedCoreRellich20261026b
open Gamma0FixedCoreCompactOperator20261026b

def finiteNetProjection (N : ℕ) [NeZero N] (S : Finset (QuotientL2 N)) :
    QuotientL2 N →L[ℂ] QuotientL2 N :=
  (Submodule.span ℂ (S : Set (QuotientL2 N))).starProjection

theorem finiteNetProjection_range (N : ℕ) [NeZero N] (S : Finset (QuotientL2 N)) :
    (finiteNetProjection N S).range = Submodule.span ℂ (S : Set (QuotientL2 N)) :=
  Submodule.range_starProjection _

theorem finiteNetProjection_finiteRange (N : ℕ) [NeZero N] (S : Finset (QuotientL2 N)) :
    FiniteDimensional ℂ (finiteNetProjection N S).range := by
  rw [finiteNetProjection_range]
  infer_instance

theorem finiteNetProjection_idempotent (N : ℕ) [NeZero N] (S : Finset (QuotientL2 N)) :
    IsIdempotentElem (finiteNetProjection N S) :=
  (Submodule.span ℂ (S : Set (QuotientL2 N))).isIdempotentElem_starProjection

theorem finiteNetProjection_selfAdjoint (N : ℕ) [NeZero N] (S : Finset (QuotientL2 N)) :
    IsSelfAdjoint (finiteNetProjection N S) :=
  isSelfAdjoint_starProjection (Submodule.span ℂ (S : Set (QuotientL2 N)))

/-- The genuine orthogonal projection error is bounded by the distance
to ANY net center in the finite span. -/
theorem finiteNetProjection_error_le_center (N : ℕ) [NeZero N]
    (S : Finset (QuotientL2 N)) (x v : QuotientL2 N) (hv : v ∈ S) :
    ‖x-finiteNetProjection N S x‖ ≤ dist x v := by
  let V := Submodule.span ℂ (S : Set (QuotientL2 N))
  have hvV : v ∈ V := Submodule.subset_span hv
  have hfix : V.starProjection v = v := Submodule.starProjection_eq_self_iff.mpr hvV
  have he : Vᗮ.starProjection (x-v) = x-V.starProjection x := by
    rw [Submodule.starProjection_orthogonal V]
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,map_sub,hfix]
    abel
  have h := Vᗮ.norm_starProjection_apply_le (x-v)
  rw [he] at h
  simpa only [dist_eq_norm,finiteNetProjection,V] using h

/-- A finite net is selected BEFORE every vector in the actual completed
energy unit ball. Its literal finite span supplies an orthogonal finite
rank projection P with ||J_Y-P J_Y|| at most epsilon. -/
theorem exists_actual_finite_net_orthogonal_approximation (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset (QuotientL2 N),
      (∀ e : EnergyCompletion N, ‖e‖^2 ≤ 1 →
        ∃ v ∈ S, dist (completedCoreRestriction N Y e) v < ε) ∧
      ‖completedCoreRestriction N Y-(finiteNetProjection N S).comp (completedCoreRestriction N Y)‖ ≤ ε := by
  obtain ⟨T,hTfin,hTcover⟩ := Metric.totallyBounded_iff.mp
    (actual_completed_form_fixed_core_totallyBounded N Y hY 1 (by norm_num)) ε hε
  let S : Finset (QuotientL2 N) := hTfin.toFinset
  have hnet (e : EnergyCompletion N) (he : ‖e‖^2 ≤ 1) :
      ∃ v ∈ S, dist (completedCoreRestriction N Y e) v < ε := by
    obtain ⟨v,hv,hd⟩ := Set.mem_iUnion₂.mp (hTcover ⟨e,he,rfl⟩)
    refine ⟨v,?_,hd⟩
    simpa only [S,Set.Finite.mem_toFinset] using hv
  refine ⟨S,hnet,?_⟩
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hε.le
  intro e he
  obtain ⟨v,hv,hd⟩ := hnet e (by simp [he])
  exact (finiteNetProjection_error_le_center N S (completedCoreRestriction N Y e) v hv).trans hd.le

/-- Unbundled operator form exposes finite dimensional range, actual
orthogonality and the norm approximation together. -/
theorem exists_finiteRank_orthogonal_approximation (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : QuotientL2 N →L[ℂ] QuotientL2 N,
      FiniteDimensional ℂ P.range ∧ IsIdempotentElem P ∧ IsSelfAdjoint P ∧
        ‖completedCoreRestriction N Y-P.comp (completedCoreRestriction N Y)‖ ≤ ε := by
  obtain ⟨S,_hnet,happrox⟩ := exists_actual_finite_net_orthogonal_approximation N Y hY ε hε
  exact ⟨finiteNetProjection N S,finiteNetProjection_finiteRange N S,
    finiteNetProjection_idempotent N S,finiteNetProjection_selfAdjoint N S,happrox⟩

end
end ImbalancedChen.Part3.Gamma0FixedCoreFiniteNetProjection20261026b
