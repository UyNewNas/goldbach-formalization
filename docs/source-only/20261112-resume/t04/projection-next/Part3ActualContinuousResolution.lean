import ImbalancedChen.Part3ActualContinuousGeneratorColumns
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! Resolution of the spatial operator on the closed span of the
physical centered zero-mode Poincaré generators. -/
namespace ImbalancedChen.Part3.ActualContinuousResolution20261112

noncomputable section
open Set Filter Topology MeasureTheory Complex Matrix
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualContinuousGeneratorColumns20261112 ActualHorocycleSynthesisBound20261112
open ActualLogHorocycleAdjoint20261112 ActualMarkedContinuousCoordinates20261112
open AngularFourierUnitary20261026b SmoothZeroHeightSeedProfiles20261026b
open Gamma0QuotientCellPushforward20261025a Gamma0ActualConstantMode20261025a
open ActualCuspDenominatorClasses20261110

def generators (N : ℕ) [NeZero N] : Set (QuotientL2 N) :=
  {v | ∃ (g : SL(2,ℤ)) (ψ : SmoothHeightSeed),centeredSeed N g ψ = v}

def centeredSpace (N : ℕ) [NeZero N] : Submodule ℂ (QuotientL2 N) :=
  (Submodule.span ℂ (generators N)).topologicalClosure

theorem centered_closed (N : ℕ) [NeZero N] : IsClosed (centeredSpace N : Set (QuotientL2 N)) :=
  (Submodule.span ℂ (generators N)).isClosed_topologicalClosure

instance centeredComplete (N : ℕ) [NeZero N] : CompleteSpace (centeredSpace N) :=
  (centered_closed N).completeSpace_coe

theorem centeredSeed_mem (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (ψ : SmoothHeightSeed) :
    centeredSeed N g ψ ∈ centeredSpace N :=
  (Submodule.span ℂ (generators N)).le_topologicalClosure (Submodule.subset_span ⟨g,ψ,rfl⟩)

theorem centered_le (N : ℕ) [NeZero N] {K : Submodule ℂ (QuotientL2 N)} (hK : IsClosed (K : Set _))
    (H : ∀ g ψ, centeredSeed N g ψ ∈ K) : centeredSpace N ≤ K :=
  (Submodule.span ℂ (generators N)).topologicalClosure_minimal (Submodule.span_le.mpr (by
    rintro _ ⟨g,ψ,rfl⟩
    exact H g ψ)) hK

theorem centered_perp_iff (N : ℕ) [NeZero N] (v : QuotientL2 N) :
    v ∈ (centeredSpace N)ᗮ ↔ ∀ g ψ, inner ℂ (centeredSeed N g ψ) v=0 := by
  refine ⟨fun hv g ψ => hv _ (centeredSeed_mem N g ψ),?_⟩
  intro H
  have J : centeredSpace N ≤ (ℂ ∙ v)ᗮ :=
    centered_le N (Submodule.isClosed_orthogonal _) (fun g ψ =>
      Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (H g ψ))
  intro x hx
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (J hx)

theorem synthesis_mem (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (u : RealL2) :
    synthesis N g u ∈ centeredSpace N :=
  test_dense.induction_on u ((centered_closed N).preimage (synthesis N g).continuous) (fun f => by
    rw [synthesis_test]
    exact centeredSeed_mem _ _ _)

theorem nativeSynthesis_mem (N : ℕ) [NeZero N] (h : Parameters N → AngularL2) :
    nativeSynthesis N h ∈ centeredSpace N :=
  (centeredSpace N).smul_mem _ ((centeredSpace N).sum_mem (fun a _ => synthesis_mem _ _ _))

def resolution (N : ℕ) [NeZero N] : QuotientL2 N →L[ℂ] QuotientL2 N :=
  (1/2 : ℂ) • ∑ a : Parameters N,(synthesis N (parameterFrame a)).comp (synthesis N (parameterFrame a)).adjoint

theorem resolution_apply (N : ℕ) [NeZero N] (v : QuotientL2 N) :
    resolution N v = nativeSynthesis N (fun a => analysis N a v) := by
  simp only [resolution,ContinuousLinearMap.smul_apply,sum_apply,ContinuousLinearMap.comp_apply,
    nativeSynthesis,analysis,LinearIsometryEquiv.symm_apply_apply]

theorem resolution_inner (N : ℕ) [NeZero N] (x y : QuotientL2 N) :
    inner ℂ x (resolution N y) = (1/2 : ℂ)*∑ a : Parameters N,inner ℂ (analysis N a x) (analysis N a y) := by
  rw [resolution_apply,nativeSynthesis,inner_smul_right,inner_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [← ContinuousLinearMap.adjoint_inner_left,← angularFourierUnitary.inner_map_eq_flip] <;> rfl

private theorem fix_generator (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (φ : SmoothHeightSeed) :
    resolution N (centeredSeed N g φ) = centeredSeed N g φ := by
  let y := centeredSeed N g φ
  let v := resolution N y-y
  have hy : y ∈ centeredSpace N := centeredSeed_mem N g φ
  have hv : v ∈ centeredSpace N := (centeredSpace N).sub_mem
    (by rw [resolution_apply]; exact nativeSynthesis_mem _ _) hy
  have hz : v ∈ (centeredSpace N)ᗮ := (centered_perp_iff N v).mpr (fun h ψ => by
    rw [show v=resolution N y-y from rfl,inner_sub_right,resolution_inner,
      ← analysis_seed_gram N h g ψ φ,sub_self])
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (hz v hv))

theorem fix_centered (N : ℕ) [NeZero N] {v : QuotientL2 N} (hv : v ∈ centeredSpace N) :
    resolution N v=v := by
  let D := resolution N-ContinuousLinearMap.id ℂ (QuotientL2 N)
  have H : centeredSpace N ≤ D.ker := centered_le N D.isClosed_ker (fun g ψ =>
    show resolution N (centeredSeed N g ψ)-centeredSeed N g ψ=0 from sub_eq_zero.mpr (fix_generator N g ψ))
  exact sub_eq_zero.mp (show resolution N v-v=0 from H hv)

theorem adjoint_vanishes (N : ℕ) [NeZero N] {v : QuotientL2 N} (hv : v ∈ (centeredSpace N)ᗮ)
    (g : SL(2,ℤ)) : (synthesis N g).adjoint v=0 := by
  apply ext_inner_left ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right,inner_zero_right]
  exact hv _ (synthesis_mem N g u)

theorem resolution_perp (N : ℕ) [NeZero N] {v : QuotientL2 N} (hv : v ∈ (centeredSpace N)ᗮ) :
    resolution N v=0 := by
  simp only [resolution,ContinuousLinearMap.smul_apply,sum_apply,ContinuousLinearMap.comp_apply,
    adjoint_vanishes N hv,map_zero,Finset.sum_const_zero,smul_zero]

/-- The physical frame operator equals the orthogonal projection on the
whole quotient Hilbert space. The subspace was fixed from the original
zero Poincaré seeds before the spectral analysis map was applied. -/
theorem resolution_eq_projection (N : ℕ) [NeZero N] :
    resolution N = (centeredSpace N).starProjection := by
  apply ContinuousLinearMap.ext
  intro v
  let p := (centeredSpace N).starProjection v
  have P : resolution N p=p := fix_centered N ((centeredSpace N).starProjection_apply_mem v)
  have J := resolution_perp N ((centeredSpace N).sub_starProjection_mem_orthogonal v)
  rw [map_sub] at J
  exact (sub_eq_zero.mp J).trans P

theorem nativeSynthesis_analysis_eq_projection (N : ℕ) [NeZero N] (v : QuotientL2 N) :
    nativeSynthesis N (fun a => analysis N a v) = (centeredSpace N).starProjection v := by
  rw [← resolution_apply,resolution_eq_projection]

theorem range_nativeSynthesis (N : ℕ) [NeZero N] :
    range (nativeSynthesis N) = (centeredSpace N : Set (QuotientL2 N)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨h,rfl⟩
    exact nativeSynthesis_mem N h
  · intro v hv
    exact ⟨fun a => analysis N a v,(resolution_apply N v).symm.trans (fix_centered N hv)⟩

theorem continuous_projection_gram (N : ℕ) [NeZero N] (v w : QuotientL2 N) :
    inner ℂ ((centeredSpace N).starProjection v) ((centeredSpace N).starProjection w) =
      (1/2 : ℂ)*∑ a : Parameters N,inner ℂ (analysis N a v) (analysis N a w) := by
  have h := (centeredSpace N).starProjection_inner_eq_zero v
    ((centeredSpace N).starProjection w) ((centeredSpace N).starProjection_apply_mem w)
  rw [inner_sub_left,sub_eq_zero] at h
  exact h.symm.trans (by rw [← resolution_eq_projection,resolution_inner])

end
end ImbalancedChen.Part3.ActualContinuousResolution20261112
