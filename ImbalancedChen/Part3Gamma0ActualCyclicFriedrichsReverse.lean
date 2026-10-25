import ImbalancedChen.Part3Gamma0ActualCyclicFriedrichsGraph
import ImbalancedChen.Part3GenericResolventGlobalSpectralAssembly
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The EXACT reverse cyclic graph theorem for the ACTUAL Gamma0 Friedrichs
operator. The actual cyclic unitary proves R-invariance of its closed
physical cyclic subspace C; genuine self-adjointness proves invariance of
C-orthogonal. Native orthogonal decomposition and actual R-injectivity
then prove Rw in C implies w in C. Consequently the actual forcing u+A_Fu
belongs to C whenever the actual-domain input u belongs to C.

The full cyclic-restricted graph is therefore exactly the image of
(M_t h,h-M_t h), and its scalar conjugate is the NATIVE partial map
M_t^{-1}-I with exact domain range M_t. No zero-atom or lambda-integrability
premise is required, and no invariance/reducing hypothesis is assumed.
-/

namespace ImbalancedChen.Part3.Gamma0ActualCyclicFriedrichsReverse20261025a

noncomputable section
open Set MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0ActualCyclicFriedrichsGraph20261025a
open GenericResolventCyclicL2Representation20261025a
open GenericFriedrichsOperator20261025a
open GenericResolventGlobalSpectralAssembly20261025a

theorem actualCyclicSubspace_isClosed (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    IsClosed (actualCyclicSubspace N f:Set (QuotientL2 N)) :=
  isClosed_cyclicSubspace (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f

theorem actualCyclicSynthesis_injective (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    Function.Injective (actualCyclicSynthesis N f) := by
  intro h k hhk
  apply (actualCyclicRepresentation N f).injective
  apply Subtype.ext
  exact hhk

/-- Invariance is derived from the TRUE onto cyclic unitary. -/
theorem actualCyclicSubspace_resolvent_invariant (N : ℕ) [NeZero N]
    (f : QuotientL2 N) {u : QuotientL2 N} (hu : u∈actualCyclicSubspace N f) :
    actualGammaResolvent N u∈actualCyclicSubspace N f :=
  resolvent_mem_cyclicSubspace (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f hu

/-- The orthogonal complement is invariant by ACTUAL self-adjointness,
not by an assumed reducing-subspace or projection-commutation field. -/
theorem actualCyclicOrthogonal_resolvent_invariant (N : ℕ) [NeZero N]
    (f : QuotientL2 N) {v : QuotientL2 N} (hv : v∈(actualCyclicSubspace N f)ᗮ) :
    actualGammaResolvent N v∈(actualCyclicSubspace N f)ᗮ :=
  resolvent_mem_cyclicSubspace_orthogonal (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) f hv

/-- Closed cyclic orthogonal decomposition plus actual injectivity gives
the crucial reverse range property, without assuming a spectral inverse. -/
theorem actualCyclicSubspace_of_resolvent_mem (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (w : QuotientL2 N)
    (hw : actualGammaResolvent N w∈actualCyclicSubspace N f) :
    w∈actualCyclicSubspace N f := by
  let C := actualCyclicSubspace N f
  letI : CompleteSpace C := (actualCyclicSubspace_isClosed N f).completeSpace_coe
  obtain ⟨c,hc,d,hd,hdecomp⟩ := C.exists_add_mem_mem_orthogonal w
  have hRc : actualGammaResolvent N c∈C :=
    actualCyclicSubspace_resolvent_invariant N f hc
  have hRdC : actualGammaResolvent N d∈C := by
    have heq : actualGammaResolvent N d=actualGammaResolvent N w-actualGammaResolvent N c := by
      rw [hdecomp,map_add]
      abel
    rw [heq]
    exact C.sub_mem hw hRc
  have hRdOrth : actualGammaResolvent N d∈Cᗮ :=
    actualCyclicOrthogonal_resolvent_invariant N f hd
  have hRd0 : actualGammaResolvent N d=0 :=
    inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hRdC hRdOrth)
  have hd0 : d=0 := (actualGammaResolvent_injective N) (by simpa only [map_zero] using hRd0)
  rw [hdecomp,hd0,add_zero]
  exact hc

theorem actualFriedrichs_forcing_mem_cyclic (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (u : (actualGammaFriedrichs N).domain)
    (hu : (u:QuotientL2 N)∈actualCyclicSubspace N f) :
    (u:QuotientL2 N)+actualGammaFriedrichs N u∈actualCyclicSubspace N f := by
  apply actualCyclicSubspace_of_resolvent_mem N f
  rw [actualGammaResolvent_shift_friedrichs]
  exact hu

/-- Every ACTUAL unbounded graph pair with cyclic input comes from a
scalar forcing h. In particular its output is cyclic as a conclusion. -/
theorem actualGammaFriedrichs_cyclic_reverse_graph (N : ℕ) [NeZero N]
    (f : QuotientL2 N) {u v : QuotientL2 N}
    (hu : u∈actualCyclicSubspace N f) (huv : (u,v)∈(actualGammaFriedrichs N).graph) :
    ∃ h : ActualCyclicScalarL2 N f,
      u=actualCyclicSynthesis N f (actualCyclicCoordinate N f h) ∧
      v=actualCyclicSynthesis N f (h-actualCyclicCoordinate N f h) := by
  have hR := (actualGammaFriedrichs_mem_graph_iff N).mp huv
  have hforcing : u+v∈actualCyclicSubspace N f :=
    actualCyclicSubspace_of_resolvent_mem N f (u+v) (by rw [hR]; exact hu)
  let h := (actualCyclicRepresentation N f).symm ⟨u+v,hforcing⟩
  have hsyn : actualCyclicSynthesis N f h=u+v :=
    congrArg Subtype.val ((actualCyclicRepresentation N f).apply_symm_apply ⟨u+v,hforcing⟩)
  have hfirst : actualCyclicSynthesis N f (actualCyclicCoordinate N f h)=u := by
    rw [actualCyclicSynthesis_intertwine,hsyn,hR]
  have hsecond : actualCyclicSynthesis N f (h-actualCyclicCoordinate N f h)=v := by
    rw [map_sub,hsyn,hfirst]
    abel
  exact ⟨h,hfirst.symm,hsecond.symm⟩

/-- EXACT cyclic restriction of the ACTUAL Gamma0 unbounded graph. -/
theorem actualGammaFriedrichs_cyclic_graph_iff (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (u v : QuotientL2 N) :
    (u∈actualCyclicSubspace N f ∧ (u,v)∈(actualGammaFriedrichs N).graph) ↔
      ∃ h : ActualCyclicScalarL2 N f,
        u=actualCyclicSynthesis N f (actualCyclicCoordinate N f h) ∧
        v=actualCyclicSynthesis N f (h-actualCyclicCoordinate N f h) := by
  constructor
  · rintro ⟨hu,huv⟩
    exact actualGammaFriedrichs_cyclic_reverse_graph N f hu huv
  · rintro ⟨h,rfl,rfl⟩
    exact ⟨actualCyclicSynthesis_mem N f _,actualGammaFriedrichs_cyclic_forward_graph N f h⟩

theorem actualCyclicCoordinate_injective (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    Function.Injective (actualCyclicCoordinate N f) := by
  intro h k hhk
  apply actualCyclicSynthesis_injective N f
  apply actualGammaResolvent_injective N
  rw [← actualCyclicSynthesis_intertwine,← actualCyclicSynthesis_intertwine,hhk]

/-- Native inverse-coordinate-minus-identity on the actual scalar L2,
with domain range M_t; lambda-integrability is a separately owned stage. -/
def actualCyclicInverseShift (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    ActualCyclicScalarL2 N f→ₗ.[ℂ]ActualCyclicScalarL2 N f :=
  friedrichsR (actualCyclicCoordinate N f)

theorem actualCyclicInverseShift_domain (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    (actualCyclicInverseShift N f).domain=(actualCyclicCoordinate N f).range :=
  friedrichsR_domain (actualCyclicCoordinate N f)

theorem actualCyclicInverseShift_mem_graph_iff (N : ℕ) [NeZero N]
    (f : QuotientL2 N) {a b : ActualCyclicScalarL2 N f} :
    (a,b)∈(actualCyclicInverseShift N f).graph ↔ actualCyclicCoordinate N f (a+b)=a :=
  friedrichsR_mem_graph_iff (actualCyclicCoordinate N f) (actualCyclicCoordinate_injective N f)

/-- Exact native operator-graph conjugacy, preserving the actual physical
quotient space and the actual scalar-measure quotient space. -/
theorem actualGammaFriedrichs_graph_unitary_iff (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (a b : ActualCyclicScalarL2 N f) :
    (actualCyclicSynthesis N f a,actualCyclicSynthesis N f b)∈(actualGammaFriedrichs N).graph ↔
      (a,b)∈(actualCyclicInverseShift N f).graph := by
  rw [actualGammaFriedrichs_mem_graph_iff,actualCyclicInverseShift_mem_graph_iff]
  have hinter : actualGammaResolvent N (actualCyclicSynthesis N f a+actualCyclicSynthesis N f b)=
      actualCyclicSynthesis N f (actualCyclicCoordinate N f (a+b)) := by
    rw [← map_add,actualCyclicSynthesis_intertwine]
  rw [hinter]
  exact (actualCyclicSynthesis_injective N f).eq_iff

end
end ImbalancedChen.Part3.Gamma0ActualCyclicFriedrichsReverse20261025a
