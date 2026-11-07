import ImbalancedChen.Part3Gamma0ActualFriedrichsOperator
import ImbalancedChen.Part3GenericResolventCyclicIntertwining

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

An ACTUAL cyclic scalar-measure representation on the physical Gamma0
quotient Hilbert space, with a genuine UNBOUNDED Friedrichs graph binding.
For every h in the actual scalar-measure L2 space, U(M_t h)=R(U h) lies in
the native actual Friedrichs domain and A_F U(M_t h)=U(h-M_t h).

The unitary and bounded coordinate multiplier are instantiated from their
proved generic suppliers at the genuine actual physical R=J J*. The new
graph/domain/action assertions use the ACTUAL native unbounded operator,
rather than only renaming a unitary. No zero-atom, lambda-integrability,
density or spectral-graph conclusion is assumed as an input. Reverse graph
description and lambda-domain multiplication are separate steps.
-/

namespace ImbalancedChen.Part3.Gamma0ActualCyclicFriedrichsGraph20261025a

noncomputable section
open Set MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualFriedrichsOperator20261025a
open GenericResolventScalarMeasure20261025a
open GenericResolventCyclicL2Representation20261025a
open GenericResolventCyclicIntertwining20261025a

abbrev ActualCyclicScalarL2 (N : ℕ) [NeZero N] (f : QuotientL2 N) :=
  ScalarL2 (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f

def actualCyclicSubspace (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    Submodule ℂ (QuotientL2 N) :=
  cyclicSubspace (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f

def actualCyclicRepresentation (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    ActualCyclicScalarL2 N f≃ₗᵢ[ℂ]actualCyclicSubspace N f :=
  cyclicRepresentation (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f

def actualCyclicSynthesis (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    ActualCyclicScalarL2 N f→L[ℂ]QuotientL2 N :=
  cyclicExtension (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f

def actualCyclicCoordinate (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    ActualCyclicScalarL2 N f→L[ℂ]ActualCyclicScalarL2 N f :=
  coordinateMultiplier (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f

theorem actualCyclicRepresentation_coe (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (h : ActualCyclicScalarL2 N f) :
    (actualCyclicRepresentation N f h:QuotientL2 N)=actualCyclicSynthesis N f h := rfl

theorem actualCyclicSynthesis_mem (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (h : ActualCyclicScalarL2 N f) :
    actualCyclicSynthesis N f h∈actualCyclicSubspace N f :=
  (actualCyclicRepresentation N f h).property

theorem actualCyclicSynthesis_norm (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (h : ActualCyclicScalarL2 N f) :
    ‖actualCyclicSynthesis N f h‖=‖h‖ :=
  cyclicExtension_norm (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f h

theorem actualCyclicSynthesis_intertwine (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (h : ActualCyclicScalarL2 N f) :
    actualCyclicSynthesis N f (actualCyclicCoordinate N f h)=
      actualGammaResolvent N (actualCyclicSynthesis N f h) :=
  cyclicExtension_intertwine (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) f h

/-- The multiplier is literally t*h in the genuine actual scalar measure,
not an abstract operator with a proposed spectral coordinate. -/
theorem actualCyclicCoordinate_coe_ae (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (h : ActualCyclicScalarL2 N f) :
    actualCyclicCoordinate N f h =ᵐ[
      scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f]
      (fun t : ResolventSpectrum (actualGammaResolvent N) => ((t:ℝ):ℂ)*h t) :=
  coordinateMultiplier_coe_ae (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) f h

/-- An actual native-domain vector constructed from EVERY scalar L2 h. -/
def actualCyclicFriedrichsPoint (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (h : ActualCyclicScalarL2 N f) :
    (actualGammaFriedrichs N).domain :=
  ⟨actualCyclicSynthesis N f (actualCyclicCoordinate N f h),by
    rw [actualGammaFriedrichs_domain]
    exact ⟨actualCyclicSynthesis N f h,(actualCyclicSynthesis_intertwine N f h).symm⟩⟩

theorem actualCyclicFriedrichsPoint_coe (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (h : ActualCyclicScalarL2 N f) :
    (actualCyclicFriedrichsPoint N f h:QuotientL2 N)=
      actualCyclicSynthesis N f (actualCyclicCoordinate N f h) := rfl

theorem actualCyclicFriedrichsPoint_eq_resolventPoint (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (h : ActualCyclicScalarL2 N f) :
    actualCyclicFriedrichsPoint N f h=actualResolventPoint N (actualCyclicSynthesis N f h) := by
  apply Subtype.ext
  exact actualCyclicSynthesis_intertwine N f h

/-- The actual unbounded Friedrichs action is bound to the literal
scalar coordinate graph. This is a DOMAIN and ACTION theorem, not an alias. -/
theorem actualGammaFriedrichs_apply_cyclicPoint (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (h : ActualCyclicScalarL2 N f) :
    actualGammaFriedrichs N (actualCyclicFriedrichsPoint N f h)=
      actualCyclicSynthesis N f (h-actualCyclicCoordinate N f h) := by
  rw [actualCyclicFriedrichsPoint_eq_resolventPoint,actualGammaFriedrichs_apply_resolvent,
    map_sub,actualCyclicSynthesis_intertwine]

/-- Full forward unbounded graph binding on the SAME actual quotient H. -/
theorem actualGammaFriedrichs_cyclic_forward_graph (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (h : ActualCyclicScalarL2 N f) :
    (actualCyclicSynthesis N f (actualCyclicCoordinate N f h),
      actualCyclicSynthesis N f (h-actualCyclicCoordinate N f h))∈
        (actualGammaFriedrichs N).graph := by
  have hh := LinearPMap.mem_graph (actualGammaFriedrichs N) (actualCyclicFriedrichsPoint N f h)
  rw [actualGammaFriedrichs_apply_cyclicPoint] at hh
  exact hh

/-- The same actual unbounded graph statement through the genuine cyclic
unitary onto the actual closed cyclic physical subspace. -/
theorem actualGammaFriedrichs_unitary_forward_graph (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (h : ActualCyclicScalarL2 N f) :
    ((actualCyclicRepresentation N f (actualCyclicCoordinate N f h):QuotientL2 N),
      (actualCyclicRepresentation N f (h-actualCyclicCoordinate N f h):QuotientL2 N))∈
        (actualGammaFriedrichs N).graph :=
  actualGammaFriedrichs_cyclic_forward_graph N f h

end
end ImbalancedChen.Part3.Gamma0ActualCyclicFriedrichsGraph20261025a
