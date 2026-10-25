import ImbalancedChen.Part3Gamma0ActualCyclicFriedrichsReverse
import ImbalancedChen.Part3GenericResolventUnboundedMultiplication

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The ACTUAL Gamma0 cyclic Friedrichs operator has its TRUE unbounded
lambda=(1-t)/t multiplication domain in the actual scalar-measure L2
model. Domain membership is proved equivalent to MemLp(lambda*g), and
the actual physical action equals U(lambda*g). The actual graph is
identified with the corresponding a.e. multiplication graph.

The proof consumes the native cyclic inverse-coordinate graph and the
generic lambda theorem, whose zero-atom input was independently DERIVED
from true injectivity. No hLambdaDomain, assumed zero atom, bounded-R-only
alias, scalar moment supplier or global direct-sum representation is used.
-/

namespace ImbalancedChen.Part3.Gamma0ActualCyclicLambdaDomain20261025a

noncomputable section
open Set MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0ActualCyclicFriedrichsGraph20261025a
open Gamma0ActualCyclicFriedrichsReverse20261025a
open GenericResolventScalarMeasure20261025a
open GenericResolventUnboundedMultiplication20261025a

def actualCyclicCoordinates (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (u : actualCyclicSubspace N f) : ActualCyclicScalarL2 N f :=
  (actualCyclicRepresentation N f).symm u

theorem actualCyclicSynthesis_coordinates (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (u : actualCyclicSubspace N f) :
    actualCyclicSynthesis N f (actualCyclicCoordinates N f u)=(u:QuotientL2 N) :=
  congrArg Subtype.val ((actualCyclicRepresentation N f).apply_symm_apply u)

/-- Exact native-domain conjugacy, using the ACTUAL reverse graph rather
than assuming that bounded intertwining implies an unbounded domain. -/
theorem actualGammaFriedrichs_cyclic_domain_iff_native (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (a : ActualCyclicScalarL2 N f) :
    actualCyclicSynthesis N f a∈(actualGammaFriedrichs N).domain ↔
      a∈(actualCyclicInverseShift N f).domain := by
  constructor
  · intro ha
    obtain ⟨v,hv⟩ := LinearPMap.mem_domain_iff.mp ha
    obtain ⟨h,hh,_⟩ := actualGammaFriedrichs_cyclic_reverse_graph N f
      (actualCyclicSynthesis_mem N f a) hv
    have hae : a=actualCyclicCoordinate N f h := (actualCyclicSynthesis_injective N f) hh
    rw [hae,actualCyclicInverseShift_domain]
    exact ⟨h,rfl⟩
  · intro ha
    obtain ⟨b,hb⟩ := LinearPMap.mem_domain_iff.mp ha
    exact LinearPMap.mem_domain_of_mem_graph
      ((actualGammaFriedrichs_graph_unitary_iff N f a b).mpr hb)

/-- The actual unbounded Gamma0 graph is precisely the lambda-product
a.e. graph on this scalar-measure block. -/
theorem actualGammaFriedrichs_cyclic_graph_iff_lambda (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (a b : ActualCyclicScalarL2 N f) :
    (actualCyclicSynthesis N f a,actualCyclicSynthesis N f b)∈(actualGammaFriedrichs N).graph ↔
      b=ᵐ[scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f]
        lambdaProduct (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f a :=
  (actualGammaFriedrichs_graph_unitary_iff N f a b).trans
    (coordinateFriedrichs_mem_graph_iff (actualGammaResolvent N)
      (actualGammaResolvent_selfAdjoint N) (actualGammaResolvent_injective N) f)

/-- TRUE maximal multiplication-domain criterion for every vector in the
actual physical cyclic subspace. No integrability conclusion is assumed. -/
theorem actualGammaFriedrichs_cyclic_domain_iff_lambdaMemLp (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (u : actualCyclicSubspace N f) :
    (u:QuotientL2 N)∈(actualGammaFriedrichs N).domain ↔
      MemLp (lambdaProduct (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f
        (actualCyclicCoordinates N f u)) 2
        (scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f) := by
  rw [← actualCyclicSynthesis_coordinates N f u,
    actualGammaFriedrichs_cyclic_domain_iff_native]
  exact coordinateFriedrichs_domain_iff (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) (actualGammaResolvent_injective N) f _

/-- The actual Friedrichs output remains cyclic as a CONCLUSION from the
full reverse graph, not an assumed unbounded invariant-domain field. -/
theorem actualGammaFriedrichs_output_mem_cyclic (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (u : (actualGammaFriedrichs N).domain)
    (hu : (u:QuotientL2 N)∈actualCyclicSubspace N f) :
    actualGammaFriedrichs N u∈actualCyclicSubspace N f := by
  obtain ⟨h,_hh,hout⟩ := actualGammaFriedrichs_cyclic_reverse_graph N f hu
    (LinearPMap.mem_graph (actualGammaFriedrichs N) u)
  rw [hout]
  exact actualCyclicSynthesis_mem N f _

theorem actualGammaFriedrichs_cyclic_lambda_memLp (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (u : (actualGammaFriedrichs N).domain)
    (hu : (u:QuotientL2 N)∈actualCyclicSubspace N f) :
    MemLp (lambdaProduct (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f
      (actualCyclicCoordinates N f ⟨u,hu⟩)) 2
      (scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f) :=
  (actualGammaFriedrichs_cyclic_domain_iff_lambdaMemLp N f ⟨u,hu⟩).mp u.property

/-- Exact a.e. coordinate action of the actual native unbounded operator. -/
theorem actualGammaFriedrichs_cyclic_action_ae (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (u : (actualGammaFriedrichs N).domain)
    (hu : (u:QuotientL2 N)∈actualCyclicSubspace N f) :
    actualCyclicCoordinates N f
        ⟨actualGammaFriedrichs N u,actualGammaFriedrichs_output_mem_cyclic N f u hu⟩
      =ᵐ[scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f]
      lambdaProduct (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f
        (actualCyclicCoordinates N f ⟨u,hu⟩) := by
  apply (actualGammaFriedrichs_cyclic_graph_iff_lambda N f _ _).mp
  rw [actualCyclicSynthesis_coordinates,actualCyclicSynthesis_coordinates]
  exact LinearPMap.mem_graph (actualGammaFriedrichs N) u

/-- PHYSICAL action U(lambda*U^{-1}u), with its L2 membership already
proved from the actual domain. There is no hLambdaDomain input. -/
theorem actualGammaFriedrichs_cyclic_apply_lambda (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (u : (actualGammaFriedrichs N).domain)
    (hu : (u:QuotientL2 N)∈actualCyclicSubspace N f) :
    actualGammaFriedrichs N u=actualCyclicSynthesis N f
      (lambdaMultiply (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f
        (actualCyclicCoordinates N f ⟨u,hu⟩)
        (actualGammaFriedrichs_cyclic_lambda_memLp N f u hu)) := by
  let b := actualCyclicCoordinates N f
    ⟨actualGammaFriedrichs N u,actualGammaFriedrichs_output_mem_cyclic N f u hu⟩
  have hb := actualGammaFriedrichs_cyclic_action_ae N f u hu
  have heq : lambdaMultiply (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) f
      (actualCyclicCoordinates N f ⟨u,hu⟩)
      (actualGammaFriedrichs_cyclic_lambda_memLp N f u hu)=b := by
    apply Lp.ext
    exact (actualGammaFriedrichs_cyclic_lambda_memLp N f u hu).coeFn_toLp.trans hb.symm
  rw [heq]
  exact (actualCyclicSynthesis_coordinates N f
    ⟨actualGammaFriedrichs N u,actualGammaFriedrichs_output_mem_cyclic N f u hu⟩).symm

end
end ImbalancedChen.Part3.Gamma0ActualCyclicLambdaDomain20261025a
