import ImbalancedChen.Part3Gamma0ActualGlobalFriedrichsGraph
import ImbalancedChen.Part3GenericResolventGlobalUnboundedMultiplication

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The ACTUAL Gamma0 GLOBAL unbounded spectral multiplication model. The
native physical Friedrichs graph is exactly the fiberwise a.e. lambda
graph after the actual global unitary. Its TRUE full domain is equivalent
to L2 membership of every lambda-times-coordinate fiber AND Hilbert-sum
membership of those output fibers. No hGlobalLambdaDomain, zero-atom,
countability or spectral-decomposition premise is assumed.

The generic graph/domain theorem is instantiated at the genuine actual
Gamma0 physical R and then connected to the already proved actual native
unbounded graph conjugacy. This does not replace a domain proof with a
bounded-resolvent alias. Standard cusp/Eisenstein normalizations are not
part of this abstract scalar-measure model.
-/

namespace ImbalancedChen.Part3.Gamma0ActualGlobalLambdaDomain20261025a

noncomputable section
open Set MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0ActualGlobalFriedrichsGraph20261025a
open GenericResolventScalarMeasure20261025a
open GenericResolventUnboundedMultiplication20261025a
open GenericResolventGlobalUnboundedMultiplication20261025a

def actualGlobalSpectralCoordinates (N : ℕ) [NeZero N] (u : QuotientL2 N) :
    ActualSpectralSum N := (actualGlobalSpectralUnitary N).symm u

def actualGlobalLambdaProduct (N : ℕ) [NeZero N] (a : ActualSpectralSum N)
    (i : ActualSpectralIndex N) :
    GenericResolventScalarMeasure20261025a.ResolventSpectrum (actualGammaResolvent N)→ℂ :=
  lambdaProduct (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) (i:QuotientL2 N) (a i)

def actualGlobalFamilyLambdaDomain (N : ℕ) [NeZero N] (a : ActualSpectralSum N) : Prop :=
  FamilyLambdaDomain (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) a

def actualGlobalFamilyLambdaGraph (N : ℕ) [NeZero N] (a b : ActualSpectralSum N) : Prop :=
  FamilyLambdaGraph (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) a b

/-- The native global scalar model has the true fiberwise multiplication
graph, obtained without a zero-atom or domain supplier premise. -/
theorem actualGlobalModel_graph_iff_lambda (N : ℕ) [NeZero N]
    (a b : ActualSpectralSum N) :
    (a,b)∈(actualGlobalFriedrichsModel N).graph ↔ actualGlobalFamilyLambdaGraph N a b :=
  globalFriedrichs_mem_graph_iff_lambda (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) (actualGammaResolvent_injective N)

theorem actualGlobalModel_domain_iff_lambda (N : ℕ) [NeZero N]
    (a : ActualSpectralSum N) :
    a∈(actualGlobalFriedrichsModel N).domain ↔ actualGlobalFamilyLambdaDomain N a :=
  globalFriedrichs_domain_iff (actualGammaResolvent N)
    (actualGammaResolvent_selfAdjoint N) (actualGammaResolvent_injective N) a

/-- EXACT graph of the ACTUAL physical unbounded Gamma0 Friedrichs
operator in its global, genuinely onto scalar spectral coordinates. -/
theorem actualGammaFriedrichs_global_graph_iff_lambda (N : ℕ) [NeZero N]
    (u v : QuotientL2 N) :
    (u,v)∈(actualGammaFriedrichs N).graph ↔
      actualGlobalFamilyLambdaGraph N (actualGlobalSpectralCoordinates N u)
        (actualGlobalSpectralCoordinates N v) :=
  (actualGlobalFriedrichs_graph_coordinates_iff N u v).trans
    (actualGlobalModel_graph_iff_lambda N _ _)

/-- The true physical operator domain, with BOTH local L2 and global
Hilbert-sum output conditions retained. This is not an assumed domain. -/
theorem actualGammaFriedrichs_global_domain_iff_lambda (N : ℕ) [NeZero N]
    (u : QuotientL2 N) :
    u∈(actualGammaFriedrichs N).domain ↔
      actualGlobalFamilyLambdaDomain N (actualGlobalSpectralCoordinates N u) :=
  (actualGlobalFriedrichs_domain_coordinates_iff N u).trans
    (actualGlobalModel_domain_iff_lambda N _)

/-- Explicit maximal physical-domain criterion: EVERY fiber product is
in its true scalar L2, AND the squared output norms have a finite sum.
The index is unrestricted; there is no countable-index hypothesis. -/
theorem actualGammaFriedrichs_global_domain_iff_sum_norm_sq (N : ℕ) [NeZero N]
    (u : QuotientL2 N) :
    u∈(actualGammaFriedrichs N).domain ↔
      ∃ h : ∀ i : ActualSpectralIndex N,
          MemLp (actualGlobalLambdaProduct N (actualGlobalSpectralCoordinates N u) i) 2
            (scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
              (i:QuotientL2 N)),
        Summable (fun i : ActualSpectralIndex N =>
          ‖(h i).toLp (actualGlobalLambdaProduct N (actualGlobalSpectralCoordinates N u) i)‖^2) :=
  (actualGlobalFriedrichs_domain_coordinates_iff N u).trans
    (globalFriedrichs_domain_iff_sum_norm_sq (actualGammaResolvent N)
      (actualGammaResolvent_selfAdjoint N) (actualGammaResolvent_injective N) _)

/-- Actual domain membership CONSTRUCTS the local integrability proofs;
there is no user-supplied lambda-domain field. -/
def actualGlobalDomainFiberMemLp (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    ∀ i : ActualSpectralIndex N,
      MemLp (actualGlobalLambdaProduct N (actualGlobalSpectralCoordinates N u) i) 2
        (scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)
          (i:QuotientL2 N)) :=
  Classical.choose ((actualGammaFriedrichs_global_domain_iff_lambda N u).mp u.property)

theorem actualGlobalDomainOutputs_memℓp (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    Memℓp (fun i : ActualSpectralIndex N =>
      (actualGlobalDomainFiberMemLp N u i).toLp
        (actualGlobalLambdaProduct N (actualGlobalSpectralCoordinates N u) i)) 2 :=
  Classical.choose_spec ((actualGammaFriedrichs_global_domain_iff_lambda N u).mp u.property)

/-- The global lambda output vector itself, with genuine global lp
membership derived from the actual native physical domain. -/
def actualGlobalLambdaCoordinates (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) : ActualSpectralSum N :=
  ⟨fun i => (actualGlobalDomainFiberMemLp N u i).toLp
    (actualGlobalLambdaProduct N (actualGlobalSpectralCoordinates N u) i),
    actualGlobalDomainOutputs_memℓp N u⟩

/-- Actual unbounded action on EVERY fiber, almost everywhere in that
fiber's true scalar measure. The output family is already in global L2. -/
theorem actualGammaFriedrichs_global_action_ae (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) (i : ActualSpectralIndex N) :
    (actualGlobalSpectralCoordinates N (actualGammaFriedrichs N u)) i =ᵐ[
      scalarMeasure (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) (i:QuotientL2 N)]
      actualGlobalLambdaProduct N (actualGlobalSpectralCoordinates N u) i := by
  have hg := (actualGammaFriedrichs_global_graph_iff_lambda N u (actualGammaFriedrichs N u)).mp
    (LinearPMap.mem_graph (actualGammaFriedrichs N) u)
  exact hg i

/-- The actual unbounded output equals the CONSTRUCTED global lambda
family in the true Hilbert sum, not just formally on individual fibers. -/
theorem actualGammaFriedrichs_global_action_coordinates (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    actualGlobalSpectralCoordinates N (actualGammaFriedrichs N u)=actualGlobalLambdaCoordinates N u := by
  apply lp.ext
  intro i
  apply Lp.ext
  exact (actualGammaFriedrichs_global_action_ae N u i).trans
    (actualGlobalDomainFiberMemLp N u i).coeFn_toLp.symm

/-- ACTUAL physical operator action by the genuine global unbounded
lambda multiplication family, with both L2 and square-sum domain proved. -/
theorem actualGammaFriedrichs_global_apply_lambda (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    actualGammaFriedrichs N u=actualGlobalSpectralUnitary N (actualGlobalLambdaCoordinates N u) := by
  calc
    _ = actualGlobalSpectralUnitary N
        (actualGlobalSpectralCoordinates N (actualGammaFriedrichs N u)) :=
      ((actualGlobalSpectralUnitary N).apply_symm_apply _).symm
    _ = _ := by rw [actualGammaFriedrichs_global_action_coordinates]

end
end ImbalancedChen.Part3.Gamma0ActualGlobalLambdaDomain20261025a
