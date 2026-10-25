import ImbalancedChen.Part3Gamma0ActualFriedrichsOperator
import ImbalancedChen.Part3GenericResolventGlobalSpectralAssembly

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The ACTUAL Gamma0 global scalar spectral Hilbert-sum model, with an exact
NATIVE UNBOUNDED Friedrichs graph, domain and action conjugacy. The generic
Zorn/orthogonal-total-family unitary is instantiated at the actual physical
Gamma0 R=J J*. No countability, totality, unitary or diagonalization input
is assumed. The diagonal bounded coordinate map is proved injective from
the actual unitary and actual R-injectivity.

Its native inverse-minus-identity operator is then genuinely self-adjoint,
closed, nonnegative and densely defined, with exact domain range diagonalR.
The ACTUAL physical Friedrichs graph is proved equivalent in BOTH directions
to that native global graph; physical and scalar domain points and actions
are explicitly transported. This is more than a bounded-R alias. Fiberwise
lambda integrability and the sum-of-square domain are the next separate
stage; no hGlobalLambdaDomain premise occurs here.
-/

namespace ImbalancedChen.Part3.Gamma0ActualGlobalFriedrichsGraph20261025a

noncomputable section
open Set MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualFriedrichsOperator20261025a
open GenericResolventGlobalSpectralAssembly20261025a
open GenericFriedrichsOperator20261025a

abbrev ActualSpectralIndex (N : ℕ) [NeZero N] :=
  SpectralIndex (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)

abbrev ActualSpectralFiber (N : ℕ) [NeZero N] (i : ActualSpectralIndex N) :=
  SpectralFiber (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) i

abbrev ActualSpectralSum (N : ℕ) [NeZero N] :=
  SpectralSum (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)

def actualGlobalSpectralUnitary (N : ℕ) [NeZero N] :
    ActualSpectralSum N≃ₗᵢ[ℂ]QuotientL2 N :=
  spectralUnitary (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)

def actualGlobalDiagonalResolvent (N : ℕ) [NeZero N] :
    ActualSpectralSum N→L[ℂ]ActualSpectralSum N :=
  diagonalResolvent (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)

theorem actualGlobalSpectralUnitary_intertwine (N : ℕ) [NeZero N]
    (a : ActualSpectralSum N) :
    actualGlobalSpectralUnitary N (actualGlobalDiagonalResolvent N a)=
      actualGammaResolvent N (actualGlobalSpectralUnitary N a) :=
  spectralUnitary_intertwine (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N) a

theorem actualGlobalSpectral_reconstruction (N : ℕ) [NeZero N] (u : QuotientL2 N) :
    actualGlobalSpectralUnitary N ((actualGlobalSpectralUnitary N).symm u)=u :=
  (actualGlobalSpectralUnitary N).apply_symm_apply u

/-- The actual bounded coordinate map is injective; this is not a
zero-coordinate or inverse-domain assumption. -/
theorem actualGlobalDiagonalResolvent_injective (N : ℕ) [NeZero N] :
    Function.Injective (actualGlobalDiagonalResolvent N) := by
  intro a b hab
  apply (actualGlobalSpectralUnitary N).injective
  apply actualGammaResolvent_injective N
  rw [← actualGlobalSpectralUnitary_intertwine,← actualGlobalSpectralUnitary_intertwine,hab]

theorem actualGlobalDiagonalResolvent_symmetric (N : ℕ) [NeZero N]
    (a b : ActualSpectralSum N) :
    inner ℂ (actualGlobalDiagonalResolvent N a) b=
      inner ℂ a (actualGlobalDiagonalResolvent N b) := by
  calc
    _ = inner ℂ (actualGlobalSpectralUnitary N (actualGlobalDiagonalResolvent N a))
        (actualGlobalSpectralUnitary N b) :=
      ((actualGlobalSpectralUnitary N).toLinearIsometry.inner_map_map _ _).symm
    _ = inner ℂ (actualGammaResolvent N (actualGlobalSpectralUnitary N a))
        (actualGlobalSpectralUnitary N b) := by rw [actualGlobalSpectralUnitary_intertwine]
    _ = inner ℂ (actualGlobalSpectralUnitary N a)
        (actualGammaResolvent N (actualGlobalSpectralUnitary N b)) :=
      actualGammaResolvent_symmetric N _ _
    _ = inner ℂ (actualGlobalSpectralUnitary N a)
        (actualGlobalSpectralUnitary N (actualGlobalDiagonalResolvent N b)) := by
      rw [actualGlobalSpectralUnitary_intertwine]
    _ = _ := (actualGlobalSpectralUnitary N).toLinearIsometry.inner_map_map _ _

theorem actualGlobalDiagonalResolvent_selfAdjoint (N : ℕ) [NeZero N] :
    IsSelfAdjoint (actualGlobalDiagonalResolvent N) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (actualGlobalDiagonalResolvent_symmetric N)

theorem actualGlobalDiagonalResolvent_opNorm_le_one (N : ℕ) [NeZero N] :
    ‖actualGlobalDiagonalResolvent N‖≤1 :=
  (diagonalResolvent_opNorm_le (actualGammaResolvent N) (actualGammaResolvent_selfAdjoint N)).trans
    (actualGammaResolvent_opNorm_le_one N)

theorem actualGlobalDiagonalResolvent_firm (N : ℕ) [NeZero N] (a : ActualSpectralSum N) :
    ‖actualGlobalDiagonalResolvent N a‖^2≤
      (inner ℂ a (actualGlobalDiagonalResolvent N a)).re := by
  have hh := actualGammaResolvent_firm N (actualGlobalSpectralUnitary N a)
  rw [← actualGlobalSpectralUnitary_intertwine,
    (actualGlobalSpectralUnitary N).norm_map,
    (actualGlobalSpectralUnitary N).toLinearIsometry.inner_map_map] at hh
  exact hh

/-- The genuine native unbounded global model, on the actual unrestricted
Hilbert sum of the actual Gamma0 scalar-measure fibers. -/
def actualGlobalFriedrichsModel (N : ℕ) [NeZero N] :
    ActualSpectralSum N→ₗ.[ℂ]ActualSpectralSum N :=
  friedrichsR (actualGlobalDiagonalResolvent N)

theorem actualGlobalFriedrichsModel_domain (N : ℕ) [NeZero N] :
    (actualGlobalFriedrichsModel N).domain=(actualGlobalDiagonalResolvent N).range :=
  friedrichsR_domain (actualGlobalDiagonalResolvent N)

theorem actualGlobalFriedrichsModel_mem_graph_iff (N : ℕ) [NeZero N]
    {a b : ActualSpectralSum N} :
    (a,b)∈(actualGlobalFriedrichsModel N).graph ↔ actualGlobalDiagonalResolvent N (a+b)=a :=
  friedrichsR_mem_graph_iff (actualGlobalDiagonalResolvent N)
    (actualGlobalDiagonalResolvent_injective N)

theorem actualGlobalFriedrichsModel_isClosed (N : ℕ) [NeZero N] :
    (actualGlobalFriedrichsModel N).IsClosed :=
  friedrichsR_isClosed (actualGlobalDiagonalResolvent N) (actualGlobalDiagonalResolvent_injective N)

theorem actualGlobalFriedrichsModel_isSelfAdjoint (N : ℕ) [NeZero N] :
    IsSelfAdjoint (actualGlobalFriedrichsModel N) :=
  friedrichsR_isSelfAdjoint (actualGlobalDiagonalResolvent N)
    (actualGlobalDiagonalResolvent_selfAdjoint N) (actualGlobalDiagonalResolvent_injective N)

theorem actualGlobalFriedrichsModel_dense_domain (N : ℕ) [NeZero N] :
    Dense ((actualGlobalFriedrichsModel N).domain:Set (ActualSpectralSum N)) :=
  friedrichsR_dense_domain (actualGlobalDiagonalResolvent N)
    (actualGlobalDiagonalResolvent_selfAdjoint N) (actualGlobalDiagonalResolvent_injective N)

theorem actualGlobalFriedrichsModel_nonneg (N : ℕ) [NeZero N]
    (a : (actualGlobalFriedrichsModel N).domain) :
    0≤(inner ℂ (a:ActualSpectralSum N) (actualGlobalFriedrichsModel N a)).re :=
  friedrichsR_nonneg (actualGlobalDiagonalResolvent N) (actualGlobalDiagonalResolvent_injective N)
    (actualGlobalDiagonalResolvent_firm N) a

/-- EXACT two-way graph conjugacy for the ACTUAL physical unbounded
operator. The full-domain statement is proved from its native graph. -/
theorem actualGlobalFriedrichs_graph_unitary_iff (N : ℕ) [NeZero N]
    (a b : ActualSpectralSum N) :
    (actualGlobalSpectralUnitary N a,actualGlobalSpectralUnitary N b)∈
        (actualGammaFriedrichs N).graph ↔ (a,b)∈(actualGlobalFriedrichsModel N).graph := by
  rw [actualGammaFriedrichs_mem_graph_iff,actualGlobalFriedrichsModel_mem_graph_iff]
  have heq : actualGammaResolvent N (actualGlobalSpectralUnitary N a+actualGlobalSpectralUnitary N b)=
      actualGlobalSpectralUnitary N (actualGlobalDiagonalResolvent N (a+b)) := by
    rw [← map_add,actualGlobalSpectralUnitary_intertwine]
  rw [heq]
  exact (actualGlobalSpectralUnitary N).injective.eq_iff

theorem actualGlobalFriedrichs_graph_coordinates_iff (N : ℕ) [NeZero N]
    (u v : QuotientL2 N) :
    (u,v)∈(actualGammaFriedrichs N).graph ↔
      ((actualGlobalSpectralUnitary N).symm u,(actualGlobalSpectralUnitary N).symm v)∈
        (actualGlobalFriedrichsModel N).graph := by
  have hh := actualGlobalFriedrichs_graph_unitary_iff N
    ((actualGlobalSpectralUnitary N).symm u) ((actualGlobalSpectralUnitary N).symm v)
  simpa only [LinearIsometryEquiv.apply_symm_apply] using hh

theorem actualGlobalFriedrichs_domain_unitary_iff (N : ℕ) [NeZero N]
    (a : ActualSpectralSum N) :
    actualGlobalSpectralUnitary N a∈(actualGammaFriedrichs N).domain ↔
      a∈(actualGlobalFriedrichsModel N).domain := by
  constructor
  · intro ha
    obtain ⟨v,hv⟩ := LinearPMap.mem_domain_iff.mp ha
    apply LinearPMap.mem_domain_iff.mpr
    refine ⟨(actualGlobalSpectralUnitary N).symm v,?_⟩
    apply (actualGlobalFriedrichs_graph_unitary_iff N a _).mp
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact hv
  · intro ha
    obtain ⟨b,hb⟩ := LinearPMap.mem_domain_iff.mp ha
    exact LinearPMap.mem_domain_of_mem_graph ((actualGlobalFriedrichs_graph_unitary_iff N a b).mpr hb)

theorem actualGlobalFriedrichs_domain_coordinates_iff (N : ℕ) [NeZero N]
    (u : QuotientL2 N) :
    u∈(actualGammaFriedrichs N).domain ↔
      (actualGlobalSpectralUnitary N).symm u∈(actualGlobalFriedrichsModel N).domain := by
  have hh := actualGlobalFriedrichs_domain_unitary_iff N ((actualGlobalSpectralUnitary N).symm u)
  simpa only [LinearIsometryEquiv.apply_symm_apply] using hh

def actualGlobalPhysicalDomainPoint (N : ℕ) [NeZero N]
    (a : (actualGlobalFriedrichsModel N).domain) : (actualGammaFriedrichs N).domain :=
  ⟨actualGlobalSpectralUnitary N a,(actualGlobalFriedrichs_domain_unitary_iff N a).mpr a.property⟩

theorem actualGlobalFriedrichs_apply_unitary (N : ℕ) [NeZero N]
    (a : (actualGlobalFriedrichsModel N).domain) :
    actualGammaFriedrichs N (actualGlobalPhysicalDomainPoint N a)=
      actualGlobalSpectralUnitary N (actualGlobalFriedrichsModel N a) := by
  have hpair := (actualGlobalFriedrichs_graph_unitary_iff N a (actualGlobalFriedrichsModel N a)).mpr
    (LinearPMap.mem_graph (actualGlobalFriedrichsModel N) a)
  exact LinearPMap.mem_graph_snd_inj (actualGammaFriedrichs N)
    (LinearPMap.mem_graph _ (actualGlobalPhysicalDomainPoint N a)) hpair rfl

def actualGlobalModelDomainPoint (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) : (actualGlobalFriedrichsModel N).domain :=
  ⟨(actualGlobalSpectralUnitary N).symm u,
    (actualGlobalFriedrichs_domain_coordinates_iff N u).mp u.property⟩

theorem actualGlobalFriedrichs_apply_coordinates (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    actualGlobalFriedrichsModel N (actualGlobalModelDomainPoint N u)=
      (actualGlobalSpectralUnitary N).symm (actualGammaFriedrichs N u) := by
  have hpair := (actualGlobalFriedrichs_graph_coordinates_iff N u (actualGammaFriedrichs N u)).mp
    (LinearPMap.mem_graph (actualGammaFriedrichs N) u)
  exact LinearPMap.mem_graph_snd_inj (actualGlobalFriedrichsModel N)
    (LinearPMap.mem_graph _ (actualGlobalModelDomainPoint N u)) hpair rfl

end
end ImbalancedChen.Part3.Gamma0ActualGlobalFriedrichsGraph20261025a
