import ImbalancedChen.Part3GammaActualMinimalDefectVanishes
import ImbalancedChen.Part3Gamma0ArbitrarySmoothWeakGradient

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Every vector in the native actual adjoint domain belongs to the ORIGINAL
actual completed energy form domain. This follows from proved native
self-adjointness and equality with the actual Friedrichs operator, not
from a form-membership input. Its existing completed local gradients have
the literal arbitrary compact smooth weak derivative identities. -/

namespace ImbalancedChen.Part3.GammaActualAdjointFormRegularity20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMaassClosedOperator20261025a
open GammaActualMinimalDefectVanishes20261026b Gamma0ActualFriedrichsOperator20261025a
open Gamma0PhysicalClosedDirichletForm20261025a Gamma0ArbitrarySmoothWeakGradient20261026b
open Gamma0EnergyCompactGradientExtension20261025a ArbitraryCompactFirstGradientIBP20261026b
open CompactC2ProductMollifier20261026a Gamma0QuotientCellPushforward20261025a
open Gamma0EnergyGeometricWeakGradient20261025a Gamma0CompactTensorPoincareC2Core20261025a

theorem actual_adjoint_eq_friedrichs (N : ℕ) [NeZero N] :
    (actualClosedGammaMaass N).adjoint = actualGammaFriedrichs N :=
  (LinearPMap.isSelfAdjoint_def.mp (actual_minimal_closure_isSelfAdjoint N)).trans
    (actual_minimal_closure_eq_friedrichs N)

/-- Genuine inclusion for every native adjoint-domain vector. -/
theorem actual_adjoint_domain_le_energyFormDomain (N : ℕ) [NeZero N] :
    (actualClosedGammaMaass N).adjoint.domain ≤ actualEnergyFormDomain N := by
  rw [actual_adjoint_eq_friedrichs N]
  exact actualGammaFriedrichs_domain_le_formDomain N

def actualAdjointFormVector (N : ℕ) [NeZero N]
    (u : (actualClosedGammaMaass N).adjoint.domain) : actualEnergyFormDomain N :=
  ⟨u, actual_adjoint_domain_le_energyFormDomain N u.property⟩

theorem actual_adjoint_graph_input_mem_form (N : ℕ) [NeZero N]
    {f w : QuotientL2 N} (hfw : (f,w) ∈ (actualClosedGammaMaass N).adjoint.graph) :
    f ∈ actualEnergyFormDomain N := by
  obtain ⟨u, hu, _⟩ := LinearPMap.mem_graph_iff.mp hfw
  rw [← hu]
  exact actual_adjoint_domain_le_energyFormDomain N u.property

/-- Every actual adjoint-domain vector has the actual completed local
gradient representation against every compact smooth positive test. -/
theorem actual_adjoint_arbitrary_smooth_weak_derivative (N : ℕ) [NeZero N]
    (u : (actualClosedGammaMaass N).adjoint.domain)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (vertical : Bool)
    {ψ : Plane → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ positiveChart) (hTK : chartTestSupport ψ ⊆ K) :
    (∫ z in K, star (directional (coordinateDirection vertical) ψ (z.re,z.im)) *
      (u : QuotientL2 N) (orbitProjection N z) * (z.im : ℂ)^2) =
      -(∫ z in K, star (ψ (z.re,z.im)) *
        (completedCompactGradient N hK (actualEnergyLift N (actualAdjointFormVector N u))) z
          (firstCoordinate vertical) * (z.im : ℂ)) :=
  actual_form_arbitrary_smooth_weak_derivative N hK vertical hψ hc hs hTK
    (actualAdjointFormVector N u)

end
end ImbalancedChen.Part3.GammaActualAdjointFormRegularity20261026b
