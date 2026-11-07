import ImbalancedChen.Part3GlobalFrickeClosedEnergyAction

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO FORMAL CREDIT.

The genuinely constructed Fricke energy isometry and its physical
intertwining identity transform the ACTUAL completed Riesz variational
problem. Actual Riesz uniqueness then proves global resolvent covariance.
The existing exact native Friedrichs graph equation R(u+v)=u yields the
full Friedrichs graph/domain action and operator intertwining. This does
not identify the minimal and Friedrichs domains or assume ESA, form
invariance, Riesz covariance, or a global operator-domain action.
-/

noncomputable section

namespace ImbalancedChen.Part3.GlobalFrickeFriedrichsIntertwining20261026b

open Set MeasureTheory
open ImbalancedChen.Part3.ActualHeckeSecondL220261026b
open ImbalancedChen.Part3.GlobalFrickeHilbertInvolution20261026b
open ImbalancedChen.Part3.GlobalFrickeClosedEnergyAction20261026b
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualEnergyCompletion20261025a
open ImbalancedChen.Part3.Gamma0ActualWeakRieszResolvent20261025a
open ImbalancedChen.Part3.Gamma0ActualFriedrichsOperator20261025a

theorem frickeL2_inner_flip (N : ℕ) [NeZero N] (hN : 0 < N) (f g : QuotientL2 N) :
    inner ℂ (frickeL2 N hN f) g = inner ℂ f (frickeL2 N hN g) := by
  simpa only [frickeL2_involutive N hN g] using
    (frickeL2 N hN).inner_map_map f (frickeL2 N hN g)

theorem energyFricke_inner_flip (N : ℕ) [NeZero N] (hN : 0 < N) (d e : EnergyCompletion N) :
    inner ℂ d (energyFricke N hN e) = inner ℂ (energyFricke N hN d) e := by
  simpa only [energyFricke_involutive N hN d] using
    energyFricke_inner N hN (energyFricke N hN d) e

/-- Transform the actual completed variational problem, then use its
proved uniqueness. No generic Riesz-commutation supplier is assumed. -/
theorem actualRieszLift_fricke (N : ℕ) [NeZero N] (hN : 0 < N) (f : QuotientL2 N) :
    energyFricke N hN (actualRieszLift N f) = actualRieszLift N (frickeL2 N hN f) := by
  apply actualRieszLift_unique N (frickeL2 N hN f)
  intro d
  calc
    inner ℂ d (energyFricke N hN (actualRieszLift N f)) =
        inner ℂ (energyFricke N hN d) (actualRieszLift N f) := energyFricke_inner_flip N hN _ _
    _ = inner ℂ (physicalProjection N (energyFricke N hN d)) f := actualRieszLift_weak N f _
    _ = inner ℂ (frickeL2 N hN (physicalProjection N d)) f := by rw [energyFricke_physical]
    _ = inner ℂ (physicalProjection N d) (frickeL2 N hN f) := frickeL2_inner_flip N hN _ _

/-- Global covariance of the genuine canonical physical resolvent J J*. -/
theorem actualGammaResolvent_fricke (N : ℕ) [NeZero N] (hN : 0 < N) (f : QuotientL2 N) :
    frickeL2 N hN (actualGammaResolvent N f) = actualGammaResolvent N (frickeL2 N hN f) := by
  rw [actualGammaResolvent_apply, actualGammaResolvent_apply,
    ← energyFricke_physical, actualRieszLift_fricke]

theorem fricke_friedrichsGraph_action (N : ℕ) [NeZero N] (hN : 0 < N)
    {f g : QuotientL2 N} (hfg : (f,g) ∈ (actualGammaFriedrichs N).graph) :
    (frickeL2 N hN f, frickeL2 N hN g) ∈ (actualGammaFriedrichs N).graph := by
  apply (actualGammaFriedrichs_mem_graph_iff N).mpr
  rw [← (frickeL2 N hN).map_add f g, ← actualGammaResolvent_fricke N hN]
  exact congrArg (frickeL2 N hN) ((actualGammaFriedrichs_mem_graph_iff N).mp hfg)

/-- The FULL actual Friedrichs domain, derived from its actual graph,
not inferred from invariance of the smaller minimal domain. -/
theorem fricke_friedrichsDomain_action (N : ℕ) [NeZero N] (hN : 0 < N)
    {f : QuotientL2 N} (hf : f ∈ (actualGammaFriedrichs N).domain) :
    frickeL2 N hN f ∈ (actualGammaFriedrichs N).domain := by
  obtain ⟨g, hg⟩ := LinearPMap.mem_domain_iff.mp hf
  exact LinearPMap.mem_domain_iff.mpr ⟨frickeL2 N hN g, fricke_friedrichsGraph_action N hN hg⟩

def friedrichsFrickeDomain (N : ℕ) [NeZero N] (hN : 0 < N)
    (u : (actualGammaFriedrichs N).domain) : (actualGammaFriedrichs N).domain :=
  ⟨frickeL2 N hN u, fricke_friedrichsDomain_action N hN u.property⟩

/-- Exact unbounded-operator intertwining on the actual full domain. -/
theorem actualGammaFriedrichs_fricke (N : ℕ) [NeZero N] (hN : 0 < N)
    (u : (actualGammaFriedrichs N).domain) :
    actualGammaFriedrichs N (friedrichsFrickeDomain N hN u) =
      frickeL2 N hN (actualGammaFriedrichs N u) := by
  have h1 := actualGammaResolvent_shift_friedrichs N (friedrichsFrickeDomain N hN u)
  have h2 := (actualGammaFriedrichs_mem_graph_iff N).mp
    (fricke_friedrichsGraph_action N hN (LinearPMap.mem_graph (actualGammaFriedrichs N) u))
  have heq := actualGammaResolvent_injective N (h1.trans h2.symm)
  exact add_left_cancel heq

def friedrichsFrickeDomainEquiv (N : ℕ) [NeZero N] (hN : 0 < N) :
    (actualGammaFriedrichs N).domain ≃ₗᵢ[ℂ] (actualGammaFriedrichs N).domain where
  toFun := friedrichsFrickeDomain N hN
  invFun := friedrichsFrickeDomain N hN
  left_inv u := Subtype.ext (frickeL2_involutive N hN u)
  right_inv u := Subtype.ext (frickeL2_involutive N hN u)
  map_add' u v := Subtype.ext ((frickeL2 N hN).map_add u v)
  map_smul' c u := Subtype.ext ((frickeL2 N hN).map_smul c u)
  norm_map' u := (frickeL2 N hN).norm_map u

end ImbalancedChen.Part3.GlobalFrickeFriedrichsIntertwining20261026b
