import ImbalancedChen.Part3ActualTensorGradientLinearMaps
import ImbalancedChen.Part3MaassFirstGradientClosability
import ImbalancedChen.Part3CanonicalMaassTensorDensity
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Topology.Sequences

/-!
The actual completed shifted energy form. The ambient space is a nested
L2 product of three genuine Hilbert spaces, not the max-norm product.
The energy domain is the closed linear span of the actual input/gradient
graph. Actual first-gradient closability proves that physical projection
is injective; genuine actual-domain density proves its dense range.
No closed-form, density, derivative map or injectivity supplier is assumed.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualCompletedTensorEnergyForm20261025a

noncomputable section

open MeasureTheory Filter Topology Set
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.MaassFiniteCoreL2LinearOperator20261025a
open ImbalancedChen.Part3.MaassFirstGradientWeakLimit20261025a
open ImbalancedChen.Part3.MaassFirstGradientClosability20261025a
open ImbalancedChen.Part3.CanonicalMaassTensorDensity20261025a
open ImbalancedChen.Part3.ActualNestedTensorRitzEnergy20261025a
open ImbalancedChen.Part3.ActualTensorGradientLinearMaps20261025a

abbrev GradientPair := WithLp 2 (PlaneL2 × PlaneL2)
abbrev EnergyTriple := WithLp 2 (HyperbolicL2 × GradientPair)

def triplePhysical : EnergyTriple →L[ℂ] HyperbolicL2 :=
  WithLp.fstL 2 ℂ HyperbolicL2 GradientPair

def tripleGradient (vertical : Bool) : EnergyTriple →L[ℂ] PlaneL2 :=
  (if vertical then WithLp.sndL 2 ℂ PlaneL2 PlaneL2
    else WithLp.fstL 2 ℂ PlaneL2 PlaneL2).comp
      (WithLp.sndL 2 ℂ HyperbolicL2 GradientPair)

/-- The literal actual input and the two constructed actual derivatives. -/
def energyGraphEmbedding : actualTensorDomain →ₗ[ℂ] EnergyTriple :=
  (WithLp.linearEquiv 2 ℂ (HyperbolicL2 × GradientPair)).symm.toLinearMap.comp
    (actualTensorDomain.subtype.prod
      ((WithLp.linearEquiv 2 ℂ (PlaneL2 × PlaneL2)).symm.toLinearMap.comp
        ((actualGradient false).prod (actualGradient true))))

theorem energyGraphEmbedding_apply (u : actualTensorDomain) :
    energyGraphEmbedding u = WithLp.toLp 2
      ((u : HyperbolicL2), WithLp.toLp 2 (actualGradient false u, actualGradient true u)) := rfl

theorem triplePhysical_energyGraphEmbedding (u : actualTensorDomain) :
    triplePhysical (energyGraphEmbedding u) = (u : HyperbolicL2) := rfl

theorem tripleGradient_energyGraphEmbedding (vertical : Bool) (u : actualTensorDomain) :
    tripleGradient vertical (energyGraphEmbedding u) = actualGradient vertical u := by
  cases vertical <;> rfl

def energyCore : Submodule ℂ EnergyTriple := LinearMap.range energyGraphEmbedding

/-- A closed submodule of the genuine L2 Hilbert triple. -/
def completedEnergy : Submodule ℂ EnergyTriple := energyCore.topologicalClosure

instance completedEnergy_completeSpace : CompleteSpace completedEnergy := by
  change CompleteSpace energyCore.topologicalClosure
  infer_instance

def coreEmbedding : actualTensorDomain →ₗ[ℂ] completedEnergy :=
  energyGraphEmbedding.codRestrict completedEnergy
    (fun u => energyCore.le_topologicalClosure ⟨u, rfl⟩)

theorem coreEmbedding_coe (u : actualTensorDomain) :
    (coreEmbedding u : EnergyTriple) = energyGraphEmbedding u := rfl

/-- The exact inherited Hilbert pairing, including both gradient terms. -/
theorem coreEmbedding_inner (u v : actualTensorDomain) :
    inner ℂ (coreEmbedding u) (coreEmbedding v) =
      inner ℂ (u : HyperbolicL2) (v : HyperbolicL2) +
        inner ℂ (actualGradient false u) (actualGradient false v) +
        inner ℂ (actualGradient true u) (actualGradient true v) := by
  change inner ℂ (energyGraphEmbedding u) (energyGraphEmbedding v) = _
  simp only [energyGraphEmbedding_apply, WithLp.prod_inner_apply, WithLp.ofLp_toLp]
  ring

theorem coreEmbedding_norm_sq_eq_energy (u : actualTensorDomain) :
    ‖coreEmbedding u‖ ^ 2 = shiftedEnergy u := by
  change ‖energyGraphEmbedding u‖ ^ 2 = _
  rw [energyGraphEmbedding_apply]
  simp only [WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd]
  rw [shiftedEnergy_eq_gradient_norms]
  ring

def physicalProjection : completedEnergy →L[ℂ] HyperbolicL2 :=
  triplePhysical.comp completedEnergy.subtypeL

def completedGradient (vertical : Bool) : completedEnergy →L[ℂ] PlaneL2 :=
  (tripleGradient vertical).comp completedEnergy.subtypeL

theorem physicalProjection_coreEmbedding (u : actualTensorDomain) :
    physicalProjection (coreEmbedding u) = (u : HyperbolicL2) := rfl

theorem completedGradient_coreEmbedding (vertical : Bool) (u : actualTensorDomain) :
    completedGradient vertical (coreEmbedding u) = actualGradient vertical u :=
  tripleGradient_energyGraphEmbedding vertical u

/-- The physical projection is a contraction in the true completed
shifted energy norm, with no bound supplied by the caller. -/
theorem physicalProjection_norm_le (u : completedEnergy) :
    ‖physicalProjection u‖ ≤ ‖u‖ :=
  WithLp.norm_fst_le (u : EnergyTriple)

/-- Each pair of projected coordinates lies in the actual closed first
gradient graph, by continuity of the literal pair projection. -/
theorem completedGradient_mem_closed_graph (vertical : Bool) (u : completedEnergy) :
    (physicalProjection u, completedGradient vertical u) ∈
      closure (finiteGradientGraph vertical) := by
  let q : EnergyTriple →L[ℂ] HyperbolicL2 × PlaneL2 :=
    triplePhysical.prod (tripleGradient vertical)
  have hcore : MapsTo q (energyCore : Set EnergyTriple) (finiteGradientGraph vertical) := by
    rintro z ⟨v, rfl⟩
    change (triplePhysical (energyGraphEmbedding v),
      tripleGradient vertical (energyGraphEmbedding v)) ∈ finiteGradientGraph vertical
    rw [triplePhysical_energyGraphEmbedding, tripleGradient_energyGraphEmbedding]
    exact actualGradient_mem_graph vertical v
  have hclosure : (u : EnergyTriple) ∈ closure (energyCore : Set EnergyTriple) := u.property
  exact map_mem_closure q.continuous hclosure hcore

/-- Actual first-gradient closability removes both vertical fibers of
the completed triple graph. Physical L2 inputs determine form elements. -/
theorem physicalProjection_injective : Function.Injective physicalProjection := by
  intro u v huv
  have hxu := completedGradient_mem_closed_graph false u
  have hxv := completedGradient_mem_closed_graph false v
  have hyu := completedGradient_mem_closed_graph true u
  have hyv := completedGradient_mem_closed_graph true v
  rw [← huv] at hxv hyv
  have hx := closure_finiteGradientGraph_right_unique false hxu hxv
  have hy := closure_finiteGradientGraph_right_unique true hyu hyv
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact huv
  · apply WithLp.ofLp_injective 2
    exact Prod.ext hx hy

/-- The literal actual core is dense for the completed form norm. This
comes from closing the graph range, without assuming an exhaustion. -/
theorem coreEmbedding_denseRange : DenseRange coreEmbedding := by
  intro u
  have hu : (u : EnergyTriple) ∈ closure (energyCore : Set EnergyTriple) := u.property
  obtain ⟨z, hz, hlim⟩ := mem_closure_iff_seq_limit.mp hu
  have hw (k : ℕ) : ∃ v : actualTensorDomain, energyGraphEmbedding v = z k := hz k
  choose v hv using hw
  have hsub : Tendsto (fun k => coreEmbedding (v k)) atTop (𝓝 u) := by
    apply tendsto_subtype_rng.2
    exact hlim.congr' (Eventually.of_forall fun k => (hv k).symm)
  exact isClosed_closure.mem_of_tendsto hsub
    (Eventually.of_forall fun k => subset_closure ⟨v k, rfl⟩)

/-- The actual canonical tensor-domain density, already proved from the
true planar density/unitary construction, gives dense physical range. -/
theorem physicalProjection_denseRange : DenseRange physicalProjection := by
  apply actualTensorDomain_dense.mono
  intro f hf
  exact ⟨coreEmbedding ⟨f, hf⟩, rfl⟩

end

end ImbalancedChen.Part3.ActualCompletedTensorEnergyForm20261025a
