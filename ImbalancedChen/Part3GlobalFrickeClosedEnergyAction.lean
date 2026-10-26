import ImbalancedChen.Part3GlobalFrickeMinimalDomainAction

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO FORMAL CREDIT.

Actual native graph action supplies an energy-completion lift for the
Fricke image of every ORIGINAL energy-core vector. The true completed
Dirichlet testing relation and actual L2 isometry prove preservation of
the core energy inner product. Extending this derived isometry along
the original dense core embedding constructs a global involutive energy
isometry, with the actual physical projection intertwining Fricke.
The actual closed Dirichlet pair and actual form domain are preserved.
No hFormIsometry, domain action, completion identification or ESA premise.
-/

noncomputable section

namespace ImbalancedChen.Part3.GlobalFrickeClosedEnergyAction20261026b

open Set MeasureTheory Filter UniformSpace
open ImbalancedChen.Part3.ActualHeckeSecondL220261026b
open ImbalancedChen.Part3.GlobalFrickeHilbertInvolution20261026b
open ImbalancedChen.Part3.GlobalFrickeMinimalDomainAction20261026b
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientMaassGraph20261025a
open ImbalancedChen.Part3.Gamma0ActualMaassClosedOperator20261025a
open ImbalancedChen.Part3.Gamma0ActualEnergyCompletion20261025a
open ImbalancedChen.Part3.Gamma0ActualFriedrichsOperator20261025a
open ImbalancedChen.Part3.Gamma0ActualMinimalFriedrichsInclusion20261025a

theorem exists_frickeCoreEnergy (N : ℕ) [NeZero N] (hN : 0 < N) (u : EnergyCore N) :
    ∃ e : EnergyCompletion N,
      physicalProjection N e = frickeL2 N hN (physicalCore N u) ∧
      ∀ d : EnergyCompletion N, actualDirichletPair N d e =
        inner ℂ (physicalProjection N d) (frickeL2 N hN (coreLaplacian N u)) := by
  have hc := graphOutput_mem N u
  change (physicalCore N u, coreLaplacian N u) ∈ coreGraph N at hc
  have hclosed : (physicalCore N u, coreLaplacian N u) ∈ closedGammaGraph N := subset_closure hc
  have hfr := fricke_closedGraph_action N hN hclosed
  exact (actualGammaFriedrichs_mem_graph_iff_formPair N).mp
    (closedGammaGraph_le_friedrichsGraph N hfr)

def frickeCoreEnergy (N : ℕ) [NeZero N] (hN : 0 < N) (u : EnergyCore N) : EnergyCompletion N :=
  Classical.choose (exists_frickeCoreEnergy N hN u)

theorem frickeCoreEnergy_projection (N : ℕ) [NeZero N] (hN : 0 < N) (u : EnergyCore N) :
    physicalProjection N (frickeCoreEnergy N hN u) = frickeL2 N hN (physicalCore N u) :=
  (Classical.choose_spec (exists_frickeCoreEnergy N hN u)).1

theorem frickeCoreEnergy_Dirichlet (N : ℕ) [NeZero N] (hN : 0 < N)
    (u : EnergyCore N) (d : EnergyCompletion N) :
    actualDirichletPair N d (frickeCoreEnergy N hN u) =
      inner ℂ (physicalProjection N d) (frickeL2 N hN (coreLaplacian N u)) :=
  (Classical.choose_spec (exists_frickeCoreEnergy N hN u)).2 d

/-- Injectivity of the genuine physical projection supplies all linear
laws; no arbitrary choice of energy lift is used as linearity data. -/
def frickeCoreEnergyLinear (N : ℕ) [NeZero N] (hN : 0 < N) :
    EnergyCore N →ₗ[ℂ] EnergyCompletion N where
  toFun := frickeCoreEnergy N hN
  map_add' u v := by
    apply physicalProjection_injective N
    simp only [map_add, frickeCoreEnergy_projection]
  map_smul' c u := by
    apply physicalProjection_injective N
    simp only [map_smul, frickeCoreEnergy_projection]

/-- Derived from actual graph/Green energy and actual canonical L2
isometry, rather than postulated energy preservation. -/
theorem frickeCoreEnergy_inner (N : ℕ) [NeZero N] (hN : 0 < N) (u v : EnergyCore N) :
    inner ℂ (frickeCoreEnergy N hN u) (frickeCoreEnergy N hN v) = inner ℂ u v := by
  have ht := frickeCoreEnergy_Dirichlet N hN v (frickeCoreEnergy N hN u)
  unfold actualDirichletPair at ht
  rw [frickeCoreEnergy_projection, frickeCoreEnergy_projection,
    (frickeL2 N hN).inner_map_map, (frickeL2 N hN).inner_map_map] at ht
  rw [energyInner_apply]
  exact (sub_eq_iff_eq_add.mp ht).trans (add_comm _ _)

def frickeCoreEnergyIsometry (N : ℕ) [NeZero N] (hN : 0 < N) :
    EnergyCore N →ₗᵢ[ℂ] EnergyCompletion N :=
  (frickeCoreEnergyLinear N hN).isometryOfInner (frickeCoreEnergy_inner N hN)

theorem frickeCoreEnergy_bound (N : ℕ) [NeZero N] (hN : 0 < N) (u : EnergyCore N) :
    ‖frickeCoreEnergyLinear N hN u‖ ≤ 1 * ‖coreEmbedding N u‖ := by
  rw [one_mul, coreEmbedding_norm]
  exact (frickeCoreEnergyIsometry N hN).norm_map u |>.le

/-- The original dense energy-core embedding is the actual extension
map. The needed norm bound was proved from the real geometric operator. -/
def energyFricke (N : ℕ) [NeZero N] (hN : 0 < N) :
    EnergyCompletion N →L[ℂ] EnergyCompletion N :=
  (frickeCoreEnergyLinear N hN).extendOfNorm (coreEmbedding N).toLinearMap

theorem energyFricke_core (N : ℕ) [NeZero N] (hN : 0 < N) (u : EnergyCore N) :
    energyFricke N hN (coreEmbedding N u) = frickeCoreEnergy N hN u :=
  LinearMap.extendOfNorm_eq (coreEmbedding_denseRange N) ⟨1, frickeCoreEnergy_bound N hN⟩ u

theorem energyFricke_bound (N : ℕ) [NeZero N] (hN : 0 < N) (e : EnergyCompletion N) :
    ‖energyFricke N hN e‖ ≤ ‖e‖ := by
  simpa only [one_mul, energyFricke] using
    (LinearMap.norm_extendOfNorm_apply_le (f := frickeCoreEnergyLinear N hN)
      (e := (coreEmbedding N).toLinearMap) (coreEmbedding_denseRange N) 1
      (frickeCoreEnergy_bound N hN) e)

/-- Exact actual physical projection identity, extended by original core
density; this is not an assumed global form-domain action. -/
theorem energyFricke_physical (N : ℕ) [NeZero N] (hN : 0 < N) (e : EnergyCompletion N) :
    physicalProjection N (energyFricke N hN e) = frickeL2 N hN (physicalProjection N e) := by
  refine Completion.induction_on e ?_ ?_
  · exact isClosed_eq ((physicalProjection N).continuous.comp (energyFricke N hN).continuous)
      ((frickeL2 N hN).continuous.comp (physicalProjection N).continuous)
  · intro u
    change physicalProjection N (energyFricke N hN (coreEmbedding N u)) =
      frickeL2 N hN (physicalProjection N (coreEmbedding N u))
    rw [energyFricke_core, frickeCoreEnergy_projection, physicalProjection_core]

theorem energyFricke_involutive (N : ℕ) [NeZero N] (hN : 0 < N) :
    Function.Involutive (energyFricke N hN) := by
  intro e
  apply physicalProjection_injective N
  rw [energyFricke_physical, energyFricke_physical, frickeL2_involutive N hN]

theorem energyFricke_norm (N : ℕ) [NeZero N] (hN : 0 < N) (e : EnergyCompletion N) :
    ‖energyFricke N hN e‖ = ‖e‖ := by
  apply le_antisymm (energyFricke_bound N hN e)
  simpa only [energyFricke_involutive N hN e] using energyFricke_bound N hN (energyFricke N hN e)

/-- A genuine involutive isometry of the ACTUAL closed energy completion. -/
def energyFrickeEquiv (N : ℕ) [NeZero N] (hN : 0 < N) :
    EnergyCompletion N ≃ₗᵢ[ℂ] EnergyCompletion N where
  toFun := energyFricke N hN
  invFun := energyFricke N hN
  left_inv := energyFricke_involutive N hN
  right_inv := energyFricke_involutive N hN
  map_add' := (energyFricke N hN).map_add
  map_smul' := (energyFricke N hN).map_smul
  norm_map' := energyFricke_norm N hN

theorem energyFricke_inner (N : ℕ) [NeZero N] (hN : 0 < N) (d e : EnergyCompletion N) :
    inner ℂ (energyFricke N hN d) (energyFricke N hN e) = inner ℂ d e :=
  (energyFrickeEquiv N hN).inner_map_map d e

theorem energyFricke_Dirichlet (N : ℕ) [NeZero N] (hN : 0 < N) (d e : EnergyCompletion N) :
    actualDirichletPair N (energyFricke N hN d) (energyFricke N hN e) = actualDirichletPair N d e := by
  unfold actualDirichletPair
  rw [energyFricke_inner, energyFricke_physical, energyFricke_physical,
    (frickeL2 N hN).inner_map_map]

theorem fricke_actualFormDomain_action (N : ℕ) [NeZero N] (hN : 0 < N)
    {f : QuotientL2 N} (hf : f ∈ actualEnergyFormDomain N) :
    frickeL2 N hN f ∈ actualEnergyFormDomain N := by
  obtain ⟨e, he⟩ := hf
  refine ⟨energyFricke N hN e, ?_⟩
  rw [energyFricke_physical, he]

end ImbalancedChen.Part3.GlobalFrickeClosedEnergyAction20261026b
