import ImbalancedChen.Part3GammaHeatMeanInvariant

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual native Friedrichs graph has mean-zero output and splits off
its genuine constant input without changing the output. On the actual
completed energy space, the true constant has zero Dirichlet pairing
against every completed-energy test. Physical centering lifts to energy
centering, preserving the entire closed Dirichlet form. These are actual
operator/form facts needed for a later spectral split, with no positive
spectral gap or automorphic cusp/Eisenstein completeness assertion.
-/
namespace ImbalancedChen.Part3.GammaMeanZeroClosedFormSplit20261026b

noncomputable section
open Set MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0QuotientCellPushforward20261025a
open Gamma0ActualConstantMode20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualFriedrichsOperator20261025a
open GammaConstantFormClosure20261026a
open GammaConstantRankOneProjection20261026a
open GammaZeroSpectralProjectionKernel20261026a
open GammaHeatMeanInvariant20261026b

/-- Every actual native graph output is orthogonal to the actual constant,
even when the input has nonzero mean. -/
theorem actualGammaFriedrichs_graph_output_meanZero (N : ℕ) [NeZero N]
    {u v : QuotientL2 N} (huv : (u, v) ∈ (actualGammaFriedrichs N).graph) :
    v ∈ actualMeanZero N := by
  change inner ℂ (constantL2 N) v = 0
  have hfixed : actualGammaResolvent N (constantL2 N) = constantL2 N :=
    (kernel_mem_iff_resolvent_fixed N (constantL2 N)).mp
      (constantL2_mem_friedrichsGraph_zero N)
  have hgraph := (actualGammaFriedrichs_mem_graph_iff N).mp huv
  have hsym := (actualGammaResolvent_selfAdjoint N).isSymmetric (constantL2 N) (u + v)
  rw [hfixed, hgraph, inner_add_right] at hsym
  linear_combination hsym

theorem actualGammaFriedrichs_output_meanZero (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    actualGammaFriedrichs N u ∈ actualMeanZero N :=
  actualGammaFriedrichs_graph_output_meanZero N ((actualGammaFriedrichs N).mem_graph u)

/-- Removing the actual constant projection preserves the literal native
graph output, not merely a weak or bounded resolvent relation. -/
theorem actualGammaFriedrichs_graph_centered_iff (N : ℕ) [NeZero N]
    (u v : QuotientL2 N) :
    (actualCenteredVector N u, v) ∈ (actualGammaFriedrichs N).graph ↔
      (u, v) ∈ (actualGammaFriedrichs N).graph := by
  have hp : (constantRankOne N u, (0 : QuotientL2 N)) ∈
      (actualGammaFriedrichs N).graph :=
    (ambientFriedrichsKernel_mem_iff N _).mp (constantRankOne_range_le_kernel N u)
  constructor
  · intro h
    have hsum := (actualGammaFriedrichs N).graph.add_mem h hp
    change (actualCenteredVector N u + constantRankOne N u, v + 0) ∈
      (actualGammaFriedrichs N).graph at hsum
    simpa only [actualCenteredVector, sub_add_cancel, add_zero] using hsum
  · intro h
    have hsub := (actualGammaFriedrichs N).graph.sub_mem h hp
    change (u - constantRankOne N u, v - 0) ∈ (actualGammaFriedrichs N).graph at hsub
    simpa only [sub_zero, actualCenteredVector] using hsub

private theorem exists_actualConstantEnergy (N : ℕ) [NeZero N] :
    ∃ e : EnergyCompletion N, physicalProjection N e = constantL2 N ∧
      ∀ d : EnergyCompletion N, actualDirichletPair N d e = 0 := by
  obtain ⟨e, he, htest⟩ := (actualGammaFriedrichs_mem_graph_iff_formPair N).mp
    (constantL2_mem_friedrichsGraph_zero N)
  refine ⟨e, he, ?_⟩
  intro d
  simpa only [inner_zero_right] using htest d

/-- The uniquely determined energy lift of the genuine physical constant. -/
def actualConstantEnergy (N : ℕ) [NeZero N] : EnergyCompletion N :=
  Classical.choose (exists_actualConstantEnergy N)

theorem physicalProjection_actualConstantEnergy (N : ℕ) [NeZero N] :
    physicalProjection N (actualConstantEnergy N) = constantL2 N :=
  (Classical.choose_spec (exists_actualConstantEnergy N)).1

theorem actualDirichletPair_constant_right (N : ℕ) [NeZero N]
    (d : EnergyCompletion N) :
    actualDirichletPair N d (actualConstantEnergy N) = 0 :=
  (Classical.choose_spec (exists_actualConstantEnergy N)).2 d

theorem actualDirichletPair_constant_left (N : ℕ) [NeZero N]
    (d : EnergyCompletion N) :
    actualDirichletPair N (actualConstantEnergy N) d = 0 := by
  have h := congrArg (fun z : ℂ => star z) (actualDirichletPair_constant_right N d)
  simpa only [actualDirichletPair, map_sub, inner_conj_symm, star_zero] using h

/-- In the true shifted-energy Hilbert space, the constant coefficient
is exactly the original physical integral. -/
theorem actualConstantEnergy_inner (N : ℕ) [NeZero N] (e : EnergyCompletion N) :
    inner ℂ (actualConstantEnergy N) e =
      ∫ q, physicalProjection N e q ∂carrierPushforward N := by
  have h := actualDirichletPair_constant_left N e
  rw [actualDirichletPair, physicalProjection_actualConstantEnergy, constantL2_inner] at h
  exact sub_eq_zero.mp h

theorem actualConstantEnergy_norm_sq (N : ℕ) [NeZero N] :
    ‖actualConstantEnergy N‖ ^ 2 = actualVolume N := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), actualConstantEnergy_inner,
    physicalProjection_actualConstantEnergy, ← constantL2_inner,
    constantL2_inner_self, Complex.ofReal_re]

def actualCenteredEnergy (N : ℕ) [NeZero N] (e : EnergyCompletion N) :
    EnergyCompletion N :=
  e - (((∫ q, physicalProjection N e q ∂carrierPushforward N) /
    (actualVolume N : ℂ)) • actualConstantEnergy N)

/-- Centering commutes with the genuine injective physical form inclusion. -/
theorem physicalProjection_actualCenteredEnergy (N : ℕ) [NeZero N]
    (e : EnergyCompletion N) :
    physicalProjection N (actualCenteredEnergy N e) =
      actualCenteredVector N (physicalProjection N e) := by
  rw [actualCenteredEnergy, map_sub, map_smul, physicalProjection_actualConstantEnergy,
    actualCenteredVector, constantRankOne_apply_mean]

theorem actualCenteredEnergy_physical_meanZero (N : ℕ) [NeZero N]
    (e : EnergyCompletion N) :
    physicalProjection N (actualCenteredEnergy N e) ∈ actualMeanZero N := by
  rw [physicalProjection_actualCenteredEnergy]
  exact actualCenteredVector_mem_meanZero N _

theorem actualCenteredEnergy_orthogonal_constant (N : ℕ) [NeZero N]
    (e : EnergyCompletion N) :
    inner ℂ (actualConstantEnergy N) (actualCenteredEnergy N e) = 0 := by
  rw [actualConstantEnergy_inner]
  exact (mem_actualMeanZero_iff N _).mp (actualCenteredEnergy_physical_meanZero N e)

private theorem actualDirichletPair_sub_constant_right (N : ℕ) [NeZero N]
    (d e : EnergyCompletion N) (c : ℂ) :
    actualDirichletPair N d (e - c • actualConstantEnergy N) = actualDirichletPair N d e := by
  have h := actualDirichletPair_constant_right N d
  unfold actualDirichletPair at h ⊢
  simp only [map_sub, map_smul, inner_sub_right, inner_smul_right]
  rw [sub_eq_zero.mp h]
  ring

theorem actualDirichletPair_centered_right (N : ℕ) [NeZero N]
    (d e : EnergyCompletion N) :
    actualDirichletPair N d (actualCenteredEnergy N e) = actualDirichletPair N d e :=
  actualDirichletPair_sub_constant_right N d e _

theorem actualDirichletPair_centered_left (N : ℕ) [NeZero N]
    (d e : EnergyCompletion N) :
    actualDirichletPair N (actualCenteredEnergy N d) e = actualDirichletPair N d e := by
  have h := congrArg (fun z : ℂ => star z) (actualDirichletPair_centered_right N e d)
  simpa only [actualDirichletPair, map_sub, inner_conj_symm] using h

/-- The full actual closed Dirichlet pairing is supported on the true
mean-zero component, including all completed-energy vectors. -/
theorem actualDirichletPair_centered (N : ℕ) [NeZero N]
    (d e : EnergyCompletion N) :
    actualDirichletPair N (actualCenteredEnergy N d) (actualCenteredEnergy N e) =
      actualDirichletPair N d e := by
  rw [actualDirichletPair_centered_left, actualDirichletPair_centered_right]

end
end ImbalancedChen.Part3.GammaMeanZeroClosedFormSplit20261026b
