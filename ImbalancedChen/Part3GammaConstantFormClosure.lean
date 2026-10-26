import ImbalancedChen.Part3GammaModularCutoffMinimalDomain
import ImbalancedChen.Part3GammaConstantCutoffL2
import ImbalancedChen.Part3GammaClosedGraphCoreDiagonal
import ImbalancedChen.Part3GammaCoreDiagonalEnergyBudget
import ImbalancedChen.Part3GammaNormalizedConstantVector

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Constant one belongs to the ACTUAL closed Gamma0 Dirichlet form and the
native Friedrichs kernel. Each global cutoff has genuine minimal graph
membership from constructed compact smooth seeds and finite tensor C2
graph approximation. The fixed heights n+2 have true physical tail and
Delta L2 budgets. A same-stage 1/(n+1) diagonal produces ORIGINAL legal
finite tensor core vectors converging in the actual shifted form norm.
Explicit squared form error and gradient-energy error are retained.
The actual normalized constant and its whole complex line are in the
same native operator kernel. No whole-Hardy or assumed constant domain.
-/
namespace ImbalancedChen.Part3.GammaConstantFormClosure20261026a

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0ActualMaassClosedOperator20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0ActualConstantMode20261025a
open GammaModularCutoffMinimalDomain20261026a
open GammaConstantCutoffL220261026a
open GammaClosedGraphCoreDiagonal20261026a
open GammaCoreDiagonalEnergyBudget20261026a
open GammaNormalizedConstantVector20261026a
open ActualCuspStripCutoffGraph20261025a

/-- This is the actual full modular cutoff on every Gamma0 cusp, not a
single infinity-cusp cutoff. The two objects are canonical quotient L2. -/
theorem cutoffL2_pair_mem_closedGraph (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    (cutoffL2 N Y hY, cutoffMaassL2 N Y hY) ∈ closedGammaGraph N :=
  cutoff_ae_pair_mem_closedGraph N Y hY _ _ (cutoffL2_ae N Y hY) (cutoffMaassL2_ae N Y hY)

/-- A stronger endpoint than needed for Friedrichs membership: the actual
constant already lies in the actual MINIMAL closed differential graph. -/
theorem constantL2_mem_minimalGraph (N : ℕ) [NeZero N] :
    (constantL2 N, (0 : QuotientL2 N)) ∈ closedGammaGraph N := by
  apply (closedGammaGraph_isClosed N).mem_of_tendsto
    ((cutoffL2_tendsto_constant N).prodMk_nhds (cutoffMaassL2_tendsto_zero N))
  exact Filter.Eventually.of_forall (fun n =>
    cutoffL2_pair_mem_closedGraph N (cutoffHeight n) (cutoffHeight_gt_one n))

/-- The physical and differential error radii have the literal original
index and fixed cutoff second-derivative constant. -/
def physicalErrorRadius (N n : ℕ) : ℝ := diagonalTolerance n +
  Real.sqrt (((CongruenceSubgroup.Gamma0 N).index : ℝ) / cutoffHeight n)

def deltaErrorRadius (N n : ℕ) : ℝ := diagonalTolerance n +
  Real.sqrt (cutoffGraphConstant * ((CongruenceSubgroup.Gamma0 N).index : ℝ) / cutoffHeight n)

theorem physicalErrorRadius_nonneg (N n : ℕ) : 0 ≤ physicalErrorRadius N n :=
  add_nonneg (diagonalTolerance_pos n).le (Real.sqrt_nonneg _)

/-- The requested concrete diagonal in the ORIGINAL finite tensor core:
true physical convergence, Delta convergence, form-norm convergence and
an explicit same-stage form error, with no assumed form membership. -/
theorem exists_constant_legal_core_energy_diagonal (N : ℕ) [NeZero N] :
    ∃ u : ℕ → EnergyCore N, ∃ e : EnergyCompletion N,
      physicalProjection N e = constantL2 N ∧ actualDirichletPair N e e = 0 ∧
      Tendsto (fun n => coreEmbedding N (u n)) atTop (𝓝 e) ∧
      Tendsto (fun n => physicalCore N (u n)) atTop (𝓝 (constantL2 N)) ∧
      Tendsto (fun n => coreLaplacian N (u n)) atTop (𝓝 0) ∧
      (∀ n, ‖physicalCore N (u n) - constantL2 N‖ ≤ physicalErrorRadius N n ∧
        ‖coreLaplacian N (u n)‖ ≤ deltaErrorRadius N n ∧
        ‖coreEmbedding N (u n) - e‖ ^ 2 ≤
          physicalErrorRadius N n ^ 2 +
            (‖constantL2 N‖ + physicalErrorRadius N n) * deltaErrorRadius N n) := by
  let U : ℕ → QuotientL2 N := fun n => cutoffL2 N (cutoffHeight n) (cutoffHeight_gt_one n)
  let V : ℕ → QuotientL2 N := fun n => cutoffMaassL2 N (cutoffHeight n) (cutoffHeight_gt_one n)
  obtain ⟨u, e, hnear, hU, hV, he, hproj, henergy, _hkernel⟩ :=
    exists_legal_energy_diagonal_of_graph_zero N U V (constantL2 N)
      (fun n => cutoffL2_pair_mem_closedGraph N _ _) (cutoffL2_tendsto_constant N)
      (cutoffMaassL2_tendsto_zero N)
  refine ⟨u, e, hproj, henergy, he, hU, hV, ?_⟩
  intro n
  have hgapU : ‖physicalCore N (u n) - U n‖ ≤ diagonalTolerance n := by
    simpa only [dist_eq_norm, norm_sub_rev] using (hnear n).1.le
  have hgapV : ‖coreLaplacian N (u n) - V n‖ ≤ diagonalTolerance n := by
    simpa only [dist_eq_norm, norm_sub_rev] using (hnear n).2.le
  have htail : ‖U n - constantL2 N‖ ≤
      Real.sqrt (((CongruenceSubgroup.Gamma0 N).index : ℝ) / cutoffHeight n) :=
    Real.le_sqrt_of_sq_le (cutoffL2_sub_constant_norm_sq_le N _ _)
  have hdelta : ‖V n‖ ≤ Real.sqrt
      (cutoffGraphConstant * ((CongruenceSubgroup.Gamma0 N).index : ℝ) / cutoffHeight n) :=
    Real.le_sqrt_of_sq_le (cutoffMaassL2_norm_sq_le N _ _)
  have hp : ‖physicalCore N (u n) - constantL2 N‖ ≤ physicalErrorRadius N n := by
    calc
      _ = ‖(physicalCore N (u n) - U n) + (U n - constantL2 N)‖ := by congr 1; abel
      _ ≤ ‖physicalCore N (u n) - U n‖ + ‖U n - constantL2 N‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hgapU htail
  have hL : ‖coreLaplacian N (u n)‖ ≤ deltaErrorRadius N n := by
    calc
      _ = ‖(coreLaplacian N (u n) - V n) + V n‖ := by congr 1; abel
      _ ≤ ‖coreLaplacian N (u n) - V n‖ + ‖V n‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hgapV hdelta
  refine ⟨hp, hL, ?_⟩
  have hb := energy_distance_sq_le N e henergy (u n) (physicalErrorRadius_nonneg N n)
    (by simpa only [hproj] using hp) hL
  simpa only [hproj] using hb

/-- Actual form-domain membership with a constructed energy lift. -/
theorem constantL2_mem_formDomain (N : ℕ) [NeZero N] :
    constantL2 N ∈ actualEnergyFormDomain N := by
  obtain ⟨u, e, he, _⟩ := exists_constant_legal_core_energy_diagonal N
  exact ⟨e, he⟩

/-- Genuine native operator kernel, with no hNoEigen or hMembership input. -/
theorem constantL2_mem_friedrichsGraph_zero (N : ℕ) [NeZero N] :
    (constantL2 N, (0 : QuotientL2 N)) ∈ (actualGammaFriedrichs N).graph :=
  Gamma0ActualMinimalFriedrichsInclusion20261025a.closedGammaGraph_le_friedrichsGraph N
    (constantL2_mem_minimalGraph N)

theorem constantL2_mem_friedrichsDomain (N : ℕ) [NeZero N] :
    constantL2 N ∈ (actualGammaFriedrichs N).domain :=
  LinearPMap.mem_domain_iff.mpr ⟨0, constantL2_mem_friedrichsGraph_zero N⟩

def constantDomainPoint (N : ℕ) [NeZero N] : (actualGammaFriedrichs N).domain :=
  ⟨constantL2 N, constantL2_mem_friedrichsDomain N⟩

theorem actualGammaFriedrichs_constant (N : ℕ) [NeZero N] :
    actualGammaFriedrichs N (constantDomainPoint N) = 0 := by
  obtain ⟨u, hu, hv⟩ := LinearPMap.mem_graph_iff.mp (constantL2_mem_friedrichsGraph_zero N)
  have heq : u = constantDomainPoint N := Subtype.ext hu
  simpa only [heq] using hv

/-- All complex constants belong to the SAME kernel. -/
theorem scalar_constant_mem_friedrichsGraph_zero (N : ℕ) [NeZero N] (c : ℂ) :
    (c • constantL2 N, (0 : QuotientL2 N)) ∈ (actualGammaFriedrichs N).graph := by
  simpa only [Prod.smul_mk, smul_zero] using
    (actualGammaFriedrichs N).graph.smul_mem c (constantL2_mem_friedrichsGraph_zero N)

theorem constantUnit_mem_friedrichsGraph_zero (N : ℕ) [NeZero N] :
    (constantUnit N, (0 : QuotientL2 N)) ∈ (actualGammaFriedrichs N).graph :=
  scalar_constant_mem_friedrichsGraph_zero N ((volumeRoot N)⁻¹ : ℂ)

/-- Precise ambient kernel: the pullback of the native graph along
f↦(f,0). Its elements are actual physical L2 vectors, not domain subtypes. -/
def ambientFriedrichsKernel (N : ℕ) [NeZero N] : Submodule ℂ (QuotientL2 N) :=
  (actualGammaFriedrichs N).graph.comap
    ((LinearMap.id : QuotientL2 N →ₗ[ℂ] QuotientL2 N).prod 0)

theorem ambientFriedrichsKernel_mem_iff (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    f ∈ ambientFriedrichsKernel N ↔
      (f, (0 : QuotientL2 N)) ∈ (actualGammaFriedrichs N).graph := Iff.rfl

/-- Reverse kernel inclusion for the actual one-dimensional constant line. -/
theorem constantLine_le_friedrichsKernel (N : ℕ) [NeZero N] :
    Submodule.span ℂ {constantL2 N} ≤ ambientFriedrichsKernel N := by
  apply Submodule.span_le.mpr
  intro f hf
  have heq : f = constantL2 N := Set.mem_singleton_iff.mp hf
  rw [heq]
  exact constantL2_mem_friedrichsGraph_zero N

end
end ImbalancedChen.Part3.GammaConstantFormClosure20261026a
