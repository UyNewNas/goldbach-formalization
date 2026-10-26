import ImbalancedChen.Part3GammaActualCarrierGradientPolarization
import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A genuine native closed first-order gradient operator on the ORIGINAL
physical quotient Hilbert space. Its domain is exactly the EXISTING
actualEnergyFormDomain. The graph is proved closed as the range of the
complete energy space under (physical value, actual carrier gradient),
using the proved exact norm identity and an explicit inverse bound.
No closed-gradient, Sobolev model or graph-closedness premise is supplied.
-/

namespace ImbalancedChen.Part3.GammaActualClosedGradientRealization20261026b
noncomputable section
open Set Filter MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualFriedrichsOperator20261025a Gamma0PhysicalClosedDirichletForm20261025a
open Gamma0CarrierGradientHilbertMap20261026b GammaActualCarrierGradientPolarization20261026b

def gradientGraphEmbedding (N : ℕ) [NeZero N] :
    EnergyCompletion N →L[ℂ] (QuotientL2 N × CarrierGradientL2 N) :=
  (physicalProjection N).prod (completedCarrierGradient N)

theorem energy_norm_sq_value_gradient (N : ℕ) [NeZero N] (e : EnergyCompletion N) :
    ‖e‖^2 = ‖physicalProjection N e‖^2 + ‖completedCarrierGradient N e‖^2 := by
  have h := completedCarrierGradient_norm_sq N e
  rw [actualDirichletPair_self_re_eq_energy_defect] at h
  linarith

theorem energy_norm_le_value_add_gradient (N : ℕ) [NeZero N] (e : EnergyCompletion N) :
    ‖e‖ ≤ ‖physicalProjection N e‖ + ‖completedCarrierGradient N e‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [energy_norm_sq_value_gradient]
  nlinarith [mul_nonneg (norm_nonneg (physicalProjection N e))
    (norm_nonneg (completedCarrierGradient N e))]

theorem gradientGraphEmbedding_inverse_bound (N : ℕ) [NeZero N] (e : EnergyCompletion N) :
    ‖e‖ ≤ (2 : ℝ) * ‖gradientGraphEmbedding N e‖ := by
  change ‖e‖ ≤ 2 * max ‖physicalProjection N e‖ ‖completedCarrierGradient N e‖
  have h := energy_norm_le_value_add_gradient N e
  linarith [le_max_left ‖physicalProjection N e‖ ‖completedCarrierGradient N e‖,
    le_max_right ‖physicalProjection N e‖ ‖completedCarrierGradient N e‖]

theorem gradientGraphEmbedding_closed_range (N : ℕ) [NeZero N] :
    IsClosed (Set.range (gradientGraphEmbedding N)) := by
  have hanti : AntilipschitzWith (2 : ℝ≥0) (gradientGraphEmbedding N) :=
    (gradientGraphEmbedding N).antilipschitz_of_bound (gradientGraphEmbedding_inverse_bound N)
  exact hanti.isClosed_range (gradientGraphEmbedding N).uniformContinuous

def actualClosedGradient (N : ℕ) [NeZero N] :
    QuotientL2 N →ₗ.[ℂ] CarrierGradientL2 N where
  domain := actualEnergyFormDomain N
  toFun := (completedCarrierGradient N).toLinearMap.comp (actualEnergyLift N).toLinearMap

/-- The graph uses the SAME original physical form domain; its energy
lift is unique because the original physical projection is injective. -/
theorem actualClosedGradient_graph_eq_range (N : ℕ) [NeZero N] :
    ((actualClosedGradient N).graph : Set (QuotientL2 N × CarrierGradientL2 N)) =
      Set.range (gradientGraphEmbedding N) := by
  ext p
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨u,hu,hGu⟩
    refine ⟨actualEnergyLift N u,?_⟩
    apply Prod.ext
    · exact (actualEnergyLift_projection N u).trans hu
    · exact hGu
  · rintro ⟨e,rfl⟩
    let u : actualEnergyFormDomain N := ⟨physicalProjection N e,⟨e,rfl⟩⟩
    refine ⟨u,rfl,?_⟩
    have heq : actualEnergyLift N u = e := by
      apply physicalProjection_injective N
      exact actualEnergyLift_projection N u
    change completedCarrierGradient N (actualEnergyLift N u) = completedCarrierGradient N e
    rw [heq]

theorem actualClosedGradient_isClosed (N : ℕ) [NeZero N] : (actualClosedGradient N).IsClosed := by
  change IsClosed ((actualClosedGradient N).graph : Set (QuotientL2 N × CarrierGradientL2 N))
  rw [actualClosedGradient_graph_eq_range]
  exact gradientGraphEmbedding_closed_range N

theorem actualClosedGradient_dense_domain (N : ℕ) [NeZero N] :
    Dense ((actualClosedGradient N).domain : Set (QuotientL2 N)) :=
  physicalProjection_denseRange N

/-- Exact complex form realization through the native closed gradient. -/
theorem actualClosedGradient_inner (N : ℕ) [NeZero N]
    (u v : actualEnergyFormDomain N) :
    inner ℂ (actualClosedGradient N u) (actualClosedGradient N v) =
      actualDirichletPair N (actualEnergyLift N u) (actualEnergyLift N v) :=
  completed_carrier_gradient_inner N _ _

end
end ImbalancedChen.Part3.GammaActualClosedGradientRealization20261026b
