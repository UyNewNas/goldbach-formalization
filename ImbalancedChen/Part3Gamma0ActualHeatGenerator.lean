import ImbalancedChen.Part3Gamma0ActualShiftedFriedrichsResolvent
import ImbalancedChen.Part3GenericPositiveResolventHeatGenerator
import ImbalancedChen.Part3GenericHeatStrongContinuity

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

Heat on the ACTUAL Gamma0 quotient Hilbert space, constructed from the
ACTUAL physical energy resolvent R=JJ*. All primitive generic heat data
are supplied by the proved actual Riesz-energy construction.

The right strong heat generator graph is exactly the negative graph of
the ACTUAL native Friedrichs operator, including full domain equality.
This is stronger than an alias or an assertion of semigroup properties:
existence of any strong right heat derivative forces the actual operator
domain and the actual differential output. The genuine Bochner heat
Laplace transform is the actual shifted resolvent and solves the actual
completed shifted Dirichlet variational problem.

Semigroup time is nonnegative. No heat kernel, essential self-adjointness
or equality with the minimal closed differential domain is asserted.
-/

namespace ImbalancedChen.Part3.Gamma0ActualHeatGenerator20261025a

noncomputable section
open MeasureTheory Set Filter Topology
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0ActualWeakRieszResolvent20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0ActualShiftedFriedrichsResolvent20261025a
open GenericPositiveResolventHeat20261025a
open GenericPositiveResolventHeatGenerator20261025a
open GenericHeatLaplaceResolvent20261025a
open GenericHeatStrongContinuity20261025a

/-- Every primitive field is the existing actual Gamma0 physical R
supplier; no heat/generator conclusion appears among these fields. -/
def actualGammaHeatData (N : ℕ) [NeZero N] : ResolventData (QuotientL2 N) where
  R := actualGammaResolvent N
  selfAdjoint := actualGammaResolvent_selfAdjoint N
  nonneg := actualGammaResolvent_nonneg N
  norm_le_one := actualGammaResolvent_opNorm_le_one N
  injective := actualGammaResolvent_injective N

def actualGammaHeat (N : ℕ) [NeZero N] (s : ℝ) :
    QuotientL2 N →L[ℂ] QuotientL2 N := heatOperator (actualGammaHeatData N) s

theorem actualGammaHeat_zero (N : ℕ) [NeZero N] : actualGammaHeat N 0=1 :=
  heatOperator_zero (actualGammaHeatData N)

theorem actualGammaHeat_add (N : ℕ) [NeZero N] {s r : ℝ}
    (hs : 0≤s) (hr : 0≤r) :
    actualGammaHeat N (s+r)=actualGammaHeat N s*actualGammaHeat N r :=
  heatOperator_add (actualGammaHeatData N) hs hr

theorem actualGammaHeat_selfAdjoint (N : ℕ) [NeZero N] (s : ℝ) :
    IsSelfAdjoint (actualGammaHeat N s) :=
  heatOperator_selfAdjoint (actualGammaHeatData N) s

theorem actualGammaHeat_isPositive (N : ℕ) [NeZero N] (s : ℝ) :
    (actualGammaHeat N s).IsPositive := heatOperator_positive (actualGammaHeatData N) s

theorem actualGammaHeat_nonneg (N : ℕ) [NeZero N] (s : ℝ) :
    0≤actualGammaHeat N s := heatOperator_nonneg (actualGammaHeatData N) s

theorem actualGammaHeat_norm_le_one (N : ℕ) [NeZero N] (s : ℝ) :
    ‖actualGammaHeat N s‖≤1 := heatOperator_opNorm_le_one (actualGammaHeatData N) s

theorem actualGammaHeat_apply_norm_le (N : ℕ) [NeZero N] (s : ℝ) (f : QuotientL2 N) :
    ‖actualGammaHeat N s f‖≤‖f‖ := heatOperator_norm_le (actualGammaHeatData N) s f

theorem actualGammaHeat_strong_at_zero (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    Tendsto (fun s : ℝ => actualGammaHeat N s f) (𝓝[>] 0) (𝓝 f) :=
  tendsto_heatOperator_at_zero (actualGammaHeatData N) f

theorem actualGammaHeat_continuousOn_positive (N : ℕ) [NeZero N] :
    ContinuousOn (actualGammaHeat N) (Ioi (0:ℝ)) :=
  continuousOn_heatOperator_positive (actualGammaHeatData N)

theorem actualGammaHeat_strong_continuousOn (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    ContinuousOn (fun s : ℝ => actualGammaHeat N s f) (Ici (0:ℝ)) :=
  continuousOn_heatTrajectory_nonnegative (actualGammaHeatData N) f

/-- KEY actual binding: the native actual Friedrichs graph is equivalent
to the actual strong heat derivative with its actual negative output. -/
theorem actualGammaFriedrichs_mem_graph_iff_heat_difference_quotient
    (N : ℕ) [NeZero N] (u v : QuotientL2 N) :
    (u,v)∈(actualGammaFriedrichs N).graph ↔
      Tendsto (fun s : ℝ => (s:ℂ)⁻¹ • (actualGammaHeat N s u-u))
        (𝓝[>] 0) (𝓝 (-v)) := by
  calc
    _ ↔ (u,v)∈PositiveContractionResolventCalculus20261025a.resolventGraph
        (actualGammaHeatData N).R := actualGammaFriedrichs_mem_graph_iff N
    _ ↔ _ := mem_resolventGraph_iff_heat_difference_quotient (actualGammaHeatData N) u v

theorem actualGammaHeat_difference_quotient_on_domain (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) :
    Tendsto (fun s : ℝ => (s:ℂ)⁻¹ • (actualGammaHeat N s (u:QuotientL2 N)-(u:QuotientL2 N)))
      (𝓝[>] 0) (𝓝 (-actualGammaFriedrichs N u)) :=
  (actualGammaFriedrichs_mem_graph_iff_heat_difference_quotient N _ _).mp
    ((actualGammaFriedrichs N).mem_graph u)

/-- Full actual domain characterization, including the converse for an
arbitrary physical quotient vector with ANY strong right heat derivative. -/
theorem actualGammaFriedrichs_domain_iff_heat_derivative (N : ℕ) [NeZero N]
    (u : QuotientL2 N) :
    u∈(actualGammaFriedrichs N).domain ↔
      ∃ w : QuotientL2 N,Tendsto (fun s : ℝ => (s:ℂ)⁻¹ • (actualGammaHeat N s u-u))
        (𝓝[>] 0) (𝓝 w) := by
  constructor
  · intro hu
    exact ⟨-actualGammaFriedrichs N ⟨u,hu⟩,actualGammaHeat_difference_quotient_on_domain N ⟨u,hu⟩⟩
  · rintro ⟨w,hw⟩
    apply LinearPMap.mem_domain_of_mem_graph (y := -w)
    apply (actualGammaFriedrichs_mem_graph_iff_heat_difference_quotient N u (-w)).mpr
    simpa only [neg_neg] using hw

def actualGammaHeatRightGeneratorGraph (N : ℕ) [NeZero N] :
    Set (QuotientL2 N × QuotientL2 N) :=
  {p | Tendsto (fun s : ℝ => (s:ℂ)⁻¹ • (actualGammaHeat N s p.1-p.1))
    (𝓝[>] 0) (𝓝 p.2)}

theorem actualGammaHeatRightGeneratorGraph_eq (N : ℕ) [NeZero N] :
    actualGammaHeatRightGeneratorGraph N=
      {p : QuotientL2 N × QuotientL2 N | (p.1,-p.2)∈(actualGammaFriedrichs N).graph} := by
  ext p
  simpa only [actualGammaHeatRightGeneratorGraph,mem_setOf_eq,neg_neg] using
    (actualGammaFriedrichs_mem_graph_iff_heat_difference_quotient N p.1 (-p.2)).symm

theorem actualGammaHeat_damped_integrableOn (N : ℕ) [NeZero N]
    (a : ℝ) (ha : 0<a) (f : QuotientL2 N) :
    IntegrableOn (fun s : ℝ => Real.exp (-a*s) • actualGammaHeat N s f) (Ioi (0:ℝ)) :=
  dampedHeatTrajectory_integrableOn (actualGammaHeatData N) a ha f

/-- Genuine Bochner Laplace transform, identified with the already
constructed ACTUAL positive shifted Friedrichs resolvent. -/
theorem actualGammaHeat_laplace (N : ℕ) [NeZero N]
    (a : ℝ) (ha : 0<a) (f : QuotientL2 N) :
    (∫ s : ℝ in Ioi 0,Real.exp (-a*s) • actualGammaHeat N s f)=
      actualGammaShiftedResolvent N a f :=
  integral_dampedHeatTrajectory (actualGammaHeatData N) a ha f

theorem actualGammaHeat_laplace_mem_domain (N : ℕ) [NeZero N]
    (a : ℝ) (ha : 0<a) (f : QuotientL2 N) :
    (∫ s : ℝ in Ioi 0,Real.exp (-a*s) • actualGammaHeat N s f)∈
      (actualGammaFriedrichs N).domain := by
  rw [actualGammaHeat_laplace N a ha f]
  exact actualGammaShiftedResolvent_mem_domain N ha f

/-- The time integral is the unique native actual operator solution. -/
theorem actualGammaHeat_laplace_operator_solution (N : ℕ) [NeZero N]
    (a : ℝ) (ha : 0<a) (f : QuotientL2 N) :
    ∃ u : (actualGammaFriedrichs N).domain,
      (u:QuotientL2 N)=(∫ s : ℝ in Ioi 0,Real.exp (-a*s) • actualGammaHeat N s f) ∧
        (a:ℂ) • (u:QuotientL2 N)+actualGammaFriedrichs N u=f := by
  refine ⟨actualShiftedResolventPoint N a ha f,?_,actualShiftedFriedrichsMap_apply_inverse N ha f⟩
  exact (actualGammaHeat_laplace N a ha f).symm

/-- ALL completed-energy tests obey the genuine shifted Dirichlet
identity for the heat time integral. This is obtained from the actual
closed-form graph and not assumed as a heat/resolvent supplier. -/
theorem actualGammaHeat_laplace_weak_Dirichlet (N : ℕ) [NeZero N]
    (a : ℝ) (ha : 0<a) (f : QuotientL2 N) :
    ∃ e : EnergyCompletion N,
      physicalProjection N e=(∫ s : ℝ in Ioi 0,Real.exp (-a*s) • actualGammaHeat N s f) ∧
        ∀ d : EnergyCompletion N,
          (a:ℂ)*inner ℂ (physicalProjection N d) (physicalProjection N e)+
            actualDirichletPair N d e=inner ℂ (physicalProjection N d) f := by
  rw [actualGammaHeat_laplace N a ha f]
  exact exists_actualShiftedDirichletSolution N ha f

end
end ImbalancedChen.Part3.Gamma0ActualHeatGenerator20261025a
