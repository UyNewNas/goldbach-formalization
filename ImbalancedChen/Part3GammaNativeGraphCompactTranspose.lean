import ImbalancedChen.Part3GammaFiniteSeedAdjointGraphTests
import ImbalancedChen.Part3GammaActualMinimalDefectVanishes

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Native graph/domain characterization for the ACTUAL minimal Gamma Maass
closure. Arbitrary compact smooth H transpose tests with a global quotient
L2 output are sufficient. The reverse pays the genuine finite seed
unfolding/span/closure join before using the proved native self-adjointness
of the actual minimal closure. No adjoint graph or form membership is
assumed; no spectral decomposition is asserted.
-/
namespace ImbalancedChen.Part3.GammaNativeGraphCompactTranspose20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology UpperHalfPlane
open MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareLocalFinite20261025a Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0CompactLaplacianSeed20261025a Gamma0SmoothCompactTensorCore20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0ActualMaassClosedOperator20261025a Gamma0QuotientCellPushforward20261025a
open Gamma0WholeSeedAdjointWeakEquation20261026b GammaFiniteSeedAdjointGraphTests20261026b
open GammaActualMinimalDefectVanishes20261026b

def HasCompactSmoothTranspose (N : ℕ) [NeZero N] (f w : QuotientL2 N) : Prop :=
  ∀ ψ : UpperHalfPlane → ℂ, HasCompactSupport ψ →
    ContDiffOn ℝ ∞ (extendUpper ψ) positiveChart →
      (∫ z : UpperHalfPlane, star (upperMaass ψ z) * f (orbitProjection N z)) =
        ∫ z : UpperHalfPlane, star (ψ z) * w (orbitProjection N z)

/-- The converse uses actual finite core graph tests, not a presumed
elliptic-domain or form-domain identification. -/
theorem actual_adjoint_graph_iff_compact_smooth_tests (N : ℕ) [NeZero N] (f w : QuotientL2 N) :
    (f,w) ∈ (actualClosedGammaMaass N).adjoint.graph ↔ HasCompactSmoothTranspose N f w := by
  constructor
  · intro h ψ hc hψ
    exact actual_adjoint_compact_smooth_weak N h ψ hc hψ
  · intro h
    apply actual_adjoint_graph_of_finite_seed_tests N
    intro s
    have hc : HasCompactSupport (finiteCoreFunction Finset.univ (seedTensors s)) :=
      HasCompactSupport.of_support_subset_isCompact
        (finiteCompactTensorSupportK_isCompact Finset.univ (seedTensors s))
        (finiteCoreFunction_support_subset Finset.univ (seedTensors s))
    have hsm : ContDiffOn ℝ ∞
        (extendUpper (finiteCoreFunction Finset.univ (seedTensors s))) positiveChart := by
      rw [extendUpper_finiteCoreFunction]
      exact (finiteSmoothChart_contDiff Finset.univ s.2).contDiffOn
    simpa only [upperMaass_finiteCoreFunction] using
      h (finiteCoreFunction Finset.univ (seedTensors s)) hc hsm

/-- Exact NATIVE closed-operator graph characterization. Global quotient
L2 is required for BOTH f and w, and local smooth compact H tests supply
the differential relation; this is stronger than a local PDE statement. -/
theorem actual_closed_graph_iff_compact_smooth_tests (N : ℕ) [NeZero N] (f w : QuotientL2 N) :
    (f,w) ∈ (actualClosedGammaMaass N).graph ↔ HasCompactSmoothTranspose N f w := by
  have hadjoint : (actualClosedGammaMaass N).adjoint = actualClosedGammaMaass N :=
    (LinearPMap.isSelfAdjoint_def).mp (actual_minimal_closure_isSelfAdjoint N)
  simpa only [hadjoint] using actual_adjoint_graph_iff_compact_smooth_tests N f w

/-- Native domain membership requires the existence of an ORIGINAL
quotient L2 distributional Maass output, not an assumed form vector. -/
theorem actual_closed_domain_iff_compact_smooth_transpose (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    f ∈ (actualClosedGammaMaass N).domain ↔ ∃ w : QuotientL2 N, HasCompactSmoothTranspose N f w := by
  constructor
  · intro hf
    let u : (actualClosedGammaMaass N).domain := ⟨f,hf⟩
    refine ⟨actualClosedGammaMaass N u,?_⟩
    exact (actual_closed_graph_iff_compact_smooth_tests N f _).mp (LinearPMap.mem_graph _ u)
  · rintro ⟨w,hw⟩
    have hgraph := (actual_closed_graph_iff_compact_smooth_tests N f w).mpr hw
    obtain ⟨u,hu,hAu⟩ := LinearPMap.mem_graph_iff.mp hgraph
    simpa only [hu] using u.property

/-- Global quotient L2 weak output is unique, by the actual right-unique
native operator graph obtained from compact testing. -/
theorem compact_smooth_transpose_output_unique (N : ℕ) [NeZero N]
    (f w₁ w₂ : QuotientL2 N) (h₁ : HasCompactSmoothTranspose N f w₁)
    (h₂ : HasCompactSmoothTranspose N f w₂) : w₁ = w₂ := by
  obtain ⟨u₁,hu₁,hAu₁⟩ := LinearPMap.mem_graph_iff.mp
    ((actual_closed_graph_iff_compact_smooth_tests N f w₁).mpr h₁)
  obtain ⟨u₂,hu₂,hAu₂⟩ := LinearPMap.mem_graph_iff.mp
    ((actual_closed_graph_iff_compact_smooth_tests N f w₂).mpr h₂)
  have hueq : u₁ = u₂ := Subtype.ext (hu₁.trans hu₂.symm)
  exact hAu₁.symm.trans ((congrArg (actualClosedGammaMaass N) hueq).trans hAu₂)

end
end ImbalancedChen.Part3.GammaNativeGraphCompactTranspose20261026b
