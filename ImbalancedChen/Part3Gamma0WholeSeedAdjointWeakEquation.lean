import ImbalancedChen.Part3Gamma0CompactSeedL2PairingUnfolding
import ImbalancedChen.Part3GammaFiniteTensorGraphCore

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual minimal adjoint is tested against arbitrary compact smooth
H seeds. Constructive finite-tensor graph approximation puts the actual
Poincare input/output pair in the minimal graph; full unfolding then
gives the literal whole-H weak equation. There is no reduced-carrier
support premise. The finite SmoothSeed endpoint supplies the analytic
whole-plane mollification and local-H1 chain without a seam assumption.
-/

namespace ImbalancedChen.Part3.Gamma0WholeSeedAdjointWeakEquation20261026b
noncomputable section
open Set Function Filter MeasureTheory
open scoped UpperHalfPlane ContDiff
open MaassWeakOperatorCore20261024zz MaassFiniteCoreL2Graph20261025a
open Gamma0CompactTensorPoincareLocalFinite20261025a Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0CompactLaplacianSeed20261025a Gamma0SmoothCompactTensorCore20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0ActualMaassClosedOperator20261025a Gamma0ActualMinimalShiftRange20261025a
open Gamma0ActualMinimalAdjointDefect20261025a Gamma0ActualAdjointInteriorWeakEquation20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open GammaCompactSeedGraphTransport20261026a GammaFiniteTensorGraphCore20261026a
open ActualCompactSeedMaassJoin20261025a Gamma0CompactSeedL2PairingUnfolding20261026b

/-- The raw products are independently integrable against canonical
hyperbolic volume, although the automorphic pullback is only locally L2. -/
theorem compact_smooth_adjoint_products_integrable (N : ℕ) [NeZero N]
    (ψ : UpperHalfPlane → ℂ) (hψc : HasCompactSupport ψ)
    (hψ : ContDiffOn ℝ ∞ (extendUpper ψ) positiveChart) (f w : QuotientL2 N) :
    Integrable (fun z => star (upperMaass ψ z) * f (orbitProjection N z)) ∧
      Integrable (fun z => star (ψ z) * w (orbitProjection N z)) := by
  let hψ2 : nativeC2 ψ := hψ.of_le (by simp)
  have hs : Function.support ψ ⊆ tsupport ψ := subset_closure
  exact ⟨compact_seed_quotient_product_integrable N _
      (native_C2_upperMaass_continuous ψ hψ2) hψc
      (upperMaass_support_subset_closed ψ hψc.isClosed hs) f,
    compact_seed_quotient_product_integrable N ψ (native_C2_continuous ψ hψ2)
      hψc hs w⟩

/-- True native adjoint testing on every compact smooth H seed. Both
periodized coordinates belong to the actual minimal closed graph. -/
theorem actual_adjoint_compact_smooth_weak (N : ℕ) [NeZero N]
    {f w : QuotientL2 N} (hfw : (f,w) ∈ (actualClosedGammaMaass N).adjoint.graph)
    (ψ : UpperHalfPlane → ℂ) (hψc : HasCompactSupport ψ)
    (hψ : ContDiffOn ℝ ∞ (extendUpper ψ) positiveChart) :
    (∫ z : UpperHalfPlane, star (upperMaass ψ z) * f (orbitProjection N z)) =
      ∫ z : UpperHalfPlane, star (ψ z) * w (orbitProjection N z) := by
  obtain ⟨K, hK, hs, hclosed⟩ := compact_smooth_seed_graph_mem_closed N ψ hψc hψ
  let hψ2 : nativeC2 ψ := hψ.of_le (by simp)
  have hgraph : (compactInput N ψ hψ2 K hK hs, compactOutput N ψ hψ2 K hK hs) ∈
      (actualClosedGammaMaass N).graph := by
    rw [actualClosedGammaMaass_graph_eq]
    exact hclosed
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (actualClosedGammaMaass_dense_domain N)] at hfw
  have h := (Submodule.mem_adjoint_iff _ _).mp hfw
    (compactInput N ψ hψ2 K hK hs) (compactOutput N ψ hψ2 K hK hs) hgraph
  have heq := sub_eq_zero.mp h
  rw [compact_seed_L2_inner N (upperMaass ψ) (native_C2_upperMaass_continuous ψ hψ2)
      hK (upperMaass_support_subset_closed ψ hK.isClosed hs)
      _ f (compactOutput_ae N ψ hψ2 K hK hs),
    compact_seed_L2_inner N ψ (native_C2_continuous ψ hψ2) hK hs
      _ w (compactInput_ae N ψ hψ2 K hK hs)] at heq
  exact heq

/-- The actual negative-one defect has the whole-H transposed equation.
No equation, H1 regularity, cutoff, carrier support or gradient bound
occurs among its premises. -/
theorem actual_defect_compact_smooth_weak (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N)
    (ψ : UpperHalfPlane → ℂ) (hψc : HasCompactSupport ψ)
    (hψ : ContDiffOn ℝ ∞ (extendUpper ψ) positiveChart) :
    (∫ z : UpperHalfPlane, star (upperMaass ψ z + ψ z) * f (orbitProjection N z)) = 0 := by
  obtain ⟨K, hK, hs, hclosed⟩ := compact_smooth_seed_graph_mem_closed N ψ hψc hψ
  let hψ2 : nativeC2 ψ := hψ.of_le (by simp)
  have hgraph : (compactInput N ψ hψ2 K hK hs, compactOutput N ψ hψ2 K hK hs) ∈
      (actualClosedGammaMaass N).graph := by
    rw [actualClosedGammaMaass_graph_eq]
    exact hclosed
  obtain ⟨u, hu, hAu⟩ := LinearPMap.mem_graph_iff.mp hgraph
  have hzero := (mem_minimalShiftDefect_iff_inner N f).mp hf u
  rw [inner_add_left, hu, hAu,
    compact_seed_L2_inner N ψ (native_C2_continuous ψ hψ2) hK hs
      _ f (compactInput_ae N ψ hψ2 K hK hs),
    compact_seed_L2_inner N (upperMaass ψ) (native_C2_upperMaass_continuous ψ hψ2)
      hK (upperMaass_support_subset_closed ψ hK.isClosed hs)
      _ f (compactOutput_ae N ψ hψ2 K hK hs)] at hzero
  obtain ⟨ho, hi⟩ := compact_smooth_adjoint_products_integrable N ψ hψc hψ f f
  simp_rw [star_add, add_mul]
  rw [integral_add ho hi]
  exact (add_comm _ _).trans hzero

/-- Literal original finite-tensor ABI, now with no reducedCarrier
restriction. This supplies WholeSeedAdjointTests used by local regularity. -/
theorem actual_defect_whole_finite_seed_tests (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N) (s : SmoothSeed) :
    (∫ z : UpperHalfPlane,
      star (finiteCoreLaplacian Finset.univ (seedTensors s) z +
        finiteCoreFunction Finset.univ (seedTensors s) z) * f (orbitProjection N z)) = 0 := by
  have hc : HasCompactSupport (finiteCoreFunction Finset.univ (seedTensors s)) :=
    HasCompactSupport.of_support_subset_isCompact
      (finiteCompactTensorSupportK_isCompact Finset.univ (seedTensors s))
      (finiteCoreFunction_support_subset Finset.univ (seedTensors s))
  have hsm : ContDiffOn ℝ ∞
      (extendUpper (finiteCoreFunction Finset.univ (seedTensors s))) positiveChart := by
    rw [extendUpper_finiteCoreFunction]
    exact (finiteSmoothChart_contDiff Finset.univ s.2).contDiffOn
  simpa only [upperMaass_finiteCoreFunction] using
    actual_defect_compact_smooth_weak N f hf _ hc hsm

end
end ImbalancedChen.Part3.Gamma0WholeSeedAdjointWeakEquation20261026b
