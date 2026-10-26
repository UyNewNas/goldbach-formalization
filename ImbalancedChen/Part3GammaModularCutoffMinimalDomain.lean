import ImbalancedChen.Part3GammaFiniteTensorGraphCore
import ImbalancedChen.Part3ActualModularCutoffSmoothSeed
import ImbalancedChen.Part3ActualModularCutoffMaassBudget

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The actual smooth modular cutoff and its EXISTING actual quotientMaass
output form a pair in the ACTUAL minimal closed differential graph. The
compact smooth normalized seed is genuinely constructed by the previous
source, its true Poincare/Maass identity supplies the output dictionary,
and the constructive finite tensor graph-core theorem supplies membership.

No hCoreMembership, desired graph convergence, form domain, constant
kernel or cutoff membership premise is supplied. Canonical L2 consumers
may use any representatives with the two stated raw a.e. identities.
-/

namespace ImbalancedChen.Part3.GammaModularCutoffMinimalDomain20261026a

noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open Gamma0CarrierMeasurableInverse20261025a Gamma0QuotientConullTransport20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a
open ActualCompactSeedMaassJoin20261025a
open ActualModularSmoothCuspCutoff20261025a ActualModularSmoothCutoffL2Tail20261025a
open ActualModularCutoffSmoothSeed20261025a ActualModularCutoffMaassBudget20261025a
open Gamma0ActualMaassClosedOperator20261025a
open Gamma0ActualMinimalFriedrichsInclusion20261025a Gamma0ActualFriedrichsOperator20261025a
open GammaFiniteTensorGraphCore20261026a

/-- The exact requested raw cutoff-pair endpoint. The actual canonical
cutoff construction, finite tensor approximation and graph norm transport
remove all previously missing core-membership and graph-limit obligations. -/
theorem cutoff_ae_pair_mem_closedGraph
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    (u v : Lp ℂ 2 (carrierPushforward N))
    (hu : (u : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      (fun q => (quotientCutoff N Y q : ℂ)))
    (hv : (v : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      quotientCutoffMaass N Y (lt_trans (by norm_num) hY)) :
    (u,v) ∈ closedGammaGraph N := by
  obtain ⟨f, hfc, hfs, hreconstruct⟩ :=
    exists_compact_cinfty_seed_reconstructing_globalCutoff N Y hY.le
  have htrace : complexSeedTrace N f = complexGlobalH Y := funext hreconstruct
  have hin : complexPoincare N f =ᵐ[carrierPushforward N]
      (fun q => (quotientCutoff N Y q : ℂ)) := by
    filter_upwards [reducedProjection_range_ae N] with q hq
    obtain ⟨z, rfl⟩ := hq
    rw [complexPoincare_projection]
    exact hreconstruct z
  have hout : complexPoincare N (upperMaass f) =ᵐ[carrierPushforward N]
      quotientCutoffMaass N Y (lt_trans (by norm_num) hY) := by
    filter_upwards [reducedProjection_range_ae N] with q hq
    obtain ⟨z, rfl⟩ := hq
    rw [complexPoincare_projection]
    change complexSeedTrace N (upperMaass f) (z : UpperHalfPlane) =
      upperMaass (complexGlobalH Y) z
    rw [← upperMaass_compactSeedTrace N f (hfs.of_le (by simp)) hfc (subset_tsupport f),
      htrace]
  exact compact_smooth_seed_ae_pair_mem_closedGraph N f hfc hfs u v
    (hu.trans hin.symm) (hv.trans hout.symm)

theorem cutoff_ae_pair_mem_minimalGraph
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    (u v : Lp ℂ 2 (carrierPushforward N))
    (hu : (u : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      (fun q => (quotientCutoff N Y q : ℂ)))
    (hv : (v : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      quotientCutoffMaass N Y (lt_trans (by norm_num) hY)) :
    (u,v) ∈ (actualClosedGammaMaass N).graph := by
  rw [actualClosedGammaMaass_graph_eq]
  exact cutoff_ae_pair_mem_closedGraph N Y hY u v hu hv

/-- Native minimal domain membership, not merely a representative-level
estimate or membership in an unspecified larger self-adjoint extension. -/
theorem cutoff_ae_mem_minimalDomain
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    (u v : Lp ℂ 2 (carrierPushforward N))
    (hu : (u : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      (fun q => (quotientCutoff N Y q : ℂ)))
    (hv : (v : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      quotientCutoffMaass N Y (lt_trans (by norm_num) hY)) :
    u ∈ (actualClosedGammaMaass N).domain :=
  LinearPMap.mem_domain_iff.mpr ⟨v, cutoff_ae_pair_mem_minimalGraph N Y hY u v hu hv⟩

/-- The separately proved inclusion into the actual Friedrichs graph
transports this concrete pair without any essential-self-adjointness claim. -/
theorem cutoff_ae_pair_mem_friedrichsGraph
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    (u v : Lp ℂ 2 (carrierPushforward N))
    (hu : (u : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      (fun q => (quotientCutoff N Y q : ℂ)))
    (hv : (v : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      quotientCutoffMaass N Y (lt_trans (by norm_num) hY)) :
    (u,v) ∈ (actualGammaFriedrichs N).graph :=
  closedGammaGraph_le_friedrichsGraph N (cutoff_ae_pair_mem_closedGraph N Y hY u v hu hv)

end
end ImbalancedChen.Part3.GammaModularCutoffMinimalDomain20261026a
