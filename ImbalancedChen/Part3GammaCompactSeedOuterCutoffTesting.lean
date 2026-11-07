import ImbalancedChen.Part3GammaActualCompactWeakSeedH1
import ImbalancedChen.Part3GammaActualQuotientCutoffMultiplier
import ImbalancedChen.Part3GammaCompactSeedGraphTransport
import ImbalancedChen.Part3Gamma0ActualMinimalAdjointDefect

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
An outer actual modular cutoff that is one on a compact SOURCE carrier
does not change Hilbert testing against the full Poincare seed input OR
its native output. Actual invariance transports the plateau through every
translate in the full series; no seed/Poincare pointwise identification
or reduced-carrier support restriction is used. Native defect testing can
therefore be replaced by testing against an honest cutoff form vector.
-/

namespace ImbalancedChen.Part3.GammaCompactSeedOuterCutoffTesting20261026b
noncomputable section
open Set Function Filter MeasureTheory
open scoped UpperHalfPlane
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open Gamma0CarrierMeasurableInverse20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open Gamma0CompactTensorPoincareLocalFinite20261025a Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0CompactLaplacianSeed20261025a Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualSmoothQuotientMaassGraph20261025a Gamma0ActualMinimalShiftRange20261025a
open Gamma0ActualMinimalAdjointDefect20261025a Gamma0ActualAdjointInteriorWeakEquation20261025a
open Gamma0ActualMaassClosedOperator20261025a GammaCompactSeedGraphTransport20261026a
open GammaSmoothMultiplierLegalTests20261026a GammaActualQuotientCutoffMultiplier20261026b
open ActualModularSmoothCuspCutoff20261025a ActualModularSmoothCutoffL2Tail20261025a
open MaassWeakOperatorCore20261024zz

/-- The entire actual Poincare seed, not merely its original source,
is supported where the invariant outer cutoff equals one. -/
theorem Poincare_outer_cutoff_saturation (N : ℕ) [NeZero N]
    (a : UpperHalfPlane → ℂ) {K : Set UpperHalfPlane} (hs : Function.support a ⊆ K)
    (Y : ℝ) (hplateau : ∀ z ∈ K, globalCutoff Y z = 1) :
    ∀ᵐ q ∂carrierPushforward N,
      (quotientCutoff N Y q : ℂ) * complexPoincare N a q = complexPoincare N a q := by
  filter_upwards [reducedProjection_range_ae N] with q hq
  obtain ⟨z,rfl⟩ := hq
  rw [show reducedProjection N z = orbitProjection N z from rfl, quotientCutoff_projection]
  rw [← show reducedProjection N z = orbitProjection N z from rfl, complexPoincare_projection]
  by_cases hone : globalCutoff Y z = 1
  · simp [hone]
  · have hall : ∀ r : effectiveGamma0 N, a (effectiveMatrixAction N r z) = 0 := by
      intro r
      by_contra hn
      have h := hplateau _ (hs hn)
      rw [effectiveMatrixAction, globalCutoff_sl2_invariant] at h
      exact hone h
    simp only [complexSeedTrace, translatedSeed, hall, tsum_zero, mul_zero]

theorem compact_periodized_inner_outer_cutoff_eq (N : ℕ) [NeZero N]
    (a : UpperHalfPlane → ℂ) {K : Set UpperHalfPlane} (hs : Function.support a ⊆ K)
    (A f : QuotientL2 N)
    (hA : (A : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N] complexPoincare N a)
    (Y : ℝ) (hY : 1 < Y) (hplateau : ∀ z ∈ K, globalCutoff Y z = 1) :
    inner ℂ A (actualQuotientCutoffMultiplier N Y hY f) = inner ℂ A f := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hA, actualQuotientCutoffMultiplier_coe_ae N Y hY f,
    Poincare_outer_cutoff_saturation N a hs Y hplateau] with q hq hcut hsat
  simp only [Pi.mul_apply, actualCutoff_quotientMultiplier] at hcut
  have hstar : star (complexPoincare N a q) * (quotientCutoff N Y q : ℂ) =
      star (complexPoincare N a q) := by
    have h := congrArg star hsat
    simpa only [star_mul, Complex.star_def, Complex.conj_ofReal, mul_comm] using h
  simp only [RCLike.inner_apply', Complex.star_def] at hstar ⊢
  rw [hq, hcut]
  calc
    _ = (star (complexPoincare N a q) * (quotientCutoff N Y q : ℂ)) * f q := by
      simp only [Complex.star_def]
      ring
    _ = _ := by rw [hstar]; rfl

/-- Both original finite seed coordinates retain the same source support
container. In particular all second-order output terms are included. -/
theorem finite_seed_shift_outer_cutoff_eq (N : ℕ) [NeZero N]
    (s : SmoothSeed) (f : QuotientL2 N)
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hsK : finiteCompactTensorSupportK Finset.univ (seedTensors s) ⊆ K)
    (Y : ℝ) (hY : 1 < Y) (hplateau : ∀ z ∈ K, globalCutoff Y z = 1) :
    inner ℂ (seedVector N s + seedOutput N s) (actualQuotientCutoffMultiplier N Y hY f) =
      inner ℂ (seedVector N s + seedOutput N s) f := by
  have hi : (seedVector N s : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N (finiteCoreFunction Finset.univ (seedTensors s)) := by
    rw [← compactInput_finiteTensor_eq N s.2 K hK
      ((finiteCoreFunction_support_subset Finset.univ (seedTensors s)).trans hsK)]
    exact compactInput_ae N _ (finiteTensor_nativeC2 s.2) K hK _
  have ho : (seedOutput N s : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N (finiteCoreLaplacian Finset.univ (seedTensors s)) := by
    rw [← compactOutput_finiteTensor_eq N s.2 K hK
      ((finiteCoreFunction_support_subset Finset.univ (seedTensors s)).trans hsK)]
    simpa only [upperMaass_finiteCoreFunction] using
      compactOutput_ae N _ (finiteTensor_nativeC2 s.2) K hK
        ((finiteCoreFunction_support_subset Finset.univ (seedTensors s)).trans hsK)
  rw [inner_add_left, inner_add_left,
    compact_periodized_inner_outer_cutoff_eq N _
      ((finiteCoreFunction_support_subset Finset.univ (seedTensors s)).trans hsK) _ f hi Y hY hplateau,
    compact_periodized_inner_outer_cutoff_eq N _
      ((finiteCoreLaplacian_support_subset Finset.univ (seedTensors s)).trans hsK) _ f ho Y hY hplateau]

theorem actual_defect_finite_seed_outer_cutoff_test (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N) (s : SmoothSeed)
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hsK : finiteCompactTensorSupportK Finset.univ (seedTensors s) ⊆ K)
    (Y : ℝ) (hY : 1 < Y) (hplateau : ∀ z ∈ K, globalCutoff Y z = 1) :
    inner ℂ (seedVector N s + seedOutput N s) (actualQuotientCutoffMultiplier N Y hY f) = 0 := by
  rw [finite_seed_shift_outer_cutoff_eq N s f hK hsK Y hY hplateau]
  obtain ⟨u,hu,hAu⟩ := LinearPMap.mem_graph_iff.mp (seedPair_mem_actualClosed_graph N s)
  have h := (mem_minimalShiftDefect_iff_inner N f).mp hf u
  simpa only [hu,hAu] using h

end
end ImbalancedChen.Part3.GammaCompactSeedOuterCutoffTesting20261026b
