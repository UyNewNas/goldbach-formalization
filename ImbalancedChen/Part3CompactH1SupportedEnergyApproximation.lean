import ImbalancedChen.Part3CompactH1PoincareFormDomain

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
A raw compact H1 Poincare form vector is returned TOGETHER with its genuine
normalized finite tensor approximation and one fixed compact SOURCE
container controlling BOTH original seed and Laplacian seed. The source
container is chosen before an outer plateau cutoff. No support sequence,
energy approximation or physical periodization identity is assumed.
-/
namespace ImbalancedChen.Part3.CompactH1SupportedEnergyApproximation20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open CompactC2ProductMollifier20261026a
open WeakH1ProductMollifierDerivative20261026a
open Gamma0SmoothCompactTensorCore20261025a MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareLocalFinite20261025a Gamma0CompactLaplacianSeed20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open GammaCompactSeedL2Transport20261026a GammaCompactSeedGraphTransport20261026a
open GammaCompactWeakSeedPoincareL220261026b GammaCompactWeakSeedL2Continuity20261026b
open Gamma0ActualEnergyCompletion20261025a
open LocalH1Tests20261026b LocalH1NormalizedTensorSequence20261026b LocalH1TensorDifferenceABI20261026b
open CompactH1QuotientEnergyLimit20261026b CompactH1CanonicalSeedL220261026b
open CompactH1PoincareFormDomain20261026b UpperRectangleMollifierGeometry20261026b

/-- Physical identification for ANY constructed normalized sequence and
its actual energy limit. This preserves the caller's fixed source family,
rather than returning an unrelated form lift of the same physical seed. -/
theorem normalized_energy_limit_physical_ae (N : ℕ) [NeZero N]
    {J : CompactH1Jet} {L R a b : ℝ} (P : NormalizedH1TensorSequence J L R a b)
    (ha : 0 < a) (hsJ : tsupport J.value ⊆ openRect L R a b)
    (e : EnergyCompletion N)
    (he : Tendsto (fun k => coreEmbedding N (familyEnergyCore N (P.tensors k))) atTop (𝓝 e)) :
    ((physicalProjection N e : QuotientL2 N) : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N (upperSeed J.value) := by
  obtain ⟨hSeq,hJ,hcanonical⟩ := normalized_canonical_seed_tendsto P ha hsJ
  let K := upperRectangle L R a b
  have hK : IsCompact K := upperRectangle_isCompact L R a b ha
  have hJs : Function.support (upperSeed J.value) ⊆ K := upperSeed_support_rectangle hsJ
  have hFs (k : ℕ) : Function.support (upperSeed (finiteChartFunction Finset.univ
      (fun i => (P.tensors k i).toCompactTensor))) ⊆ K :=
    (finiteCoreFunction_support_subset Finset.univ (fun i => (P.tensors k i).toCompactTensor)).trans
      (P.common_support k)
  have hquotient := weakSeedL2_tendsto N (upperSeed J.value) hJ
    (fun k => upperSeed (finiteChartFunction Finset.univ (fun i => (P.tensors k i).toCompactTensor)))
    hSeq K hK hJs hFs hcanonical
  have hident (k : ℕ) : weakSeedL2 N
      (upperSeed (finiteChartFunction Finset.univ (fun i => (P.tensors k i).toCompactTensor)))
      (hSeq k) K hK (hFs k) = physicalCore N (familyEnergyCore N (P.tensors k)) := by
    change weakSeedL2 N (finiteCoreFunction Finset.univ (fun i => (P.tensors k i).toCompactTensor))
      (hSeq k) K hK (hFs k) = seedVector N ⟨P.size k,P.tensors k⟩
    rw [weakSeedL2_eq_seedL2 N _ (continuous_finiteCoreFunction _ _) K hK (hFs k)]
    exact compactInput_finiteTensor_eq N (P.tensors k) K hK (hFs k)
  have hphysical : Tendsto (fun k => physicalCore N (familyEnergyCore N (P.tensors k))) atTop
      (𝓝 (weakSeedL2 N (upperSeed J.value) hJ K hK hJs)) := by
    simpa only [hident] using hquotient
  have hprojection : Tendsto (fun k => physicalCore N (familyEnergyCore N (P.tensors k))) atTop
      (𝓝 (physicalProjection N e)) := by
    simpa only [physicalProjection_core] using ((physicalProjection N).continuous.tendsto e).comp he
  have heq := tendsto_nhds_unique hprojection hphysical
  rw [heq]
  exact weakSeedL2_ae N (upperSeed J.value) hJ K hK hJs

/-- All source support, actual energy approximation, and raw physical
periodization data are returned SIMULTANEOUSLY. K is a compact source
container, not the automorphic support of the periodized test. -/
theorem compactH1_supported_energy_approximation (N : ℕ) [NeZero N]
    (J : CompactH1Jet) (hx : HasCompactSupport J.dx) (hy : HasCompactSupport J.dy)
    (L R a b : ℝ) (ha : 0 < a) (hLR : L < R) (hab : a < b)
    (hsJ : tsupport J.value ⊆ openRect L R a b) :
    ∃ (K : Set UpperHalfPlane) (P : NormalizedH1TensorSequence J L R a b) (e : EnergyCompletion N),
      IsCompact K ∧ K = upperRectangle L R a b ∧
      (∀ k, finiteCompactTensorSupportK Finset.univ (seedTensors (P.seed k)) ⊆ K) ∧
      (∀ k, Function.support (finiteCoreFunction Finset.univ (seedTensors (P.seed k))) ⊆ K ∧
        Function.support (finiteCoreLaplacian Finset.univ (seedTensors (P.seed k))) ⊆ K) ∧
      Tendsto (fun k => coreEmbedding N (familyEnergyCore N (P.tensors k))) atTop (𝓝 e) ∧
      ((physicalProjection N e : QuotientL2 N) : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
        complexPoincare N (upperSeed J.value) := by
  obtain ⟨P,e,he,hphysical⟩ := compactH1_has_quotient_energy_limit N J hx hy L R a b ha hLR hab hsJ
  refine ⟨upperRectangle L R a b,P,e,upperRectangle_isCompact L R a b ha,rfl,
    P.common_support,?_,he,normalized_energy_limit_physical_ae N P ha hsJ e he⟩
  intro k
  exact ⟨(finiteCoreFunction_support_subset Finset.univ (seedTensors (P.seed k))).trans (P.common_support k),
    (finiteCoreLaplacian_support_subset Finset.univ (seedTensors (P.seed k))).trans (P.common_support k)⟩

end
end ImbalancedChen.Part3.CompactH1SupportedEnergyApproximation20261026b
