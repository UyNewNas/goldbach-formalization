import ImbalancedChen.Part3GlobalFrickeHilbertInvolution

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO FORMAL CREDIT.

Actual Fricke pullback sends every ORIGINAL finite smooth seed graph
generator into the actual minimal closed graph, by the constructed
zero-chart compact seed and its proved original differential dictionary.
Linearity propagates through the original graph span, and continuity
through its original graph closure. Thus global canonical Fricke really
preserves the native minimal domain and intertwines its existing actual
closed Maass operator. No domain/core action or commutation is assumed.
-/

noncomputable section

namespace ImbalancedChen.Part3.GlobalFrickeMinimalDomainAction20261026b

open Set MeasureTheory Filter
open scoped UpperHalfPlane
open ImbalancedChen.Part3.GlobalFrickeHilbertInvolution20261026b
open ImbalancedChen.Part3.ActualHeckeSecondL220261026b
open ImbalancedChen.Part3.ZeroCuspOriginalTraceMinimalPair20261026b
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0ComplexL1PoincareUnfolding20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.Gamma0SmoothCompactTensorCore20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientMaassGraph20261025a
open ImbalancedChen.Part3.Gamma0ActualMaassClosedOperator20261025a
open ImbalancedChen.Part3.GammaCompactSeedGraphTransport20261026a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz

def frickePairLinear (N : ℕ) [NeZero N] (hN : 0 < N) :
    QuotientL2 N × QuotientL2 N →ₗ[ℂ] QuotientL2 N × QuotientL2 N :=
  (frickeL2 N hN).toLinearMap.prodMap (frickeL2 N hN).toLinearMap

theorem frickePairLinear_continuous (N : ℕ) [NeZero N] (hN : 0 < N) :
    Continuous (frickePairLinear N hN) :=
  ((frickeL2 N hN).continuous.comp continuous_fst).prodMk
    ((frickeL2 N hN).continuous.comp continuous_snd)

/-- Each actual original finite smooth tensor graph generator has a
constructed real-zero-chart minimal-domain image. -/
theorem fricke_seedPair_mem_closedGraph (N : ℕ) [NeZero N] (hN : 0 < N)
    (s : SmoothSeed) : frickePairLinear N hN (seedPair N s) ∈ closedGammaGraph N := by
  rcases s with ⟨n, T⟩
  let f := finiteCoreFunction Finset.univ (fun i => (T i).toCompactTensor)
  let K := finiteCompactTensorSupportK Finset.univ (fun i => (T i).toCompactTensor)
  have hK : IsCompact K := finiteCompactTensorSupportK_isCompact Finset.univ _
  have hs : Function.support f ⊆ K := finiteCoreFunction_support_subset Finset.univ _
  have hfc : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact hK hs
  have hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart := by
    dsimp only [f]
    rw [extendUpper_finiteCoreFunction]
    exact (finiteSmoothChart_contDiff Finset.univ T).contDiffOn
  have hin : (seedVector N ⟨n,T⟩ : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N f := by
    rw [← compactInput_finiteTensor_eq N T K hK hs]
    exact compactInput_ae N f (finiteTensor_nativeC2 T) K hK hs
  have hout : (seedOutput N ⟨n,T⟩ : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N (upperMaass f) := by
    rw [← compactOutput_finiteTensor_eq N T K hK hs]
    exact compactOutput_ae N f (finiteTensor_nativeC2 T) K hK hs
  have hU : frickeL2 N hN (seedVector N ⟨n,T⟩) = originalZeroInputL2 N hN f hfc hf := by
    apply Lp.ext
    exact (frickeL2_original_trace_ae N hN f _ hin).trans
      (originalZeroTraceQuotient_memLp_two N hN f hfc hf).coeFn_toLp.symm
  have hV : frickeL2 N hN (seedOutput N ⟨n,T⟩) = originalZeroOutputL2 N hN f hfc hf := by
    apply Lp.ext
    exact (frickeL2_original_trace_ae N hN (upperMaass f) _ hout).trans
      (originalZeroOutput_memLp_two N hN f hfc hf).coeFn_toLp.symm
  have hgraph := originalZero_pair_mem_minimalGraph N hN f hfc hf
  rw [actualClosedGammaMaass_graph_eq] at hgraph
  change (frickeL2 N hN (seedVector N ⟨n,T⟩), frickeL2 N hN (seedOutput N ⟨n,T⟩)) ∈ _
  rw [hU, hV]
  exact hgraph

/-- Linearity extends the actual generator action through the ORIGINAL
core graph span; no algebraic-core invariance is falsely claimed. -/
theorem fricke_coreGraph_le_closed_preimage (N : ℕ) [NeZero N] (hN : 0 < N) :
    coreGraph N ≤ (closedGammaGraph N).comap (frickePairLinear N hN) := by
  apply Submodule.span_le.mpr
  rintro p ⟨s, rfl⟩
  exact fricke_seedPair_mem_closedGraph N hN s

/-- The preimage of the genuine closed graph is closed. It contains the
original graph span, hence its closure, proving native GLOBAL action. -/
theorem fricke_closedGraph_action (N : ℕ) [NeZero N] (hN : 0 < N)
    {f g : QuotientL2 N} (hfg : (f,g) ∈ closedGammaGraph N) :
    (frickeL2 N hN f, frickeL2 N hN g) ∈ closedGammaGraph N := by
  have hsub : (coreGraph N : Set (QuotientL2 N × QuotientL2 N)) ⊆
      (frickePairLinear N hN) ⁻¹' (closedGammaGraph N : Set _) :=
    fun p hp => fricke_coreGraph_le_closed_preimage N hN hp
  have hclosed : IsClosed ((frickePairLinear N hN) ⁻¹' (closedGammaGraph N : Set _)) :=
    (closedGammaGraph_isClosed N).preimage (frickePairLinear_continuous N hN)
  exact (closure_minimal hsub hclosed) hfg

theorem fricke_minimalGraph_action (N : ℕ) [NeZero N] (hN : 0 < N)
    {f g : QuotientL2 N} (hfg : (f,g) ∈ (actualClosedGammaMaass N).graph) :
    (frickeL2 N hN f, frickeL2 N hN g) ∈ (actualClosedGammaMaass N).graph := by
  rw [actualClosedGammaMaass_graph_eq] at hfg ⊢
  exact fricke_closedGraph_action N hN hfg

theorem fricke_minimalDomain_action (N : ℕ) [NeZero N] (hN : 0 < N)
    {f : QuotientL2 N} (hf : f ∈ (actualClosedGammaMaass N).domain) :
    frickeL2 N hN f ∈ (actualClosedGammaMaass N).domain := by
  obtain ⟨g, hg⟩ := LinearPMap.mem_domain_iff.mp hf
  exact LinearPMap.mem_domain_iff.mpr ⟨frickeL2 N hN g, fricke_minimalGraph_action N hN hg⟩

/-- An actual typed native-domain action, constructed from derived graph action. -/
def minimalFrickeDomain (N : ℕ) [NeZero N] (hN : 0 < N)
    (u : (actualClosedGammaMaass N).domain) : (actualClosedGammaMaass N).domain :=
  ⟨frickeL2 N hN u, fricke_minimalDomain_action N hN u.property⟩

theorem actualClosedMaass_fricke (N : ℕ) [NeZero N] (hN : 0 < N)
    (u : (actualClosedGammaMaass N).domain) :
    actualClosedGammaMaass N (minimalFrickeDomain N hN u) =
      frickeL2 N hN (actualClosedGammaMaass N u) := by
  have hgraph := fricke_closedGraph_action N hN (actualClosedGammaMaass_mem_graph N u)
  exact closedGammaGraph_right_unique N
    (actualClosedGammaMaass_mem_graph N (minimalFrickeDomain N hN u)) hgraph

/-- The original native minimal domain has a genuine Fricke involutive
linear isometry equivalence in its inherited actual quotient L2 norm. -/
def minimalFrickeDomainEquiv (N : ℕ) [NeZero N] (hN : 0 < N) :
    (actualClosedGammaMaass N).domain ≃ₗᵢ[ℂ] (actualClosedGammaMaass N).domain where
  toFun := minimalFrickeDomain N hN
  invFun := minimalFrickeDomain N hN
  left_inv u := Subtype.ext (frickeL2_involutive N hN u)
  right_inv u := Subtype.ext (frickeL2_involutive N hN u)
  map_add' u v := Subtype.ext ((frickeL2 N hN).map_add u v)
  map_smul' c u := Subtype.ext ((frickeL2 N hN).map_smul c u)
  norm_map' u := (frickeL2 N hN).norm_map u

end ImbalancedChen.Part3.GlobalFrickeMinimalDomainAction20261026b
