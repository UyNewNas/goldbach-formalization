import ImbalancedChen.Part3GammaFixedCutoffFiniteTensorGraphErrors

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

For fixed Y, arbitrary actual closed-operator graph data after cutoff have
ORIGINAL finite smooth-tensor graph approximants whose physical inputs
all have support in ONE fixed quotientTruncatedCarrier. The source box and
quotient truncation are chosen BEFORE the closed graph pair and index.
The diagonal uses genuine localized C2 graph errors and the actual native
cutoff output limit, not an assumed support-preserving graph density.
-/

namespace ImbalancedChen.Part3.GammaFixedCutoffOriginalCoreLocalization20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open MaassWeakOperatorCore20261024zz Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0SmoothCompactTensorCore20261025a Gamma0CompactTensorQuotientL2Core20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a Gamma0QuotientCellPushforward20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0ActualMaassClosedOperator20261025a Gamma0ActualEnergyCompletion20261025a
open GammaSmoothMultiplierPeriodization20261026a GammaSmoothMultiplierLegalTests20261026a
open GammaActualQuotientCutoffMultiplier20261026b GammaActualCutoffCoreGraphOutput20261026b
open GammaActualCutoffCommutatorExtension20261026b GammaActualClosedGraphGradientEnergy20261026b
open GammaMinimalPairFormApproximation20261026b GammaSeedJetErrorTransfer20261026a
open GammaFixedCutoffSourceReseeding20261026b GammaFixedCutoffFiniteTensorGraphErrors20261026b
open GammaCompactSeedCutoffPlateau20261026a ActualModularSmoothCuspCutoff20261025a
open ActualModularCutoffMaassBudget20261025a ActualModularCutoffCompactSupport20261025a

/-- A true compact-source plateau converts a common source support into
one fixed compact QUOTIENT support for the original finite Poincare raw
representative, with no group-orbit support-invariance premise. -/
theorem finite_tensor_quotient_support_of_seed_band
    (N : ℕ) [NeZero N] (a b : ℝ) (ha : 0 < a) {n : ℕ} (T : Fin n → SmoothCompactTensor)
    (hT : Function.support (finiteCoreFunction Finset.univ (fun i => (T i).toCompactTensor)) ⊆
      plateauBand a b) :
    HasCompactSupport (quotientTensorPoincare N Finset.univ (fun i => (T i).toCompactTensor)) ∧
      Function.support (quotientTensorPoincare N Finset.univ (fun i => (T i).toCompactTensor)) ⊆
        quotientTruncatedCarrier N (2*plateauThreshold a b) := by
  let Z := plateauThreshold a b
  let f := finiteCoreFunction Finset.univ (fun i => (T i).toCompactTensor)
  have hZ1 : 1 ≤ Z := by
    have hm := le_max_left (2 : ℝ) (max (b+1) (2/a))
    dsimp only [Z,plateauThreshold]
    linarith
  have hseed : complexGlobalH Z*f = f := by
    funext z
    by_cases hz : f z = 0
    · simp only [Pi.mul_apply,hz,mul_zero]
    · have hone := globalCutoff_eq_one_on_band a b ha Z le_rfl z (hT hz)
      simp only [Pi.mul_apply,complexGlobalH,hone,Complex.ofReal_one,one_mul]
  have htrace : complexGlobalH Z*smoothFinitePoincare N Finset.univ T =
      smoothFinitePoincare N Finset.univ T := by
    have hh := complexSeedTrace_mul_invariant N (complexGlobalH Z) f (actualCutoff_isGammaInvariant N Z)
    rw [hseed] at hh
    exact hh.symm
  have hquot : quotientMultiplier N (complexGlobalH Z) (actualCutoff_isGammaInvariant N Z) *
      quotientTensorPoincare N Finset.univ (fun i => (T i).toCompactTensor) =
      quotientTensorPoincare N Finset.univ (fun i => (T i).toCompactTensor) := by
    funext q
    exact Quotient.inductionOn q (fun z => congrFun htrace z)
  have hs : Function.support (quotientTensorPoincare N Finset.univ (fun i => (T i).toCompactTensor)) ⊆
      quotientTruncatedCarrier N (2*Z) := by
    intro q hq
    apply quotientCutoff_support_subset N Z hZ1
    intro hzero
    have hh := congrFun hquot q
    simp only [Pi.mul_apply,actualCutoff_quotientMultiplier,hzero,Complex.ofReal_zero,zero_mul] at hh
    exact hq hh.symm
  letI := quotient_t2 N
  exact ⟨HasCompactSupport.of_support_subset_isCompact (quotientTruncatedCarrier_isCompact N (2*Z)) hs,hs⟩

/-- Fixed-Y ORIGINAL finite-tensor common-support graph approximation.
The quotient height H depends only on the fixed cutoff construction;
it is chosen before f,w, the core approximation and its index. -/
theorem exists_fixed_cutoff_original_core_graph_localization
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    ∃ H : ℝ, 0 < H ∧ ∀ f w : QuotientL2 N,
      (f,w) ∈ (actualClosedGammaMaass N).graph →
      ∃ (dims : ℕ → ℕ) (T : ∀ k : ℕ, Fin (dims k) → SmoothCompactTensor),
        Tendsto (fun k => (seedVector N ⟨dims k,T k⟩,seedOutput N ⟨dims k,T k⟩)) atTop
          (𝓝 (actualQuotientCutoffMultiplier N Y hY f,
            actualQuotientCutoffMultiplier N Y hY w+actualCutoffCommutator N Y hY (graphEnergyLift N f w))) ∧
        ∀ k : ℕ,
          (seedVector N ⟨dims k,T k⟩,seedOutput N ⟨dims k,T k⟩) ∈ coreGraph N ∧
          (((seedVector N ⟨dims k,T k⟩ : QuotientL2 N) : Gamma0OrbitSpace N → ℂ)
            =ᵐ[carrierPushforward N]
              quotientTensorPoincare N Finset.univ (fun i => (T k i).toCompactTensor)) ∧
          HasCompactSupport (quotientTensorPoincare N Finset.univ (fun i => (T k i).toCompactTensor)) ∧
          Function.support (quotientTensorPoincare N Finset.univ (fun i => (T k i).toCompactTensor)) ⊆
            quotientTruncatedCarrier N H := by
  obtain ⟨S⟩ := exists_fixedSmoothCutoffSeed N Y hY
  obtain ⟨A,a,b,hA,ha,hab,happrox⟩ := exists_fixed_source_finite_tensor_graph_errors N Y hY S
  let K := liftedBox (A+1) (a/2) (b+1)
  have hK : IsCompact K := liftedBox_isCompact _ _ _ (half_pos ha)
  obtain ⟨a',b',ha',hab',hband,_⟩ := exists_compact_seed_plateau_parameters hK
  refine ⟨2*plateauThreshold a' b',mul_pos (by norm_num) (plateauThreshold_pos a' b'),?_⟩
  intro f w hgraph
  obtain ⟨u,e,hp,hL,he,hproj,ht,hgrad,henergy⟩ := exists_minimal_pair_form_approximation N f w hgraph
  have heq : e = graphEnergyLift N f w :=
    (physicalProjection_injective N) (hproj.trans (graphEnergyLift_projection N hgraph).symm)
  have hE : Tendsto (fun k => coreEmbedding N (u k)) atTop (𝓝 (graphEnergyLift N f w)) := by
    simpa only [heq] using he
  have hInput := ((actualQuotientCutoffMultiplier N Y hY).continuous.tendsto f).comp hp
  have hOutput : Tendsto (fun k => cutoffCoreOutputLinear N Y hY (u k)) atTop
      (𝓝 (actualQuotientCutoffMultiplier N Y hY w+
        actualCutoffCommutator N Y hY (graphEnergyLift N f w))) := by
    have hsum := (((actualQuotientCutoffMultiplier N Y hY).continuous.tendsto w).comp hL).add
      (((actualCutoffCommutator N Y hY).continuous.tendsto (graphEnergyLift N f w)).comp hE)
    apply hsum.congr'
    exact Eventually.of_forall (fun k => by
      rw [actualCutoffCommutator_core]
      change _ = actualQuotientCutoffMultiplier N Y hY (coreLaplacian N (u k)) +
        (cutoffCoreOutputLinear N Y hY (u k)-actualQuotientCutoffMultiplier N Y hY (coreLaplacian N (u k)))
      abel)
  have hActual := hInput.prodMk_nhds hOutput
  let rate : ℕ → ℝ := fun k => 1/((k : ℝ)+1)
  have hrate : ∀ k : ℕ, 0 < rate k := by intro k; dsimp only [rate]; positivity
  choose dims T hT herr using fun k => happrox (u k) (rate k) (hrate k)
  refine ⟨dims,T,?_,?_⟩
  · apply tendsto_iff_dist_tendsto_zero.mpr
    have hbound : ∀ k : ℕ,
        dist (seedVector N ⟨dims k,T k⟩,seedOutput N ⟨dims k,T k⟩)
          (actualQuotientCutoffMultiplier N Y hY f,
            actualQuotientCutoffMultiplier N Y hY w+actualCutoffCommutator N Y hY (graphEnergyLift N f w)) ≤
        rate k+dist (actualQuotientCutoffMultiplier N Y hY (physicalCore N (u k)),cutoffCoreOutputLinear N Y hY (u k))
          (actualQuotientCutoffMultiplier N Y hY f,
            actualQuotientCutoffMultiplier N Y hY w+actualCutoffCommutator N Y hY (graphEnergyLift N f w)) := by
      intro k
      apply (dist_triangle _ _ _).trans
      exact add_le_add_right (by simpa only [dist_comm] using (herr k).le) _
    apply squeeze_zero (fun k => dist_nonneg) hbound
    simpa only [zero_add] using
      (show Tendsto rate atTop (𝓝 0) from tendsto_one_div_add_atTop_nhds_zero_nat).add
        (tendsto_iff_dist_tendsto_zero.mp hActual)
  · intro k
    have hs := finite_tensor_quotient_support_of_seed_band N a' b' ha' (T k) ((hT k).trans hband)
    exact ⟨Submodule.subset_span ⟨⟨dims k,T k⟩,rfl⟩,
      (quotientTensorPoincare_memLp_two N Finset.univ (fun i => (T k i).toCompactTensor)).coeFn_toLp,
      hs.1,hs.2⟩

end
end ImbalancedChen.Part3.GammaFixedCutoffOriginalCoreLocalization20261026b
