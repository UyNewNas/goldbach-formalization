import ImbalancedChen.Part3GammaFixedCutoffSourceReseeding
import ImbalancedChen.Part3CompactC2FiniteTensorApproximation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

For one fixed cutoff seed, every re-seeded original core product admits
genuine finite smooth tensor graph approximation on ONE fixed expanded
positive rectangle. The rectangle is chosen from sigma_Y BEFORE the core
vector and accuracy. Localized C2 mollification/quadrature is invoked with
that explicit rectangle; its six jets are transported to the actual native
quotient graph. No support-preserving graph-density premise is supplied.
-/

namespace ImbalancedChen.Part3.GammaFixedCutoffFiniteTensorGraphErrors20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0CompactTensorPoincareC2Core20261025a Gamma0SmoothCompactTensorCore20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0ActualEnergyCompletion20261025a Gamma0CompactCarrierBump20261025a
open Gamma0CompactUpperChartExtension20261025a CompactSeedSmoothPlaneExtension20261025a
open CompactProductKernelSixJet20261025a CompactC2FiniteTensorApproximation20261026a
open GammaSeedJetErrorTransfer20261026a GammaCompactSeedL2Transport20261026a
open GammaCompactSeedGraphTransport20261026a GammaFiniteTensorGraphCore20261026a
open GammaActualQuotientCutoffMultiplier20261026b GammaActualCutoffCoreGraphOutput20261026b
open GammaFixedCutoffSourceReseeding20261026b

theorem exists_fixed_source_finite_tensor_graph_errors
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (S : FixedSmoothCutoffSeed N Y) :
    ∃ A a b : ℝ, 0 ≤ A ∧ 0 < a ∧ a ≤ b ∧
      ∀ u : EnergyCore N, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ (n : ℕ) (T : Fin n → SmoothCompactTensor),
          Function.support (finiteCoreFunction Finset.univ (fun i => (T i).toCompactTensor)) ⊆
            liftedBox (A+1) (a/2) (b+1) ∧
          dist (actualQuotientCutoffMultiplier N Y hY (physicalCore N u),cutoffCoreOutputLinear N Y hY u)
            (seedVector N ⟨n,T⟩,seedOutput N ⟨n,T⟩) < epsilon := by
  obtain ⟨A,a,b,hA,ha,hab,hrect⟩ := compact_height_rectangle S.compact
  let K := liftedBox (A+1) (a/2) (b+1)
  have hK : IsCompact K := liftedBox_isCompact _ _ _ (half_pos ha)
  refine ⟨A,a,b,hA,ha,hab,?_⟩
  intro u epsilon hepsilon
  let G := reseed S u
  have hGs := reseed_smooth S u
  have hGc : HasCompactSupport G :=
    HasCompactSupport.of_support_subset_isCompact S.compact (reseed_support S u)
  have hts : tsupport G ⊆ tsupport S.seed := closure_minimal (reseed_support S u) isClosed_tsupport
  have hplane : tsupport (extendUpper G) ⊆ planeBox A a b := by
    intro p hp
    obtain ⟨z,hz,rfl⟩ := extendUpper_support_image G hGc hp
    exact hrect z (hts hz)
  let C := transportConstant N K
  let L := jetLoss (b+1)
  have hC : 0 ≤ C := transportConstant_nonneg N K
  have hL : 0 < L := jetLoss_pos _
  have hCp : 0 < C+1 := by positivity
  have hLp : 0 < L+1 := by positivity
  let eta := epsilon/(C+1)
  have heta : 0 < eta := div_pos hepsilon hCp
  let delta := eta/(L+1)
  have hdelta : 0 < delta := div_pos heta hLp
  obtain ⟨P⟩ := exists_compactC2TensorApproximation (extendUpper_cinfty G hGc hGs)
    (extendUpper_hasCompactSupport G hGc) A a b ha hplane delta hdelta
  obtain ⟨n,T,hchart⟩ := finset_tensor_enumeration P.indices P.tensors
  let g := finiteCoreFunction Finset.univ (fun i => (T i).toCompactTensor)
  have hext : extendUpper g = finiteChartFunction P.indices (fun i => (P.tensors i).toCompactTensor) := by
    change extendUpper (finiteCoreFunction Finset.univ (fun i => (T i).toCompactTensor)) = _
    rw [extendUpper_finiteCoreFunction,hchart]
  have hgK : Function.support g ⊆ K := by
    apply seed_support_liftedBox g (A+1) (a/2) (b+1)
    rw [hext]
    exact P.common_support
  have hGK : Function.support G ⊆ K := seed_support_liftedBox G _ _ _ P.source_support
  have hjets : ∀ p ∈ planeBox (A+1) (a/2) (b+1), ∀ ij : JetIndex,
      ‖partialJet ij (extendUpper G) p-partialJet ij (extendUpper g) p‖ ≤ delta := by
    intro p hp ij
    rw [hext]
    simpa only [norm_sub_rev] using (P.uniform_sixJet_error ⟨p,hp⟩ ij).le
  have herr := value_maass_errors_on_liftedBox G g (A+1) (a/2) (b+1) hdelta.le hjets
  have hsmallSeed : L*delta < eta := by
    dsimp only [delta]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hLp).mpr
    nlinarith
  have hv : ∀ z ∈ K, ‖G z-g z‖ ≤ eta := fun z hz => (herr.1 z hz).trans hsmallSeed.le
  have hD : ∀ z ∈ K, ‖upperMaass G z-upperMaass g z‖ ≤ eta :=
    fun z hz => (herr.2 z hz).trans hsmallSeed.le
  have hdist := compactGraphPair_distance_bound N G g (hGs.of_le (by simp))
    (finiteTensor_nativeC2 T) K hK hGK hgK heta.le hv hD
  have hInput : compactInput N G (hGs.of_le (by simp)) K hK hGK =
      actualQuotientCutoffMultiplier N Y hY (physicalCore N u) :=
    Lp.ext ((compactInput_ae N G _ K hK hGK).trans (reseed_input_ae S hY u).symm)
  have hOutput : compactOutput N G (hGs.of_le (by simp)) K hK hGK = cutoffCoreOutputLinear N Y hY u :=
    Lp.ext ((compactOutput_ae N G _ K hK hGK).trans (reseed_output_ae S hY u).symm)
  change dist (compactInput N G _ K hK hGK,compactOutput N G _ K hK hGK)
    (compactInput N g _ K hK hgK,compactOutput N g _ K hK hgK) ≤ C*eta at hdist
  rw [hInput,hOutput,compactInput_finiteTensor_eq N T K hK hgK,
    compactOutput_finiteTensor_eq N T K hK hgK] at hdist
  have hsmallGraph : C*eta < epsilon := by
    dsimp only [eta]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hCp).mpr
    nlinarith
  exact ⟨n,T,hgK,hdist.trans_lt hsmallGraph⟩

end
end ImbalancedChen.Part3.GammaFixedCutoffFiniteTensorGraphErrors20261026b
