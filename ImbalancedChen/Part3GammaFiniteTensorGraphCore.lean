import ImbalancedChen.Part3GammaSeedJetErrorTransfer
import ImbalancedChen.Part3CompactC2FiniteTensorApproximation
import ImbalancedChen.Part3Gamma0ActualMinimalFriedrichsInclusion
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.SpecificLimits.Basic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Finite smooth tensor approximation is transported to the ACTUAL Gamma0
quotient graph. Euclidean finite-jet approximation is supplied by its
constructive theorem, not by a density or desired-graph-limit hypothesis.
The approximating pairs are exact original coreGraph generators. Closure
then gives compact smooth periodized seeds in the minimal closed domain.
No arbitrary compact smooth function is inserted into the algebraic core.
-/

namespace ImbalancedChen.Part3.GammaFiniteTensorGraphCore20261026a

noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane ENNReal
open MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0SmoothCompactTensorCore20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0ActualMaassClosedOperator20261025a
open GammaCompactSeedL2Transport20261026a GammaCompactSeedGraphTransport20261026a
open GammaSeedJetErrorTransfer20261026a CompactProductKernelSixJet20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a Gamma0QuotientCellPushforward20261025a

/-- Genuine finite reindexing into the ORIGINAL SmoothSeed ABI. The same
smooth compact factors are copied; no representation premise is needed. -/
theorem finset_tensor_enumeration {ι : Type*} (s : Finset ι)
    (T : ι → SmoothCompactTensor) :
    ∃ (n : ℕ) (U : Fin n → SmoothCompactTensor),
      finiteChartFunction Finset.univ (fun i => (U i).toCompactTensor) =
        finiteChartFunction s (fun i => (T i).toCompactTensor) := by
  classical
  let e := Fintype.equivFin s
  let U : Fin (Fintype.card s) → SmoothCompactTensor := fun i => T (e.symm i).val
  refine ⟨Fintype.card s, U, ?_⟩
  funext p
  change (∑ i : Fin (Fintype.card s),
      (T (e.symm i).val).horizontal p.1 * (T (e.symm i).val).vertical p.2) =
    ∑ i ∈ s, (T i).horizontal p.1 * (T i).vertical p.2
  simpa only [Finset.sum_coe_sort] using
    (e.symm.sum_comp (fun i : s => (T i.val).horizontal p.1 * (T i.val).vertical p.2))

/-- Internal pointwise approximation-to-closure argument. Its input is
explicit finite tensor seed error, never a presumed graph limit. The public
compact-smooth theorem below obtains these errors from the constructive
Euclidean mollifier/quadrature theorem. -/
private theorem closed_graph_of_finite_seed_errors
    (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ) (hf : nativeC2 f)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hs : Function.support f ⊆ K)
    (happrox : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ (n : ℕ) (T : Fin n → SmoothCompactTensor)
        (hT : Function.support (finiteCoreFunction Finset.univ
          (fun i => (T i).toCompactTensor)) ⊆ K),
        (∀ z ∈ K, ‖f z - finiteCoreFunction Finset.univ
          (fun i => (T i).toCompactTensor) z‖ ≤ epsilon) ∧
        (∀ z ∈ K, ‖upperMaass f z - upperMaass (finiteCoreFunction Finset.univ
          (fun i => (T i).toCompactTensor)) z‖ ≤ epsilon)) :
    compactGraphPair N f hf K hK hs ∈ closedGammaGraph N := by
  change compactGraphPair N f hf K hK hs ∈ closure (coreGraph N : Set _)
  apply Metric.mem_closure_iff.mpr
  intro epsilon he
  let C := transportConstant N K
  have hC : 0 ≤ C := transportConstant_nonneg N K
  have hCp : 0 < C + 1 := by positivity
  let delta := epsilon / (C + 1)
  have hd : 0 < delta := div_pos he hCp
  obtain ⟨n, T, hT, hvalue, hlap⟩ := happrox delta hd
  refine ⟨compactGraphPair N _ (finiteTensor_nativeC2 T) K hK hT,
    compactGraphPair_finiteTensor_mem_coreGraph N T K hK hT, ?_⟩
  apply (compactGraphPair_distance_bound N f _ hf (finiteTensor_nativeC2 T)
    K hK hs hT hd.le hvalue hlap).trans_lt
  change C * (epsilon / (C + 1)) < epsilon
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ hCp).mpr
  nlinarith

/-- Constructive pointwise seed approximation with ONE common compact H
carrier. The full Euclidean mollifier/quadrature theorem supplies all
finite tensors; its six jets are paid into the actual height-weighted
Maass error. No approximation conclusion occurs among the hypotheses. -/
theorem exists_common_compact_finite_seed_errors
    (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    ∃ (K : Set UpperHalfPlane) (hK : IsCompact K)
      (hs : Function.support f ⊆ K),
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ (n : ℕ) (T : Fin n → SmoothCompactTensor)
          (hT : Function.support (finiteCoreFunction Finset.univ
            (fun i => (T i).toCompactTensor)) ⊆ K),
          (∀ z ∈ K, ‖f z - finiteCoreFunction Finset.univ
            (fun i => (T i).toCompactTensor) z‖ ≤ epsilon) ∧
          (∀ z ∈ K, ‖upperMaass f z - upperMaass (finiteCoreFunction Finset.univ
            (fun i => (T i).toCompactTensor)) z‖ ≤ epsilon) := by
  obtain ⟨A, a, b, hA, ha, hab, happrox⟩ :=
    CompactC2FiniteTensorApproximation20261026a.exists_upper_seed_compactC2TensorApproximation
      f hfc hf
  let K := liftedBox (A+1) (a/2) (b+1)
  have hK : IsCompact K := liftedBox_isCompact _ _ _ (half_pos ha)
  obtain ⟨P0⟩ := happrox 1 (by norm_num)
  have hs : Function.support f ⊆ K :=
    seed_support_liftedBox f (A+1) (a/2) (b+1) P0.source_support
  refine ⟨K, hK, hs, ?_⟩
  intro epsilon he
  let L := jetLoss (b+1)
  have hL : 0 < L := jetLoss_pos _
  have hLp : 0 < L+1 := by positivity
  let delta := epsilon/(L+1)
  have hd : 0 < delta := div_pos he hLp
  obtain ⟨P⟩ := happrox delta hd
  obtain ⟨n, T, hchart⟩ := finset_tensor_enumeration P.indices P.tensors
  let g := finiteCoreFunction Finset.univ (fun i => (T i).toCompactTensor)
  have hext : extendUpper g = finiteChartFunction P.indices
      (fun i => (P.tensors i).toCompactTensor) := by
    change extendUpper (finiteCoreFunction Finset.univ (fun i => (T i).toCompactTensor)) = _
    rw [extendUpper_finiteCoreFunction, hchart]
  have hT : Function.support g ⊆ K := by
    apply seed_support_liftedBox g (A+1) (a/2) (b+1)
    rw [hext]
    exact P.common_support
  have hjets : ∀ p ∈ planeBox (A+1) (a/2) (b+1), ∀ ij : JetIndex,
      ‖partialJet ij (extendUpper f) p - partialJet ij (extendUpper g) p‖ ≤ delta := by
    intro p hp ij
    rw [hext]
    simpa only [norm_sub_rev] using (P.uniform_sixJet_error ⟨p, hp⟩ ij).le
  have herrors := value_maass_errors_on_liftedBox f g (A+1) (a/2) (b+1) hd.le hjets
  have hsmall : L * delta < epsilon := by
    dsimp only [delta]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hLp).mpr
    nlinarith
  refine ⟨n, T, hT, ?_, ?_⟩
  · intro z hz
    exact (herrors.1 z hz).trans hsmall.le
  · intro z hz
    exact (herrors.2 z hz).trans hsmall.le

/-- An actual compact smooth periodized seed belongs to the MINIMAL
closed graph. This conclusion uses the constructive finite-tensor theorem,
not a core-membership, domain, density or graph-limit premise. -/
theorem compact_smooth_seed_graph_mem_closed
    (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    ∃ (K : Set UpperHalfPlane) (hK : IsCompact K)
      (hs : Function.support f ⊆ K),
      compactGraphPair N f (hf.of_le (by simp)) K hK hs ∈ closedGammaGraph N := by
  obtain ⟨K, hK, hs, happrox⟩ := exists_common_compact_finite_seed_errors f hfc hf
  exact ⟨K, hK, hs, closed_graph_of_finite_seed_errors N f
    (hf.of_le (by simp)) K hK hs happrox⟩

/-- Representation-invariant endpoint, allowing consumers to use their
canonical quotient L2 definitions for both original coordinates. -/
theorem compact_smooth_seed_ae_pair_mem_closedGraph
    (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart)
    (u v : Lp ℂ 2 (carrierPushforward N))
    (hu : (u : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N] complexPoincare N f)
    (hv : (v : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N (upperMaass f)) : (u,v) ∈ closedGammaGraph N := by
  obtain ⟨K, hK, hs, hclosed⟩ := compact_smooth_seed_graph_mem_closed N f hfc hf
  have hueq : u = compactInput N f (hf.of_le (by simp)) K hK hs :=
    Lp.ext (hu.trans (compactInput_ae N f _ K hK hs).symm)
  have hveq : v = compactOutput N f (hf.of_le (by simp)) K hK hs :=
    Lp.ext (hv.trans (compactOutput_ae N f _ K hK hs).symm)
  simpa only [hueq, hveq, compactGraphPair] using hclosed

/-- The SAME pair is in the native actual minimal closed partial-operator
graph. This is stronger than merely belonging to an arbitrary extension. -/
theorem compact_smooth_seed_ae_pair_mem_minimalGraph
    (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart)
    (u v : Lp ℂ 2 (carrierPushforward N))
    (hu : (u : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N] complexPoincare N f)
    (hv : (v : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N (upperMaass f)) :
    (u,v) ∈ (actualClosedGammaMaass N).graph := by
  rw [actualClosedGammaMaass_graph_eq]
  exact compact_smooth_seed_ae_pair_mem_closedGraph N f hfc hf u v hu hv
/-- A genuine sequence of finite SmoothSeed generators converges in the
product of the original quotient input/output L2 spaces. Thus both the
function and its ACTUAL Maass output converge, with a common compact seed
carrier independent of the sequence index. -/
theorem exists_finite_tensor_graph_sequence
    (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    ∃ (K : Set UpperHalfPlane) (hK : IsCompact K)
      (hs : Function.support f ⊆ K) (dims : ℕ → ℕ)
      (T : ∀ k : ℕ, Fin (dims k) → SmoothCompactTensor)
      (hT : ∀ k, Function.support (finiteCoreFunction Finset.univ
        (fun i => (T k i).toCompactTensor)) ⊆ K),
      (∀ k, compactGraphPair N _ (finiteTensor_nativeC2 (T k)) K hK (hT k) ∈ coreGraph N) ∧
      Tendsto (fun k => compactGraphPair N _ (finiteTensor_nativeC2 (T k)) K hK (hT k))
        atTop (𝓝 (compactGraphPair N f (hf.of_le (by simp)) K hK hs)) := by
  obtain ⟨K, hK, hs, happrox⟩ := exists_common_compact_finite_seed_errors f hfc hf
  let C := transportConstant N K
  have hC : 0 ≤ C := transportConstant_nonneg N K
  have hCp : 0 < C+1 := by positivity
  let rate : ℕ → ℝ := fun k => 1/((k:ℝ)+1)
  have hrpos : ∀ k, 0 < rate k := by intro k; dsimp [rate]; positivity
  let delta : ℕ → ℝ := fun k => rate k/(C+1)
  have hdpos : ∀ k, 0 < delta k := fun k => div_pos (hrpos k) hCp
  choose dims T hT hvalue hlap using fun k => happrox (delta k) (hdpos k)
  refine ⟨K, hK, hs, dims, T, hT,
    fun k => compactGraphPair_finiteTensor_mem_coreGraph N (T k) K hK (hT k), ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hbound : ∀ k, dist (compactGraphPair N _ (finiteTensor_nativeC2 (T k)) K hK (hT k))
      (compactGraphPair N f (hf.of_le (by simp)) K hK hs) ≤ rate k := by
    intro k
    rw [dist_comm]
    apply (compactGraphPair_distance_bound N f _ (hf.of_le (by simp))
      (finiteTensor_nativeC2 (T k)) K hK hs (hT k)
      (hdpos k).le (hvalue k) (hlap k)).trans
    change C * (rate k/(C+1)) ≤ rate k
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hCp).mpr
    nlinarith [hrpos k]
  exact squeeze_zero (fun k => dist_nonneg) hbound
    (show Tendsto rate atTop (𝓝 0) from tendsto_one_div_add_atTop_nhds_zero_nat)
end
end ImbalancedChen.Part3.GammaFiniteTensorGraphCore20261026a
