import ImbalancedChen.Part3Gamma0ActualMinimalAdjointDefect
import ImbalancedChen.Part3Gamma0CompactQuotientLocalLp
import ImbalancedChen.Part3Gamma0ReducedSeedReconstruction
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

The native adjoint of the actual minimal Gamma0 quotient Maass operator
satisfies a local weak differential identity against genuine finite smooth
compact tensor seeds. The CLOSED support container of both the test and
its actual Laplacian must lie inside the original open reduced carrier.
This geometric hypothesis controls derivative support without silently
discarding boundary terms. Product L1 comes from genuine compact local L2,
not a false global upper-half-plane L2 assertion. Negative-one deficiency
vectors satisfy the corresponding test weak equation. No elliptic
regularity, deficiency vanishing or essential self-adjointness is claimed.
-/

namespace ImbalancedChen.Part3.Gamma0ActualAdjointInteriorWeakEquation20261025a

noncomputable section
open Set Filter Function MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorQuotientL2Core20261025a
open ImbalancedChen.Part3.Gamma0ComplexL1PoincareUnfolding20261025a
open ImbalancedChen.Part3.Gamma0CompactLaplacianSeed20261025a
open ImbalancedChen.Part3.Gamma0CompactSeedQuotientL2Budget20261025a
open ImbalancedChen.Part3.Gamma0ReducedSeedReconstruction20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientCore20261025a
open ImbalancedChen.Part3.Gamma0ActualSmoothQuotientMaassGraph20261025a
open ImbalancedChen.Part3.Gamma0ActualMaassClosedOperator20261025a
open ImbalancedChen.Part3.Gamma0ActualMinimalShiftRange20261025a
open ImbalancedChen.Part3.Gamma0ActualMinimalAdjointDefect20261025a
open ImbalancedChen.Part3.Gamma0CompactQuotientLocalLp20261025a

/-- Genuine global L1 of the COMPACT test product. The quotient vector
itself is only pulled back locally on K. -/
theorem compact_seed_quotient_product_integrable (N : ℕ) [NeZero N]
    (a : UpperHalfPlane → ℂ) (ha : Continuous a)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hasupp : Function.support a ⊆ K)
    (f : QuotientL2 N) :
    Integrable (fun z => star (a z)*f (orbitProjection N z))
      (volume : Measure UpperHalfPlane) := by
  have hac : HasCompactSupport a := HasCompactSupport.of_support_subset_isCompact hK hasupp
  have halp : MemLp a 2 (volume : Measure UpperHalfPlane) := ha.memLp_of_hasCompactSupport hac
  have hprod : Integrable (fun z => star (a z)*f (orbitProjection N z))
      ((volume : Measure UpperHalfPlane).restrict K) :=
    MemLp.integrable_mul (p := 2) (q := 2) (halp.restrict K).star
      (quotientLp_pullback_memLp N hK f)
  apply (integrableOn_iff_integrable_of_support_subset (s := K) ?_).mp hprod
  intro z hz
  by_contra hzK
  have haz : a z = 0 := notMem_support.mp (fun h => hzK (hasupp h))
  exact hz (by simp [haz])

/-- Pairing localization for ANY actual quotient L2 representative
whose pointwise orbit pullback reconstructs the compact seed on S. -/
theorem reconstructed_quotient_inner_eq_compact_pair (N : ℕ) [NeZero N]
    (a : UpperHalfPlane → ℂ) (hsupp : Function.support a ⊆ reducedCarrier N)
    (A : Gamma0OrbitSpace N → ℂ) (hA : MemLp A 2 (carrierPushforward N))
    (hrec : ∀ z : reducedCarrier N, A (reducedProjection N z) = a z)
    (f : QuotientL2 N) :
    inner ℂ (hA.toLp A) f = ∫ z : UpperHalfPlane, star (a z)*f (orbitProjection N z) := by
  calc
    _ = ∫ q, star (A q)*f q ∂carrierPushforward N := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hA.coeFn_toLp] with q hq
      rw [hq]
      simp only [RCLike.inner_apply', Complex.star_def]
    _ = ∫ z : reducedCarrier N, star (a z)*f (reducedProjection N z)
        ∂reducedCarrierMeasure N := by
      rw [← reducedProjection_map_measure N,
        (reducedProjection_measurableEmbedding N).integral_map]
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by rw [hrec z])
    _ = ∫ z in reducedCarrier N, star (a z)*f (orbitProjection N z) :=
      integral_subtype_comap (reducedCarrier_measurable N) _
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      have haz : a z = 0 := notMem_support.mp (fun h => hz (hsupp h))
      simp [haz]

/-- Output reconstruction only needs the original C0 compact Laplacian
seed and its support; no fictitious fourth derivative is used. -/
theorem laplacianPoincare_reconstructs_on_reduced (N : ℕ) [NeZero N]
    {ι : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (hK : finiteCompactTensorSupportK s T ⊆ reducedCarrier N)
    (z : reducedCarrier N) :
    quotientTensorLaplacianPoincare N s T (reducedProjection N z) =
      finiteCoreLaplacian s T z := by
  rw [quotientTensorLaplacianPoincare_projection,tsum_eq_single (1 : effectiveGamma0 N)]
  · rw [effectiveMatrixAction_one]
  · intro q hq
    exact translated_seed_zero_of_ne_one N (finiteCoreLaplacian s T)
      ((finiteCoreLaplacian_support_subset s T).trans hK) z.property q hq

theorem interior_seed_input_pair (N : ℕ) [NeZero N] (s : SmoothSeed)
    (hK : finiteCompactTensorSupportK Finset.univ (seedTensors s) ⊆ reducedCarrier N)
    (f : QuotientL2 N) :
    inner ℂ (seedVector N s) f =
      ∫ z : UpperHalfPlane, star (finiteCoreFunction Finset.univ (seedTensors s) z)*
        f (orbitProjection N z) := by
  exact reconstructed_quotient_inner_eq_compact_pair N _
    ((finiteCoreFunction_support_subset Finset.univ (seedTensors s)).trans hK)
    _ (quotientTensorPoincare_memLp_two N Finset.univ (seedTensors s))
    (quotientTensorPoincare_reducedProjection N Finset.univ (seedTensors s)
      ((finiteCoreFunction_support_subset Finset.univ (seedTensors s)).trans hK)) f

theorem interior_seed_output_pair (N : ℕ) [NeZero N] (s : SmoothSeed)
    (hK : finiteCompactTensorSupportK Finset.univ (seedTensors s) ⊆ reducedCarrier N)
    (f : QuotientL2 N) :
    inner ℂ (seedOutput N s) f =
      ∫ z : UpperHalfPlane, star (finiteCoreLaplacian Finset.univ (seedTensors s) z)*
        f (orbitProjection N z) :=
  reconstructed_quotient_inner_eq_compact_pair N _
    ((finiteCoreLaplacian_support_subset Finset.univ (seedTensors s)).trans hK)
    _ (quotientTensorLaplacianPoincare_memLp_two N Finset.univ (seedTensors s))
    (laplacianPoincare_reconstructs_on_reduced N Finset.univ (seedTensors s) hK) f

theorem seedPair_mem_actualClosed_graph (N : ℕ) [NeZero N] (s : SmoothSeed) :
    (seedVector N s,seedOutput N s) ∈ (actualClosedGammaMaass N).graph := by
  rw [actualClosedGammaMaass_graph_eq]
  exact subset_closure (Submodule.subset_span ⟨s,rfl⟩)

theorem finite_tensor_weak_products_integrable (N : ℕ) [NeZero N]
    (s : SmoothSeed) (f w : QuotientL2 N) :
    Integrable (fun z => star (finiteCoreLaplacian Finset.univ (seedTensors s) z)*
      f (orbitProjection N z)) (volume : Measure UpperHalfPlane) ∧
    Integrable (fun z => star (finiteCoreFunction Finset.univ (seedTensors s) z)*
      w (orbitProjection N z)) (volume : Measure UpperHalfPlane) := by
  constructor
  · exact compact_seed_quotient_product_integrable N _
      (finiteCoreLaplacian_continuous Finset.univ (seedTensors s))
      (finiteCompactTensorSupportK_isCompact Finset.univ (seedTensors s))
      (finiteCoreLaplacian_support_subset Finset.univ (seedTensors s)) f
  · exact compact_seed_quotient_product_integrable N _
      (continuous_finiteCoreFunction Finset.univ (seedTensors s))
      (finiteCompactTensorSupportK_isCompact Finset.univ (seedTensors s))
      (finiteCoreFunction_support_subset Finset.univ (seedTensors s)) w

/-- Native adjoint membership, tested on an actual compact seed pair,
gives the genuine local differential equation for every interior test. -/
theorem actual_adjoint_graph_interior_weak (N : ℕ) [NeZero N]
    {f w : QuotientL2 N} (hfw : (f,w) ∈ (actualClosedGammaMaass N).adjoint.graph)
    (s : SmoothSeed)
    (hK : finiteCompactTensorSupportK Finset.univ (seedTensors s) ⊆ reducedCarrier N) :
    (∫ z : UpperHalfPlane, star (finiteCoreLaplacian Finset.univ (seedTensors s) z)*
      f (orbitProjection N z)) =
    ∫ z : UpperHalfPlane, star (finiteCoreFunction Finset.univ (seedTensors s) z)*
      w (orbitProjection N z) := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint
    (actualClosedGammaMaass_dense_domain N)] at hfw
  have h := (Submodule.mem_adjoint_iff _ _).mp hfw
    (seedVector N s) (seedOutput N s) (seedPair_mem_actualClosed_graph N s)
  have heq := sub_eq_zero.mp h
  rw [interior_seed_output_pair N s hK,interior_seed_input_pair N s hK] at heq
  exact heq

theorem actual_adjoint_domain_interior_weak (N : ℕ) [NeZero N]
    (f : (actualClosedGammaMaass N).adjoint.domain) (s : SmoothSeed)
    (hK : finiteCompactTensorSupportK Finset.univ (seedTensors s) ⊆ reducedCarrier N) :
    (∫ z : UpperHalfPlane, star (finiteCoreLaplacian Finset.univ (seedTensors s) z)*
      (f : QuotientL2 N) (orbitProjection N z)) =
    ∫ z : UpperHalfPlane, star (finiteCoreFunction Finset.univ (seedTensors s) z)*
      ((actualClosedGammaMaass N).adjoint f) (orbitProjection N z) :=
  actual_adjoint_graph_interior_weak N (LinearPMap.mem_graph _ f) s hK

/-- Deficiency vectors satisfy (Delta+1)f=0 AGAINST these actual interior
tests. This is a weak test statement, not elliptic regularity or f=0. -/
theorem actual_negative_one_defect_interior_weak (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N) (s : SmoothSeed)
    (hK : finiteCompactTensorSupportK Finset.univ (seedTensors s) ⊆ reducedCarrier N) :
    (∫ z : UpperHalfPlane,
      star (finiteCoreLaplacian Finset.univ (seedTensors s) z+
        finiteCoreFunction Finset.univ (seedTensors s) z)*f (orbitProjection N z)) = 0 := by
  have hfw := (mem_minimalShiftDefect_iff_adjoint_graph N f).mp hf
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint
    (actualClosedGammaMaass_dense_domain N)] at hfw
  have h := (Submodule.mem_adjoint_iff _ _).mp hfw
    (seedVector N s) (seedOutput N s) (seedPair_mem_actualClosed_graph N s)
  have hzero : inner ℂ (seedOutput N s) f+inner ℂ (seedVector N s) f=0 := by
    simpa only [inner_neg_right,sub_neg_eq_add] using h
  have hi := compact_seed_quotient_product_integrable N _
    (continuous_finiteCoreFunction Finset.univ (seedTensors s))
    (finiteCompactTensorSupportK_isCompact Finset.univ (seedTensors s))
    (finiteCoreFunction_support_subset Finset.univ (seedTensors s)) f
  have ho := compact_seed_quotient_product_integrable N _
    (finiteCoreLaplacian_continuous Finset.univ (seedTensors s))
    (finiteCompactTensorSupportK_isCompact Finset.univ (seedTensors s))
    (finiteCoreLaplacian_support_subset Finset.univ (seedTensors s)) f
  simp_rw [star_add,add_mul]
  rw [integral_add ho hi,← interior_seed_output_pair N s hK,
    ← interior_seed_input_pair N s hK]
  exact hzero

end
end ImbalancedChen.Part3.Gamma0ActualAdjointInteriorWeakEquation20261025a
