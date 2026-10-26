import ImbalancedChen.Part3SmoothZeroHeightSeedProfiles
import ImbalancedChen.Part3Gamma0ActualMinimalFriedrichsInclusion
import ImbalancedChen.Part3Gamma0SmoothCoreFinitePoincareRepresentation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Every genuine smooth compact positive-height incomplete Eisenstein seed
at infinity belongs to the ACTUAL original finite smooth tensor core.
Its native Friedrichs graph output is the actual zero seed with profile
-y^2 psi''. The horizontal partition, its two derivative cancellations,
the true effective/parabolic reindex and original core graph inclusion
supply the proof; no graph-action or operator-domain premise is used.

Consequently the native output of an infinity-cusp annihilator vector
annihilates every smooth compact zero-height test. Extending this last
test class to all HeightSeed tests requires separate actual density and
is not asserted as full cusp invariance or completeness here.
-/
namespace ImbalancedChen.Part3.GammaSmoothZeroSeedNativeGraph20261026b

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open Gamma0QuotientCellPushforward20261025a
open Gamma0CarrierAESection20261025a Gamma0CarrierMeasurableInverse20261025a
open Gamma0QuotientConullTransport20261025a
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0ParabolicCosetRows20261025a Gamma0ParabolicEffectiveDecomposition20261025a
open GammaInfinityTranslationStrip20261025a Gamma0ActualParabolicUnfolding20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a
open ActualInfinityKloostermanSeed20261025a CompactCuspParabolicL220261025a
open ActualInfinityCuspAnnihilator20261026b
open MaassWeakOperatorCore20261024zz
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0CompactTensorQuotientL2Core20261025a Gamma0CompactLaplacianSeed20261025a
open Gamma0CompactSeedQuotientL2Budget20261025a Gamma0SmoothCompactTensorCore20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0SmoothCoreFinitePoincareRepresentation20261025a
open Gamma0ActualWeakRieszResolvent20261025a Gamma0ActualFriedrichsOperator20261025a
open Gamma0ActualMinimalFriedrichsInclusion20261025a
open SmoothZeroHeightSeedProfiles20261026b

/-- Actual compact effective summability licenses the complex double
sum before the literal integer trace is replaced by the periodic seed. -/
theorem compact_trace_eq_parabolic_of_integer_trace (N : ℕ) (f F : UpperHalfPlane → ℂ)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hs : Function.support f ⊆ K)
    (htrace : ∀ z : UpperHalfPlane, (∑' k : ℤ, f (translate k z)) = F z)
    (z : UpperHalfPlane) : complexSeedTrace N f z = parabolicTraceComplex N F z := by
  have hsum := compact_seed_summable N f hK hs z
  have hprod := (parabolicEffectiveEquiv N).summable_iff.mpr hsum
  have hprod' : Summable (fun p : GammaInfinityCosets N × ℤ =>
      f (translate p.2 (parabolicRepresentative N p.1 • z))) := by
    apply hprod.congr
    rintro ⟨q, k⟩
    exact congrArg f (parabolicPair_action N q k z)
  change (∑' e : effectiveGamma0 N, f (effectiveMatrixAction N e z)) = _
  calc
    _ = ∑' p : GammaInfinityCosets N × ℤ,
        f (effectiveMatrixAction N (parabolicEffectiveEquiv N p) z) :=
      ((parabolicEffectiveEquiv N).tsum_eq _).symm
    _ = ∑' p : GammaInfinityCosets N × ℤ,
        f (translate p.2 (parabolicRepresentative N p.1 • z)) := by
      apply tsum_congr
      rintro ⟨q, k⟩
      exact congrArg f (parabolicPair_action N q k z)
    _ = ∑' q : GammaInfinityCosets N, ∑' k : ℤ,
        f (translate k (parabolicRepresentative N q • z)) := hprod'.tsum_prod
    _ = _ := by simp_rw [htrace]; rfl

def smoothProfileSeed (s : SmoothHeightSeed) : SmoothSeed := ⟨1, fun _ => profileTensor s⟩

private theorem smoothProfile_input_seed (s : SmoothHeightSeed) :
    finiteCoreFunction Finset.univ (seedTensors (smoothProfileSeed s)) = profileTensorSeed s := by
  funext z
  simp [finiteCoreFunction, seedTensors, smoothProfileSeed, profileTensorSeed, profileTensor]

private theorem smoothProfile_output_seed (s : SmoothHeightSeed) :
    finiteCoreLaplacian Finset.univ (seedTensors (smoothProfileSeed s)) =
      profileTensorLaplacianSeed s := by
  funext z
  simp [finiteCoreLaplacian, seedTensors, smoothProfileSeed, profileTensorLaplacianSeed, profileTensor]

theorem smoothProfile_input_trace (N : ℕ) (s : SmoothHeightSeed) (z : UpperHalfPlane) :
    finiteCompactTensorPoincare N Finset.univ (seedTensors (smoothProfileSeed s)) z =
      parabolicTraceComplex N (fourierRadialSeed 0 s.toFun) z := by
  apply compact_trace_eq_parabolic_of_integer_trace N _ _
    (finiteCompactTensorSupportK Finset.univ (seedTensors (smoothProfileSeed s)))
    (finiteCompactTensorSupportK_isCompact _ _) (finiteCoreFunction_support_subset _ _)
  intro w
  rw [smoothProfile_input_seed]
  simpa [fourierRadialSeed] using profileTensorSeed_integer_sum s w

theorem smoothProfile_output_trace (N : ℕ) (s : SmoothHeightSeed) (z : UpperHalfPlane) :
    complexSeedTrace N (finiteCoreLaplacian Finset.univ (seedTensors (smoothProfileSeed s))) z =
      parabolicTraceComplex N (fourierRadialSeed 0 s.maass.toFun) z := by
  apply compact_trace_eq_parabolic_of_integer_trace N _ _
    (finiteCompactTensorSupportK Finset.univ (seedTensors (smoothProfileSeed s)))
    (finiteCompactTensorSupportK_isCompact _ _) (finiteCoreLaplacian_support_subset _ _)
  intro w
  rw [smoothProfile_output_seed]
  simpa [fourierRadialSeed] using profileTensorLaplacianSeed_integer_sum s w

/-- Equality in the original actual quotient L2, using the genuine
conull reduced section for the original parabolic definition. -/
theorem smoothProfile_seedVector_eq_zeroSeed (N : ℕ) [NeZero N] (s : SmoothHeightSeed) :
    seedVector N (smoothProfileSeed s) = zeroSeedL2 N s.toHeightSeed := by
  apply Lp.ext
  filter_upwards [(quotientTensorPoincare_memLp_two N Finset.univ
    (seedTensors (smoothProfileSeed s))).coeFn_toLp,
    (compactCuspPoincare_memLp_two N 0 s.toFun s.continuous s.compact s.positive).coeFn_toLp,
    reducedProjection_range_ae N] with q hinput hzero hsection
  obtain ⟨z, rfl⟩ := hsection
  change quotientTensorPoincareL2 N Finset.univ (seedTensors (smoothProfileSeed s))
      (reducedProjection N z) = compactCuspPoincareL2 N 0 s.toFun s.continuous s.compact s.positive
      (reducedProjection N z)
  rw [hinput, hzero, quotientTensorPoincare_projection, parabolicComplexPoincare_projection]
  exact smoothProfile_input_trace N s z

theorem smoothProfile_seedOutput_eq_zeroSeed_maass (N : ℕ) [NeZero N] (s : SmoothHeightSeed) :
    seedOutput N (smoothProfileSeed s) = zeroSeedL2 N s.maass.toHeightSeed := by
  apply Lp.ext
  filter_upwards [(quotientTensorLaplacianPoincare_memLp_two N Finset.univ
    (seedTensors (smoothProfileSeed s))).coeFn_toLp,
    (compactCuspPoincare_memLp_two N 0 s.maass.toFun s.maass.continuous
      s.maass.compact s.maass.positive).coeFn_toLp,
    reducedProjection_range_ae N] with q houtput hzero hsection
  obtain ⟨z, rfl⟩ := hsection
  change quotientTensorLaplacianPoincareL2 N Finset.univ (seedTensors (smoothProfileSeed s))
      (reducedProjection N z) = compactCuspPoincareL2 N 0 s.maass.toFun s.maass.continuous
        s.maass.compact s.maass.positive (reducedProjection N z)
  rw [houtput, hzero, quotientTensorLaplacianPoincare_projection,
    parabolicComplexPoincare_projection]
  exact smoothProfile_output_trace N s z

/-- Actual original algebraic smooth-core graph membership, stronger
than merely membership in a proposed closed extension. -/
theorem smooth_zeroSeed_pair_mem_actual_coreGraph (N : ℕ) [NeZero N] (s : SmoothHeightSeed) :
    (zeroSeedL2 N s.toHeightSeed, zeroSeedL2 N s.maass.toHeightSeed) ∈ coreGraph N := by
  have h : seedPair N (smoothProfileSeed s) ∈ coreGraph N := Submodule.subset_span ⟨_, rfl⟩
  change (seedVector N (smoothProfileSeed s), seedOutput N (smoothProfileSeed s)) ∈ coreGraph N at h
  simpa only [smoothProfile_seedVector_eq_zeroSeed, smoothProfile_seedOutput_eq_zeroSeed_maass] using h

/-- Native action of the ACTUAL Friedrichs operator on every smooth
compact physical zero seed, with output profile exactly -y^2 psi''. -/
theorem smooth_zeroSeed_pair_mem_actual_friedrichsGraph (N : ℕ) [NeZero N] (s : SmoothHeightSeed) :
    (zeroSeedL2 N s.toHeightSeed, zeroSeedL2 N s.maass.toHeightSeed) ∈
      (actualGammaFriedrichs N).graph :=
  actual_coreGraph_le_friedrichsGraph N (smooth_zeroSeed_pair_mem_actual_coreGraph N s)

/-- Genuine native symmetry derived from the physical resolvent graph,
with both domain/output pairs retained explicitly. -/
theorem actual_native_graph_cross_symmetry (N : ℕ) [NeZero N]
    {u v w z : QuotientL2 N} (huv : (u, v) ∈ (actualGammaFriedrichs N).graph)
    (hwz : (w, z) ∈ (actualGammaFriedrichs N).graph) : inner ℂ w v = inner ℂ z u := by
  have hi := (actualGammaResolvent_selfAdjoint N).isSymmetric (w + z) (u + v)
  rw [(actualGammaFriedrichs_mem_graph_iff N).mp hwz,
    (actualGammaFriedrichs_mem_graph_iff N).mp huv, inner_add_right, inner_add_left] at hi
  exact add_left_cancel hi

/-- A full infinity-cusp annihilator domain vector has native output
annihilating every SMOOTH compact zero-height test. No density extension
to all continuous HeightSeed tests is smuggled into this conclusion. -/
theorem native_cusp_output_annihilates_smooth_zeroSeeds (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain) (hu : (u : QuotientL2 N) ∈ infinityCuspSubspace N)
    (s : SmoothHeightSeed) :
    inner ℂ (zeroSeedL2 N s.toHeightSeed) (actualGammaFriedrichs N u) = 0 := by
  rw [actual_native_graph_cross_symmetry N ((actualGammaFriedrichs N).mem_graph u)
    (smooth_zeroSeed_pair_mem_actual_friedrichsGraph N s)]
  exact (mem_infinityCuspSubspace_iff N (u : QuotientL2 N)).mp hu s.maass.toHeightSeed

end
end ImbalancedChen.Part3.GammaSmoothZeroSeedNativeGraph20261026b
