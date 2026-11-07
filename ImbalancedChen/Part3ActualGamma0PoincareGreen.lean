import ImbalancedChen.Part3Gamma0OneCompactChartGreen
import ImbalancedChen.Part3Gamma0PoincarePairingUnfolding
import ImbalancedChen.Part3ActualTensorPoincareMaassJoin

/-!
# Green symmetry for the ACTUAL Gamma0 quotient Poincare graph

SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED / CODE_ONLY.

The genuine C2 compact input seed has a C0 compact Laplacian seed. A new
generic C0 compact-seed pair-unfolding handles that output without giving
it nonexistent fourth derivatives. Actual local-finite Mobius commutation
identifies its Poincare trace with the genuine geometric upperMaass.
The genuine one-compact two-dimensional H Green theorem then gives the
cross pairing identity for the actual quotient input and output L2 vectors.

No hGreen, hCommutation, hL2 or whole-plane graph transport is assumed.
Positivity and the first-gradient quotient energy are separate work.
-/

namespace ImbalancedChen.Part3.ActualGamma0PoincareGreen20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane Pointwise
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorQuotientL2Core20261025a
open ImbalancedChen.Part3.Gamma0ComplexL1PoincareUnfolding20261025a
open ImbalancedChen.Part3.Gamma0CompactLaplacianSeed20261025a
open ImbalancedChen.Part3.Gamma0CompactSeedQuotientL2Budget20261025a
open ImbalancedChen.Part3.ActualTensorPoincareMaassJoin20261025a
open ImbalancedChen.Part3.Gamma0OneCompactChartGreen20261025a

/-- This trace factorization uses actual effective-group invariance of
the C0 compact seed trace, not a C2 license for a Laplacian output. -/
theorem compact_pair_trace (N : ℕ) (f g : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    complexSeedTrace N (fun w => star (f w) * complexSeedTrace N g w) z =
      star (complexSeedTrace N f z) * complexSeedTrace N g z := by
  unfold complexSeedTrace translatedSeed
  calc
    _ = ∑' q : effectiveGamma0 N,
        star (f (effectiveMatrixAction N q z)) * complexSeedTrace N g z := by
      apply tsum_congr
      intro q
      have hinv := compactSeedTrace_gamma0_invariant N g (effectiveRepresentative N q) z
      change complexSeedTrace N g (effectiveMatrixAction N q z) = complexSeedTrace N g z at hinv
      rw [hinv]
    _ = _ := by
      rw [tsum_mul_right, ← tsum_star]
      rfl

/-- True quotient pair-unfolding for arbitrary C0 compact seeds. In
particular either seed can be the actual second-order Maass image. -/
theorem compact_C0_pair_unfolding (N : ℕ) [NeZero N]
    (f g : UpperHalfPlane → ℂ) (hf : Continuous f) (hg : Continuous g)
    {K L : Set UpperHalfPlane} (hK : IsCompact K) (hL : IsCompact L)
    (hfs : Function.support f ⊆ K) (hgs : Function.support g ⊆ L) :
    (∫ q, star (complexPoincare N f q) * complexPoincare N g q ∂carrierPushforward N) =
      ∫ z : UpperHalfPlane, star (f z) * complexSeedTrace N g z := by
  have htrace : Continuous (complexSeedTrace N g) := compactSeedTrace_continuous N g hg hL hgs
  have hcompact : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact hK hfs
  have hcompactStar : HasCompactSupport (fun z => star (f z)) :=
    hcompact.comp_left (g := star) (by simp)
  have hprod : Integrable (fun z => star (f z) * complexSeedTrace N g z)
      (volume : Measure UpperHalfPlane) :=
    (hf.star.mul htrace).integrable_of_hasCompactSupport hcompactStar.mul_right
  have hquot : Integrable (fun q => star (complexPoincare N f q) * complexPoincare N g q)
      (carrierPushforward N) := by
    exact MemLp.integrable_mul (p := 2) (q := 2)
      (compactPoincare_memLp_two N f hf hK hfs).star
      (compactPoincare_memLp_two N g hg hL hgs)
  calc
    _ = ∫ z : reducedCarrier N, star (complexSeedTrace N f z) * complexSeedTrace N g z
        ∂reducedCarrierMeasure N := by
      rw [← reducedProjection_map_measure N,
        (reducedProjection_measurableEmbedding N).integral_map]
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by rw [complexPoincare_projection, complexPoincare_projection])
    _ = ∫ z in reducedCarrier N, star (complexSeedTrace N f z) * complexSeedTrace N g z :=
      integral_subtype_comap (reducedCarrier_measurable N) _
    _ = ∫ z in reducedCarrier N,
        complexSeedTrace N (fun w => star (f w) * complexSeedTrace N g w) z := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => (compact_pair_trace N f g z).symm)
    _ = _ := complex_carrier_unfolding N _ hprod

/-- The invariant orbit-lift input equals the actual section-defined
complex seed Poincare function a.e. for the SAME actual quotient measure. -/
theorem quotientTensorPoincare_ae_eq_complex (N : ℕ) [NeZero N] {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    quotientTensorPoincare N s T =ᵐ[carrierPushforward N] complexPoincare N (finiteCoreFunction s T) := by
  rw [← reducedProjection_map_measure N,
    (reducedProjection_measurableEmbedding N).ae_map_iff]
  apply Eventually.of_forall
  intro z
  rw [complexPoincare_projection]
  rfl

/-- Actual quotient Green identity for every pair of finite compact C2
input seeds. The actual C0 Laplacian outputs retain their true regularity. -/
theorem actual_quotient_poincare_green (N : ℕ) [NeZero N] {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor) :
    (∫ q, star (quotientTensorPoincare N s T q) * quotientTensorLaplacianPoincare N t U q
      ∂carrierPushforward N) =
      ∫ q, star (quotientTensorLaplacianPoincare N s T q) * quotientTensorPoincare N t U q
        ∂carrierPushforward N := by
  have hinputS := quotientTensorPoincare_ae_eq_complex N s T
  have hinputT := quotientTensorPoincare_ae_eq_complex N t U
  calc
    _ = ∫ q, star (complexPoincare N (finiteCoreFunction s T) q) *
        complexPoincare N (finiteCoreLaplacian t U) q ∂carrierPushforward N := by
      apply integral_congr_ae
      filter_upwards [hinputS] with q hq
      rw [hq]
      rfl
    _ = ∫ z : UpperHalfPlane, star (finiteCoreFunction s T z) *
        complexSeedTrace N (finiteCoreLaplacian t U) z :=
      compact_C0_pair_unfolding N _ _ (continuous_finiteCoreFunction s T)
        (finiteCoreLaplacian_continuous t U)
        (finiteCompactTensorSupportK_isCompact s T) (finiteCompactTensorSupportK_isCompact t U)
        (finiteCoreFunction_support_subset s T) (finiteCoreLaplacian_support_subset t U)
    _ = ∫ z : UpperHalfPlane, star (finiteCoreFunction s T z) *
        upperMaass (finiteCompactTensorPoincare N t U) z := by
      rw [upperMaass_finiteCompactTensorPoincare_eq_trace]
    _ = ∫ z : UpperHalfPlane, star (finiteCoreLaplacian s T z) *
        finiteCompactTensorPoincare N t U z :=
      upperMaass_one_compact_finite_seed_green s T (finiteCompactTensorPoincare N t U)
        (finiteCompactTensorPoincare_contDiffOn_chart N t U)
    _ = ∫ q, star (complexPoincare N (finiteCoreLaplacian s T) q) *
        complexPoincare N (finiteCoreFunction t U) q ∂carrierPushforward N :=
      (compact_C0_pair_unfolding N _ _ (finiteCoreLaplacian_continuous s T)
        (continuous_finiteCoreFunction t U)
        (finiteCompactTensorSupportK_isCompact s T) (finiteCompactTensorSupportK_isCompact t U)
        (finiteCoreLaplacian_support_subset s T) (finiteCoreFunction_support_subset t U)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hinputT] with q hq
      rw [hq]
      rfl

theorem quotient_input_output_inner_eq_integral (N : ℕ) [NeZero N] {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor) :
    inner ℂ (quotientTensorPoincareL2 N s T) (quotientTensorLaplacianPoincareL2 N t U) =
      ∫ q, star (quotientTensorPoincare N s T q) * quotientTensorLaplacianPoincare N t U q
        ∂carrierPushforward N := by
  rw [L2.inner_def]
  apply integral_congr_ae
  have hs := (quotientTensorPoincare_memLp_two N s T).coeFn_toLp
  have ht := (quotientTensorLaplacianPoincare_memLp_two N t U).coeFn_toLp
  filter_upwards [hs, ht] with q hqS hqT
  rw [hqS, hqT]
  simp only [RCLike.inner_apply', Complex.star_def]

theorem quotient_output_input_inner_eq_integral (N : ℕ) [NeZero N] {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor) :
    inner ℂ (quotientTensorLaplacianPoincareL2 N s T) (quotientTensorPoincareL2 N t U) =
      ∫ q, star (quotientTensorLaplacianPoincare N s T q) * quotientTensorPoincare N t U q
        ∂carrierPushforward N := by
  rw [L2.inner_def]
  apply integral_congr_ae
  have hs := (quotientTensorLaplacianPoincare_memLp_two N s T).coeFn_toLp
  have ht := (quotientTensorPoincare_memLp_two N t U).coeFn_toLp
  filter_upwards [hs, ht] with q hqS hqT
  rw [hqS, hqT]
  simp only [RCLike.inner_apply', Complex.star_def]

/-- Symmetry belongs to the ACTUAL quotient Poincare L2 input/output
family and its genuine geometric Laplacian, with no supplied Green field. -/
theorem actual_quotient_poincare_L2_symmetric (N : ℕ) [NeZero N] {ι κ : Type*}
    (s : Finset ι) (T : ι → CompactTensor) (t : Finset κ) (U : κ → CompactTensor) :
    inner ℂ (quotientTensorLaplacianPoincareL2 N s T) (quotientTensorPoincareL2 N t U) =
      inner ℂ (quotientTensorPoincareL2 N s T) (quotientTensorLaplacianPoincareL2 N t U) := by
  rw [quotient_output_input_inner_eq_integral, quotient_input_output_inner_eq_integral]
  exact (actual_quotient_poincare_green N s T t U).symm

end
end ImbalancedChen.Part3.ActualGamma0PoincareGreen20261025a
