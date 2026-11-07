import ImbalancedChen.Part3CompactH1SupportedEnergyApproximation
import ImbalancedChen.Part3GammaActualCompactWeakSeedH1
import ImbalancedChen.Part3GammaSmoothMultiplierLegalTests

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The ORIGINAL actual cutoff-square defect product has a constructed energy
approximation with one fixed compact SOURCE container. The container also
hits every effective orbit on which the original cutoff is nonzero: the
normalized scalar seed is retained in K even where the defect vanishes.
This permits a genuine outer plateau to be chosen AFTER the approximation
container, with no source-support or cutoff-nesting premise.
-/
namespace ImbalancedChen.Part3.ActualCutoffSquareSupportedEnergy20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open MaassWeakOperatorCore20261024zz ActualGamma0MaassDescent20261025a
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualSmoothQuotientMaassGraph20261025a
open Gamma0ActualMinimalShiftRange20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0CompactTensorPoincareLocalFinite20261025a
open WeakH1ProductMollifierDerivative20261026a
open LocalH1NormalizedTensorSequence20261026b LocalH1TensorDifferenceABI20261026b
open CompactH1CanonicalSeedL220261026b CompactH1SupportedEnergyApproximation20261026b
open GammaActualCutoffWeakSeedReconstruction20261026b GammaActualCompactWeakSeedH120261026b
open Gamma0WholeChartCoordinateWeakEquation20261026b
open GammaSmoothMultiplierPeriodization20261026a GammaSmoothMultiplierLegalTests20261026a
open ActualModularCutoffSmoothSeed20261025a ActualModularCutoffMaassBudget20261025a
open ActualModularSmoothCuspCutoff20261025a ActualModularSmoothCutoffL2Tail20261025a

theorem actual_cutoff_square_supported_energy_approximation (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : f ∈ minimalShiftDefect N) (Y : ℝ) (hY : 1 ≤ Y) :
    ∃ (L R a b : ℝ) (J : CompactH1Jet) (P : NormalizedH1TensorSequence J L R a b)
      (K : Set UpperHalfPlane) (e : EnergyCompletion N),
      0 < a ∧ L < R ∧ a < b ∧ IsCompact K ∧
      (∀ k, finiteCompactTensorSupportK Finset.univ (seedTensors (P.seed k)) ⊆ K) ∧
      (∀ k, Function.support (finiteCoreFunction Finset.univ (seedTensors (P.seed k))) ⊆ K ∧
        Function.support (finiteCoreLaplacian Finset.univ (seedTensors (P.seed k))) ⊆ K) ∧
      Tendsto (fun k => coreEmbedding N (familyEnergyCore N (P.tensors k))) atTop (𝓝 e) ∧
      (((physicalProjection N e : QuotientL2 N) : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
        fun q => (quotientCutoff N Y q : ℂ)^2 * f q) ∧
      (∀ z : UpperHalfPlane, globalCutoff Y z ≠ 0 →
        ∃ q : effectiveGamma0 N, effectiveMatrixAction N q z ∈ K) := by
  classical
  obtain ⟨σ,hσc,hσs,hσtrace⟩ := exists_compact_cinfty_seed_reconstructing_globalCutoff N Y hY
  let χ := complexGlobalH Y
  let τ : UpperHalfPlane → ℂ := χ * σ
  have hτc : HasCompactSupport τ := multiplier_seed_hasCompactSupport χ σ hσc
  have hχs := actualCutoff_cinfty Y (lt_of_lt_of_le (by norm_num) hY)
  have hτs : ContDiffOn ℝ ∞ (extendUpper τ) positiveChart :=
    compact_multiplier_seed_smooth χ σ hχs hσs
  have hχinv : IsGammaInvariant N χ := actualCutoff_isGammaInvariant N Y
  have hτtrace : ∀ z, complexSeedTrace N (compactCoefficientSeed N τ f) z =
      (globalCutoff Y z : ℂ)^2 * f (orbitProjection N z) := by
    intro z
    rw [compactCoefficientSeed_trace]
    rw [show complexSeedTrace N τ z = χ z * complexSeedTrace N σ z from
      congrFun (complexSeedTrace_mul_invariant N χ σ hχinv) z,hσtrace z]
    simp only [χ,complexGlobalH,pow_two]
  obtain ⟨L,R,a,b,J,ha,hLR,hab,hval,hx,hy,hsv,hsx,hsy⟩ :=
    actual_defect_compact_coefficient_H1 N f hf τ hτc hτs
  obtain ⟨K₀,P,e,hK₀,hK₀eq,hPs,hSources,he,hraw⟩ :=
    compactH1_supported_energy_approximation N J hx hy L R a b ha hLR hab hsv
  let K : Set UpperHalfPlane := K₀ ∪ tsupport σ
  have hK : IsCompact K := hK₀.union hσc
  have hK₀K : K₀ ⊆ K := subset_union_left
  have hupper : upperSeed J.value = compactCoefficientSeed N τ f := by
    funext z
    rw [hval]
    exact extendUpper_pair (compactCoefficientSeed N τ f) z
  have hphysical : ((physicalProjection N e : QuotientL2 N) : Gamma0OrbitSpace N → ℂ)
      =ᵐ[carrierPushforward N] fun q => (quotientCutoff N Y q : ℂ)^2 * f q := by
    rw [hupper] at hraw
    filter_upwards [hraw,reducedProjection_range_ae N] with q hq hsection
    obtain ⟨z,rfl⟩ := hsection
    rw [hq,complexPoincare_projection,hτtrace z]
    rfl
  refine ⟨L,R,a,b,J,P,K,e,ha,hLR,hab,hK,fun k => (hPs k).trans hK₀K,
    fun k => ⟨(hSources k).1.trans hK₀K,(hSources k).2.trans hK₀K⟩,he,hphysical,?_⟩
  intro z hz
  have hex : ∃ q : effectiveGamma0 N, σ (effectiveMatrixAction N q z) ≠ 0 := by
    by_contra hn
    have hzero : ∀ q : effectiveGamma0 N, σ (effectiveMatrixAction N q z) = 0 := by
      intro q
      by_contra hq
      exact hn ⟨q,hq⟩
    have htracezero : complexSeedTrace N σ z = 0 := by
      simp only [complexSeedTrace,translatedSeed,hzero,tsum_zero]
    have hczero : (globalCutoff Y z : ℂ) = 0 := (hσtrace z).symm.trans htracezero
    exact hz (Complex.ofReal_eq_zero.mp hczero)
  obtain ⟨q,hq⟩ := hex
  exact ⟨q,Or.inr (subset_closure hq)⟩

end
end ImbalancedChen.Part3.ActualCutoffSquareSupportedEnergy20261026b

