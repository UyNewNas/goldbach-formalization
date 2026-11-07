import ImbalancedChen.Part3ActualPoincareGradientEnergyBudget
import ImbalancedChen.Part3ActualGamma0PoincareEnergy
import ImbalancedChen.Part3Gamma0CompactCoreGradient

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Quantitative H1 transfer for finite compact seeds. The actual quotient
Dirichlet energy is bounded by the genuine effective compact-overlap
number times the original seed gradient energy. Positivity and the
integral of the full translated energy trace are proved before integration
of the existing pointwise Cauchy estimate. A common compact container
makes the constant uniform for subsequent H1 approximants.
-/

namespace ImbalancedChen.Part3.GammaCompactSeedDirichletBudget20261026b
noncomputable section
open Set Function Filter MeasureTheory
open scoped UpperHalfPlane ContDiff
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open Gamma0CarrierMeasurableInverse20261025a Gamma0QuotientConullTransport20261025a
open Gamma0CompactTensorPoincareLocalFinite20261025a Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0CompactTensorQuotientL2Core20261025a Gamma0CompactSeedQuotientL2Budget20261025a
open MaassWeakOperatorCore20261024zz Gamma0CompactGreenProductL120261025a
open Gamma0ComplexL1PoincareUnfolding20261025a Gamma0CompactGlobalOverlap20261025a
open ActualPoincareGradientEnergyBudget20261025a ActualGamma0PoincareEnergy20261025a
open ActualMobiusDirichletCovariance20261025a

theorem compactOverlapBound_mono (N : ℕ) {K L : Set UpperHalfPlane}
    (hL : IsCompact L) (hKL : K ⊆ L) : compactOverlapBound N K ≤ compactOverlapBound N L := by
  have hs : compactTransporter N K ⊆ compactTransporter N L := by
    intro q hq
    obtain ⟨z, ⟨w, hw, rfl⟩, hz⟩ := hq
    exact ⟨effectiveMatrixAction N q w, ⟨w, hKL hw, rfl⟩, hKL hz⟩
  exact Nat.add_le_add_right (Set.ncard_le_ncard hs (finite_effective_compact_hits N hL hL)) 1

def seedDirichletDensity {ι : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (z : UpperHalfPlane) : ℝ := chartEnergy (extendUpper (finiteCoreFunction s T)) (z.re,z.im)

theorem seedDirichletDensity_nonneg {ι : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (z : UpperHalfPlane) : 0 ≤ seedDirichletDensity s T z := chartEnergy_nonneg _ _

theorem seedDirichletDensity_continuous {ι : Type*} (s : Finset ι) (T : ι → CompactTensor) :
    Continuous (seedDirichletDensity s T) := by
  have hF : ContDiffOn ℝ 1 (extendUpper (finiteCoreFunction s T)) positiveChart := by
    rw [extendUpper_finiteCoreFunction]
    apply ContDiff.contDiffOn
    apply ContDiff.sum
    intro i _
    exact (((T i).horizontal_smooth.comp contDiff_fst).mul
      ((T i).vertical_smooth.comp contDiff_snd)).of_le (by norm_num)
  have hcoord : Continuous (fun z : UpperHalfPlane => (z.re,z.im)) :=
    UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im
  have hx : Continuous (fun z : UpperHalfPlane =>
      sliceDx (extendUpper (finiteCoreFunction s T)) (z.re,z.im)) :=
    (sliceDx_continuousOn_of_C1 _ hF).comp_continuous hcoord (fun z => z.im_pos)
  have hy : Continuous (fun z : UpperHalfPlane =>
      sliceDy (extendUpper (finiteCoreFunction s T)) (z.re,z.im)) :=
    (sliceDy_continuousOn_of_C1 _ hF).comp_continuous hcoord (fun z => z.im_pos)
  exact (UpperHalfPlane.continuous_im.pow 2).mul ((hx.norm.pow 2).add (hy.norm.pow 2))

theorem seedDirichletDensity_support {ι : Type*} (s : Finset ι) (T : ι → CompactTensor) :
    Function.support (seedDirichletDensity s T) ⊆ finiteCompactTensorSupportK s T := by
  intro z hz
  by_contra hout
  have hg := translated_seed_zero_germ_of_outside_compact 1 s T
    (1 : effectiveGamma0 1) z.im_pos (by simpa only [chartLift_pair, effectiveMatrixAction_one] using hout)
  have hx : sliceDx (translatedFiniteTensorChart 1 1 s T) (z.re,z.im) = 0 := by
    simpa only [sliceDx, deriv_const] using sliceDx_eq_of_eventuallyEq hg
  have hy : sliceDy (translatedFiniteTensorChart 1 1 s T) (z.re,z.im) = 0 := by
    simpa only [sliceDy, deriv_const] using sliceDy_eq_of_eventuallyEq hg
  have hcov := translated_chartEnergy_eq_actual 1 s T (1 : effectiveGamma0 1) z.im_pos
  simp only [chartLift_pair, effectiveMatrixAction_one] at hcov
  apply hz
  change chartEnergy (extendUpper (finiteCoreFunction s T)) (z.re,z.im) = 0
  rw [← hcov, chartEnergy, hx, hy]
  simp

theorem seedDirichletDensity_integrable {ι : Type*} (s : Finset ι) (T : ι → CompactTensor) :
    Integrable (seedDirichletDensity s T) :=
  (seedDirichletDensity_continuous s T).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact
      (finiteCompactTensorSupportK_isCompact s T) (seedDirichletDensity_support s T))

theorem seed_energy_trace_re (N : ℕ) {ι : Type*} (s : Finset ι) (T : ι → CompactTensor)
    (z : UpperHalfPlane) :
    (complexSeedTrace N (fun w => (seedDirichletDensity s T w : ℂ)) z).re =
      ∑' q : effectiveGamma0 N, seedDirichletDensity s T (effectiveMatrixAction N q z) := by
  simp only [complexSeedTrace, translatedSeed, ← Complex.ofReal_tsum, Complex.ofReal_re]

/-- True trace integrability and exact whole-H mass, before applying
any energy inequality. No summability/integral exchange is a premise. -/
theorem seed_energy_trace_integral (N : ℕ) [NeZero N] {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) :
    IntegrableOn (fun z => ∑' q : effectiveGamma0 N,
      seedDirichletDensity s T (effectiveMatrixAction N q z)) (reducedCarrier N) ∧
    (∫ z in reducedCarrier N, ∑' q : effectiveGamma0 N,
      seedDirichletDensity s T (effectiveMatrixAction N q z)) =
        ∫ z : UpperHalfPlane, seedDirichletDensity s T z := by
  have hi : Integrable (fun z : UpperHalfPlane => (seedDirichletDensity s T z : ℂ)) :=
    Complex.ofRealCLM.integrable_comp (seedDirichletDensity_integrable s T)
  have ht := complexSeedTrace_integrable N _ hi
  have h := congrArg Complex.re (complex_carrier_unfolding N _ hi)
  rw [← integral_re ht, ← integral_re hi] at h
  simpa only [seed_energy_trace_re, Complex.ofReal_re] using ⟨ht.re, h⟩

/-- The actual quotient finite-seed energy receives the SAME compact
overlap constant for every seed contained in a prescribed compact K. -/
theorem quotient_seed_Dirichlet_le (N : ℕ) [NeZero N] {ι : Type*}
    (s : Finset ι) (T : ι → CompactTensor) {K : Set UpperHalfPlane}
    (hK : IsCompact K) (hsK : finiteCompactTensorSupportK s T ⊆ K) :
    (inner ℂ (quotientTensorPoincareL2 N s T)
      (quotientTensorLaplacianPoincareL2 N s T)).re ≤
        (compactOverlapBound N K : ℝ) * ∫ z : UpperHalfPlane, seedDirichletDensity s T z := by
  have hqi := (quotientPoincareEnergy_integrable N s T s T).re
  have hsub : Integrable (fun z : reducedCarrier N =>
      (quotientPoincareEnergy N s T s T (reducedProjection N z)).re)
      (reducedCarrierMeasure N) :=
    (reducedProjection_measurePreserving N).integrable_comp_of_integrable hqi
  obtain ⟨htrace, htraceeq⟩ := seed_energy_trace_integral N s T
  have hE : IntegrableOn (fun z : UpperHalfPlane =>
      chartEnergy (extendUpper (finiteCompactTensorPoincare N s T)) (z.re,z.im))
      (reducedCarrier N) := by
    apply (integrableOn_iff_comap_subtypeVal (reducedCarrier_measurable N)).mpr
    convert hsub using 1
    funext z
    rw [show reducedProjection N z = orbitProjection N z from rfl,
      quotientPoincareEnergy_projection, poincareEnergyH, chartEnergy_eq_re_hyperbolicDirichlet]
  have hbound := integral_mono hE (htrace.const_mul (compactOverlapBound N K : ℝ))
    (fun z => (actualPoincare_pointwise_seed_energy_budget N s T z).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast compactOverlapBound_mono N hK hsK)
        (tsum_nonneg (fun q => seedDirichletDensity_nonneg s T _))))
  rw [integral_const_mul, htraceeq] at hbound
  rw [actual_quotient_poincare_energy, ← integral_re (quotientPoincareEnergy_integrable N s T s T)]
  calc
    _ = ∫ z : reducedCarrier N,
        (quotientPoincareEnergy N s T s T (reducedProjection N z)).re
          ∂reducedCarrierMeasure N := by
      rw [← reducedProjection_map_measure N,
        (reducedProjection_measurableEmbedding N).integral_map]
      rfl
    _ = ∫ z in reducedCarrier N,
        chartEnergy (extendUpper (finiteCompactTensorPoincare N s T)) (z.re,z.im) := by
      rw [← integral_subtype_comap (reducedCarrier_measurable N)]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        rw [show reducedProjection N z = orbitProjection N z from rfl,
          quotientPoincareEnergy_projection, poincareEnergyH, chartEnergy_eq_re_hyperbolicDirichlet]
    _ ≤ _ := hbound

end
end ImbalancedChen.Part3.GammaCompactSeedDirichletBudget20261026b
