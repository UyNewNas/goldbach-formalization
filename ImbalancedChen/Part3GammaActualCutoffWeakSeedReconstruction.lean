import ImbalancedChen.Part3GammaCompactWeakSeedL2Continuity
import ImbalancedChen.Part3Gamma0CompactSeedL2PairingUnfolding
import ImbalancedChen.Part3Gamma0CompactDefectMollifier
import ImbalancedChen.Part3ActualModularCutoffSmoothSeed
import ImbalancedChen.Part3ActualModularSmoothCutoffL2Tail

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
An actual quotient L2 vector multiplied by the original modular cutoff
is the genuine periodization of a compact nonsmooth seed. The compact
smooth coefficient is constructed by the original normalized cutoff-seed
theorem. Its product with the raw automorphic L2 representative is proved
L2 on H by compact local pullback L2 and a proved coefficient bound.
Full effective-group reconstruction is exact; no H1 or form membership
is assumed or claimed in this scalar physical identification step.
-/

namespace ImbalancedChen.Part3.GammaActualCutoffWeakSeedReconstruction20261026b
noncomputable section
open Set Function Filter MeasureTheory
open scoped UpperHalfPlane ContDiff
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open Gamma0CarrierMeasurableInverse20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0CompactDefectMollifier20261026a
open GammaCompactWeakSeedPoincareL220261026b Gamma0CompactSeedL2PairingUnfolding20261026b
open ActualModularCutoffSmoothSeed20261025a ActualModularSmoothCutoffL2Tail20261025a
open ActualCompactSeedMaassJoin20261025a Gamma0CompactTensorPoincareC2Core20261025a
open MaassWeakOperatorCore20261024zz

def compactCoefficientSeed (N : ℕ) [NeZero N] (σ : UpperHalfPlane → ℂ) (f : QuotientL2 N)
    (z : UpperHalfPlane) : ℂ := σ z * f (orbitProjection N z)

theorem compactCoefficientSeed_support (N : ℕ) [NeZero N] (σ : UpperHalfPlane → ℂ) (f : QuotientL2 N) :
    Function.support (compactCoefficientSeed N σ f) ⊆ Function.support σ := by
  intro z hz hzero
  exact hz (by simp [compactCoefficientSeed, hzero])

theorem compactCoefficientSeed_memLp (N : ℕ) [NeZero N]
    (σ : UpperHalfPlane → ℂ) (hσ : Continuous σ)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hs : Function.support σ ⊆ K)
    (f : QuotientL2 N) : MemLp (compactCoefficientSeed N σ f) 2 volume := by
  have hσc : HasCompactSupport σ := HasCompactSupport.of_support_subset_isCompact hK hs
  obtain ⟨C, hC⟩ := hσc.exists_bound_of_continuous hσ
  let D : ℝ := max C 0
  have hD : 0 ≤ D := le_max_right _ _
  have hσD : ∀ z, ‖σ z‖ ≤ D := fun z => (hC z).trans (le_max_left _ _)
  have hraw := compactPullback_memLp N hK f
  have heq : compactCoefficientSeed N σ f = fun z => σ z * compactPullback N K f z := by
    funext z
    by_cases hz : z ∈ K
    · simp [compactCoefficientSeed, compactPullback, hz]
    · have hzero : σ z = 0 := notMem_support.mp (fun h => hz (hs h))
      simp [compactCoefficientSeed, hzero]
  rw [heq]
  apply (hraw.const_smul D).of_le (hσ.aestronglyMeasurable.mul hraw.aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    simp only [Pi.smul_apply, norm_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hD]
    exact mul_le_mul_of_nonneg_right (hσD z) (norm_nonneg _)

theorem compactCoefficientSeed_trace (N : ℕ) [NeZero N] (σ : UpperHalfPlane → ℂ)
    (f : QuotientL2 N) (z : UpperHalfPlane) :
    complexSeedTrace N (compactCoefficientSeed N σ f) z =
      complexSeedTrace N σ z * f (orbitProjection N z) := by
  unfold complexSeedTrace translatedSeed compactCoefficientSeed
  calc
    _ = ∑' q : effectiveGamma0 N,
        σ (effectiveMatrixAction N q z) * f (orbitProjection N z) := by
      apply tsum_congr
      intro q
      rw [orbit_pullback_effective_invariant]
    _ = _ := tsum_mul_right

theorem coefficient_product_Poincare_ae (N : ℕ) [NeZero N]
    (σ : UpperHalfPlane → ℂ) (f : QuotientL2 N) :
    complexPoincare N (compactCoefficientSeed N σ f) =ᵐ[carrierPushforward N]
      fun q => complexPoincare N σ q * f q := by
  filter_upwards [reducedProjection_range_ae N] with q hq
  obtain ⟨z, rfl⟩ := hq
  rw [complexPoincare_projection, complexPoincare_projection, compactCoefficientSeed_trace]
  rfl

/-- Original actual modular cutoff times ANY quotient L2 vector has a
compact canonical-L2 raw seed with constructed smooth coefficient. This
is the physical reconstruction needed by H1 seed energy completion. -/
theorem actual_cutoff_product_has_compact_weak_seed (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) (f : QuotientL2 N) :
    ∃ (σ : UpperHalfPlane → ℂ) (hc : HasCompactSupport σ)
      (hsm : ContDiffOn ℝ ∞ (extendUpper σ) positiveChart)
      (hseed : MemLp (compactCoefficientSeed N σ f) 2 volume),
      (weakSeedL2 N (compactCoefficientSeed N σ f) hseed (tsupport σ) hc
        ((compactCoefficientSeed_support N σ f).trans subset_closure) : Gamma0OrbitSpace N → ℂ)
        =ᵐ[carrierPushforward N] fun q => (quotientCutoff N Y q : ℂ) * f q := by
  obtain ⟨σ, hc, hsm, htrace⟩ := exists_compact_cinfty_seed_reconstructing_globalCutoff N Y hY
  have hs : Function.support σ ⊆ tsupport σ := subset_closure
  have hseed := compactCoefficientSeed_memLp N σ
    (native_C2_continuous σ (hsm.of_le (by simp))) hc hs f
  refine ⟨σ, hc, hsm, hseed, ?_⟩
  apply (weakSeedL2_ae N (compactCoefficientSeed N σ f) hseed (tsupport σ) hc
    ((compactCoefficientSeed_support N σ f).trans subset_closure)).trans
  filter_upwards [reducedProjection_range_ae N] with q hq
  obtain ⟨z, rfl⟩ := hq
  rw [complexPoincare_projection, compactCoefficientSeed_trace, htrace z]
  rw [show reducedProjection N z = orbitProjection N z from rfl, quotientCutoff_projection]

end
end ImbalancedChen.Part3.GammaActualCutoffWeakSeedReconstruction20261026b
