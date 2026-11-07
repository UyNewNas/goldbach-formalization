import ImbalancedChen.Part3Gamma0NormalizedSeedSmoothness
import ImbalancedChen.Part3Gamma0CompactCarrierBump
import ImbalancedChen.Part3ActualModularCutoffTSupportCover

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

A genuinely constructed compact C-infinity H seed reconstructs the actual
global modular cutoff by the actual effective-Gamma0 Poincare sum. The
bump is produced from the true compact carrier, the full tsupport orbit
cover is supplied by genuine quotient topology, and smooth normalization
is proved through zero-denominator neighborhoods. No bump, trace-smoothness,
normalized-smoothness, or reconstruction conclusion is assumed.

Finite smooth-tensor-span approximation and the resulting actual core,
energy-completion or graph-domain membership remain separate obligations.
-/

namespace ImbalancedChen.Part3.ActualModularCutoffSmoothSeed20261025a

noncomputable section
open Set
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0CompactTensorPoincareC2Core20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open Gamma0NormalizedCompactSeed20261025a Gamma0NormalizedSeedSmoothness20261025a
open Gamma0CompactCarrierBump20261025a ActualModularSmoothCuspCutoff20261025a
open ActualModularCutoffCompactSupport20261025a ActualModularCutoffTSupportCover20261025a

theorem complex_cutoff_tsupport (Y : ℝ) :
    tsupport (fun z : UpperHalfPlane => (globalCutoff Y z : ℂ)) = tsupport (globalCutoff Y) := by
  unfold tsupport
  congr 1
  ext z
  simp only [Function.mem_support, Complex.ofReal_eq_zero]

/-- All actual suppliers are composed: no bump or normalized smoothness
premise remains. The equality is pointwise on the original H action. -/
theorem exists_compact_cinfty_seed_reconstructing_globalCutoff
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y) :
    ∃ f : UpperHalfPlane → ℂ,
      HasCompactSupport f ∧
      ContDiffOn ℝ ∞ (extendUpper f) positiveChart ∧
      ∀ z, complexSeedTrace N f z = (globalCutoff Y z : ℂ) := by
  let C := truncatedGammaCarrier N (2 * Y)
  have hC : IsCompact C := truncatedGammaCarrier_isCompact N (2 * Y)
  obtain ⟨b, K, hK, hbK, _hbc, hbsmooth, hbnonneg, hbC⟩ := exists_smooth_compact_bump_one hC
  let F : UpperHalfPlane → ℂ := fun z => (globalCutoff Y z : ℂ)
  have hYpos : 0 < Y := lt_of_lt_of_le (by norm_num) hY
  have hF : ContDiffOn ℝ ∞ (fun p => F (chartLift p)) positiveChart :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (globalCutoff_chart_cinfty Y hYpos)
  have hcover : ∀ z ∈ tsupport F,
      ∃ q : effectiveGamma0 N, effectiveMatrixAction N q z ∈ C := by
    intro z hz
    have hreal : z ∈ tsupport (globalCutoff Y) := by
      rw [← complex_cutoff_tsupport Y]
      exact hz
    exact globalCutoff_tsupport_compact_effective_cover N Y hY z hreal
  have hbpos : ∀ z ∈ C, 0 < b z := by
    intro z hz
    rw [hbC z hz]
    norm_num
  have hFs : ∀ g : CongruenceSubgroup.Gamma0 N, ∀ z, F (g • z) = F z := by
    intro g z
    exact congrArg (fun a : ℝ => (a : ℂ))
      (globalCutoff_sl2_invariant Y (g : SL(2, ℤ)) z)
  refine ⟨normalizedSeed N b F, normalizedSeed_hasCompactSupport N b F hK hbK,
    normalizedSeed_extendUpper_cinfty_of_orbit_cover N b F hK hbK hbnonneg hbpos
      hbsmooth hF hcover, ?_⟩
  intro z
  exact normalizedSeed_trace_eq N b F hK hbK hbnonneg hbpos hFs
    (fun w hw => hcover w (subset_tsupport F hw)) z

/-- Explicit C2 compact seed endpoint for a genuine finite-jet/tensor
approximation theorem; no finite-tensor membership is inferred here. -/
theorem exists_compact_C2_seed_reconstructing_globalCutoff
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y) :
    ∃ f : UpperHalfPlane → ℂ,
      HasCompactSupport f ∧
      ContDiffOn ℝ 2 (extendUpper f) positiveChart ∧
      ∀ z, complexSeedTrace N f z = (globalCutoff Y z : ℂ) := by
  obtain ⟨f, hf, hs, hr⟩ := exists_compact_cinfty_seed_reconstructing_globalCutoff N Y hY
  exact ⟨f, hf, hs.of_le (by simp), hr⟩

end
end ImbalancedChen.Part3.ActualModularCutoffSmoothSeed20261025a
