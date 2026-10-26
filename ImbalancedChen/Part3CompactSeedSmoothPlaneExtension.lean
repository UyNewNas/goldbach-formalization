import ImbalancedChen.Part3Gamma0CompactUpperChartExtension
import ImbalancedChen.Part3ActualModularCutoffSmoothSeed

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

A compact H seed, smooth on its genuine positive chart, has a globally
smooth compact zero extension to the real plane. The existing canonical
support-image/compactness theorem is reused. A strictly positive uniform
height floor is PRODUCED from compactness of the original H topological
support. Below that floor the extension vanishes on a neighborhood, so
gluing is valid also at y=0. No global smoothness, planar compactness,
positive planar support, finite tensor core, or graph-domain membership
is supplied as a premise.
-/

namespace ImbalancedChen.Part3.CompactSeedSmoothPlaneExtension20261025a

noncomputable section
open Set Filter Topology
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0CompactGreenProductL120261025a Gamma0CompactUpperChartExtension20261025a
open Gamma0CompactCarrierBump20261025a ActualModularCutoffSmoothSeed20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a ActualModularSmoothCuspCutoff20261025a

/-- The original compact H support yields a STRICTLY positive uniform
height floor for the WHOLE planar topological support. -/
theorem exists_extendUpper_support_height_floor (f : UpperHalfPlane → ℂ)
    (hfc : HasCompactSupport f) :
    ∃ a : ℝ, 0 < a ∧ ∀ p ∈ tsupport (extendUpper f), a ≤ p.2 := by
  obtain ⟨A, a, B, _hA, ha, _haB, hrect⟩ := compact_height_rectangle hfc
  refine ⟨a, ha, ?_⟩
  intro p hp
  obtain ⟨z, hz, rfl⟩ := extendUpper_support_image f hfc hp
  exact (hrect z hz).2.1

/-- Every point below the derived support floor has a true zero germ,
including every point on the real axis and on the lower half-plane. -/
theorem extendUpper_zero_germ_below_floor (f : UpperHalfPlane → ℂ)
    (a : ℝ) (hfloor : ∀ p ∈ tsupport (extendUpper f), a ≤ p.2)
    (p : ℝ × ℝ) (hp : p.2 < a) :
    extendUpper f =ᶠ[𝓝 p] (fun _ => (0 : ℂ)) := by
  filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hp] with q hq
  apply image_eq_zero_of_notMem_tsupport
  intro hsupport
  exact (not_le_of_gt hq) (hfloor q hsupport)

/-- Global C-infinity extension, genuinely glued at the y=0 boundary.
Only compact H support and positive-chart regularity are inputs. -/
theorem extendUpper_cinfty (f : UpperHalfPlane → ℂ) (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    ContDiff ℝ ∞ (extendUpper f) := by
  obtain ⟨a, ha, hfloor⟩ := exists_extendUpper_support_height_floor f hfc
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : 0 < p.2
  · exact (hf p hp).contDiffAt (positiveChart_isOpen.mem_nhds hp)
  · have hbelow : p.2 < a := (le_of_not_gt hp).trans_lt ha
    have hc : ContDiffAt ℝ ∞ (fun _ : ℝ × ℝ => (0 : ℂ)) p := contDiffAt_const
    exact hc.congr_of_eventuallyEq (extendUpper_zero_germ_below_floor f a hfloor p hbelow)

theorem extendUpper_tsupport_positive (f : UpperHalfPlane → ℂ)
    (hfc : HasCompactSupport f) : tsupport (extendUpper f) ⊆ positiveChart := by
  obtain ⟨a, ha, hfloor⟩ := exists_extendUpper_support_height_floor f hfc
  intro p hp
  exact ha.trans_le (hfloor p hp)

/-- The full planar input required for actual compact convolution or
finite-jet approximation is produced together; no planar support/smoothness
supplier is assumed and no finite tensor membership is inferred. -/
theorem extendUpper_compact_cinfty_positive (f : UpperHalfPlane → ℂ)
    (hfc : HasCompactSupport f)
    (hf : ContDiffOn ℝ ∞ (extendUpper f) positiveChart) :
    ContDiff ℝ ∞ (extendUpper f) ∧ HasCompactSupport (extendUpper f) ∧
      tsupport (extendUpper f) ⊆ positiveChart :=
  ⟨extendUpper_cinfty f hfc hf, extendUpper_hasCompactSupport f hfc,
    extendUpper_tsupport_positive f hfc⟩

/-- Concrete end-to-end actual modular cutoff seed: the genuine compact
normalized seed now supplies globally smooth POSITIVE compact planar data,
while retaining its exact original effective-Gamma0 reconstruction. -/
theorem exists_globalCutoff_seed_with_smooth_plane_extension
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y) :
    ∃ f : UpperHalfPlane → ℂ,
      HasCompactSupport f ∧
      ContDiff ℝ ∞ (extendUpper f) ∧ HasCompactSupport (extendUpper f) ∧
      tsupport (extendUpper f) ⊆ positiveChart ∧
      ∀ z, complexSeedTrace N f z = (globalCutoff Y z : ℂ) := by
  obtain ⟨f, hfc, hfs, hfr⟩ := exists_compact_cinfty_seed_reconstructing_globalCutoff N Y hY
  obtain ⟨hs, hpc, hp⟩ := extendUpper_compact_cinfty_positive f hfc hfs
  exact ⟨f, hfc, hs, hpc, hp, hfr⟩

end
end ImbalancedChen.Part3.CompactSeedSmoothPlaneExtension20261025a
