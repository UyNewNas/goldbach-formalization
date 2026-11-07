import ImbalancedChen.Part3Gamma0CompactQuotientLocalLp
import ImbalancedChen.Part3CanonicalPlanarL2Unitary
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecificLimits.Basic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

An actual Gamma0 quotient L2 vector, with NO differential regularity
assumption, has an ordinary complex-coordinate compact L2 localization.
The existing canonical unitary divides by height. A bounded capped-height
multiplier undoes that division on the actual compact set. Consequently
the function being mollified is the original quotient pullback there,
not the weighted y^-1 pullback. Its explicit normalized bump convolutions
are smooth, have the genuine convolution derivative, and reconstruct the
localized original function almost everywhere for canonical hyperbolic
volume. Their support is controlled by the original compact set.

This is a mollifier foundation for local elliptic regularity, NOT a proof
of local H1 for an adjoint deficiency vector. In particular no derivative
bound uniform in the mollifier radius is claimed.
-/

namespace ImbalancedChen.Part3.Gamma0CompactDefectMollifier20261026a

noncomputable section
open Set Function Filter MeasureTheory ContinuousLinearMap
open scoped Topology Convolution ContDiff UpperHalfPlane Pointwise
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CompactQuotientLocalLp20261025a
open ImbalancedChen.Part3.CanonicalPlanarL2UnitarySourceOnly
open ImbalancedChen.Part3.UpperHalfPlaneHyperbolicMeasure20261024z

/-- This cutoff only localizes an existing quotient L2 function. It does
not purport to belong to a differential operator domain. -/
def compactPullback (N : ℕ) (K : Set UpperHalfPlane)
    (f : Lp ℂ 2 (carrierPushforward N)) : UpperHalfPlane → ℂ :=
  K.indicator (fun z => f (orbitProjection N z))

theorem compactPullback_memLp (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    (f : Lp ℂ 2 (carrierPushforward N)) :
    MemLp (compactPullback N K f) 2 (volume : Measure UpperHalfPlane) := by
  exact (memLp_indicator_iff_restrict hK.measurableSet).2
    (quotientLp_pullback_memLp N hK f)

def cappedHeight (B : ℝ) (p : ℝ × ℝ) : ℝ := min (max p.2 0) B

theorem cappedHeight_continuous (B : ℝ) : Continuous (cappedHeight B) :=
  (continuous_snd.max continuous_const).min continuous_const

theorem cappedHeight_nonneg {B : ℝ} (hB : 0 ≤ B) (p : ℝ × ℝ) :
    0 ≤ cappedHeight B p :=
  le_min (le_max_right _ _) hB

theorem cappedHeight_le (B : ℝ) (p : ℝ × ℝ) : cappedHeight B p ≤ B :=
  min_le_right _ _

/-- The bound is supplied by compactness, not by an analytic estimate on f. -/
theorem exists_compact_height_bound {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, z.im ≤ B := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image UpperHalfPlane.continuous_im.continuousOn
  exact ⟨max B 0, le_max_right _ _, fun z hz =>
    (hB (mem_image_of_mem _ hz)).trans (le_max_left _ _)⟩

/-- Bounded multiplication restores ordinary coordinate values after the
existing hyperbolic-to-planar y^-1 unitary. -/
def localizedPlane (N : ℕ) (K : Set UpperHalfPlane) (B : ℝ)
    (f : Lp ℂ 2 (carrierPushforward N)) (p : ℝ × ℝ) : ℂ :=
  cappedHeight B p • forwardFunction (compactPullback N K f) p

theorem localizedPlane_memLp (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B : ℝ} (hB : 0 ≤ B)
    (f : Lp ℂ 2 (carrierPushforward N)) :
    MemLp (localizedPlane N K B f) 2 (volume : Measure (ℝ × ℝ)) := by
  have hF := forwardFunction_memLp (compactPullback_memLp N hK f)
  apply (hF.const_smul B).of_le
    ((cappedHeight_continuous B).aestronglyMeasurable.smul hF.aestronglyMeasurable)
  exact Eventually.of_forall fun p => by
    simp only [localizedPlane, Pi.smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (cappedHeight_nonneg hB p), abs_of_nonneg hB]
    exact mul_le_mul_of_nonneg_right (cappedHeight_le B p) (norm_nonneg _)

theorem localizedPlane_at_upper (N : ℕ) {K : Set UpperHalfPlane} {B : ℝ}
    (hbound : ∀ z ∈ K, z.im ≤ B) (f : Lp ℂ 2 (carrierPushforward N))
    (z : UpperHalfPlane) :
    localizedPlane N K B f (chartMap z) = compactPullback N K f z := by
  unfold localizedPlane
  rw [forwardFunction_at_upper]
  by_cases hz : z ∈ K
  · have hc : cappedHeight B (chartMap z) = z.im := by
      change min (max z.im 0) B = z.im
      rw [max_eq_left z.im_pos.le, min_eq_left (hbound z hz)]
    rw [hc, smul_smul, mul_inv_cancel₀ (ne_of_gt z.im_pos), one_smul]
  · simp [compactPullback, hz]

/-- Ordinary complex coordinates have a smooth Euclidean norm, so the
native radial bump construction applies directly. -/
def localizedComplex (N : ℕ) (K : Set UpperHalfPlane) (B : ℝ)
    (f : Lp ℂ 2 (carrierPushforward N)) : ℂ → ℂ :=
  localizedPlane N K B f ∘ Complex.measurableEquivRealProd

theorem localizedComplex_memLp (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B : ℝ} (hB : 0 ≤ B)
    (f : Lp ℂ 2 (carrierPushforward N)) :
    MemLp (localizedComplex N K B f) 2 (volume : Measure ℂ) :=
  (localizedPlane_memLp N hK hB f).comp_measurePreserving
    Complex.volume_preserving_equiv_real_prod

theorem localizedComplex_at_upper (N : ℕ) {K : Set UpperHalfPlane} {B : ℝ}
    (hbound : ∀ z ∈ K, z.im ≤ B) (f : Lp ℂ 2 (carrierPushforward N))
    (z : UpperHalfPlane) :
    localizedComplex N K B f (z : ℂ) = compactPullback N K f z :=
  localizedPlane_at_upper N hbound f z

theorem localizedComplex_support (N : ℕ) {K : Set UpperHalfPlane} {B : ℝ}
    (hbound : ∀ z ∈ K, z.im ≤ B) (f : Lp ℂ 2 (carrierPushforward N)) :
    Function.support (localizedComplex N K B f) ⊆ UpperHalfPlane.coe '' K := by
  intro w hw
  by_cases hy : 0 < w.im
  · let z : UpperHalfPlane := ⟨w, hy⟩
    have hv : localizedComplex N K B f w = compactPullback N K f z :=
      localizedComplex_at_upper N hbound f z
    have hz : z ∈ K := by
      by_contra hz
      exact hw (by simpa [compactPullback, hz] using hv)
    exact ⟨z, hz, rfl⟩
  · have hp : Complex.measurableEquivRealProd w ∉
        ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z.upperChart := hy
    have hv := forwardFunction_zero_outside (compactPullback N K f)
      (Complex.measurableEquivRealProd w) hp
    exact False.elim (hw (by simp [localizedComplex, localizedPlane, hv]))

theorem localizedComplex_hasCompactSupport (N : ℕ) {K : Set UpperHalfPlane}
    (hK : IsCompact K) {B : ℝ} (hbound : ∀ z ∈ K, z.im ≤ B)
    (f : Lp ℂ 2 (carrierPushforward N)) :
    HasCompactSupport (localizedComplex N K B f) :=
  HasCompactSupport.of_support_subset_isCompact
    (hK.image UpperHalfPlane.continuous_coe) (localizedComplex_support N hbound f)

def mollifierRadius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem mollifierRadius_pos (n : ℕ) : 0 < mollifierRadius n := by
  unfold mollifierRadius
  positivity

def mollifierBump (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := mollifierRadius n / 2
  rOut := mollifierRadius n
  rIn_pos := half_pos (mollifierRadius_pos n)
  rIn_lt_rOut := half_lt_self (mollifierRadius_pos n)

def mollifierKernel (n : ℕ) : ℂ → ℝ := (mollifierBump n).normed volume

def scalarAction : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := lsmul ℝ ℝ

def mollify (n : ℕ) (g : ℂ → ℂ) : ℂ → ℂ :=
  mollifierKernel n ⋆[scalarAction, volume] g

theorem mollify_contDiff {g : ℂ → ℂ} (hg : LocallyIntegrable g volume) (n : ℕ) :
    ContDiff ℝ ∞ (mollify n g) :=
  (mollifierBump n).hasCompactSupport_normed.contDiff_convolution_left
    scalarAction (mollifierBump n).contDiff_normed hg

theorem mollify_hasFDerivAt {g : ℂ → ℂ} (hg : LocallyIntegrable g volume)
    (n : ℕ) (w : ℂ) :
    HasFDerivAt (mollify n g)
      ((fderiv ℝ (mollifierKernel n) ⋆[scalarAction.precompL ℂ, volume] g) w) w :=
  (mollifierBump n).hasCompactSupport_normed.hasFDerivAt_convolution_left
    scalarAction (mollifierBump n).contDiff_normed hg w

theorem ae_mollify_tendsto {g : ℂ → ℂ} (hg : LocallyIntegrable g volume) :
    ∀ᵐ w ∂(volume : Measure ℂ),
      Tendsto (fun n : ℕ => mollify n g w) atTop (𝓝 (g w)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := mollifierBump) (K := 2) ?_ ?_ hg
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · exact Eventually.of_forall fun n => by
      change mollifierRadius n ≤ 2 * (mollifierRadius n / 2)
      linarith

/-- Canonical hyperbolic a.e. conclusions may be pulled back from ordinary
complex Lebesgue a.e. conclusions. This uses actual null-set transport. -/
theorem upperCoe_quasiMeasurePreserving :
    QuasiMeasurePreserving UpperHalfPlane.coe (volume : Measure UpperHalfPlane)
      (volume : Measure ℂ) := by
  have h : QuasiMeasurePreserving UpperHalfPlane.coe coordinateMeasure
      (volume : Measure ℂ) := by
    refine ⟨UpperHalfPlane.measurableEmbedding_coe.measurable, ?_⟩
    rw [coordinateMeasure, UpperHalfPlane.measurableEmbedding_coe.map_comap]
    exact Measure.restrict_le_self.absolutelyContinuous
  exact h.mono_left hyperbolicMeasure_absolutelyContinuous_coordinate

/-- Applies in particular to actual minimal-adjoint deficiency vectors:
NO H1, C2 or weak-gradient hypothesis is needed. -/
theorem actual_compact_mollification (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, z.im ≤ B) (f : Lp ℂ 2 (carrierPushforward N)) :
    (∀ n : ℕ, ContDiff ℝ ∞ (mollify n (localizedComplex N K B f))) ∧
    (∀ᵐ z ∂(volume : Measure UpperHalfPlane),
      Tendsto (fun n : ℕ => mollify n (localizedComplex N K B f) (z : ℂ))
        atTop (𝓝 (compactPullback N K f z))) := by
  have hg := (localizedComplex_memLp N hK hB f).locallyIntegrable (by norm_num)
  refine ⟨fun n => mollify_contDiff hg n, ?_⟩
  filter_upwards [upperCoe_quasiMeasurePreserving.ae (ae_mollify_tendsto hg)] with z hz
  simpa only [localizedComplex_at_upper N hbound f z] using hz

theorem actual_compact_mollification_on_original (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ z ∈ K, z.im ≤ B) (f : Lp ℂ 2 (carrierPushforward N)) :
    ∀ᵐ z ∂((volume : Measure UpperHalfPlane).restrict K),
      Tendsto (fun n : ℕ => mollify n (localizedComplex N K B f) (z : ℂ))
        atTop (𝓝 (f (orbitProjection N z))) := by
  apply (ae_restrict_iff' hK.measurableSet).2
  filter_upwards [(actual_compact_mollification N hK hB hbound f).2] with z hz hzK
  simpa only [compactPullback, indicator_of_mem hzK] using hz

/-- The smoothing has an explicit compact neighborhood support budget. -/
theorem actual_mollifier_support (N : ℕ) {K : Set UpperHalfPlane} {B : ℝ}
    (hbound : ∀ z ∈ K, z.im ≤ B) (f : Lp ℂ 2 (carrierPushforward N)) (n : ℕ) :
    Function.support (mollify n (localizedComplex N K B f)) ⊆
      Metric.ball (0 : ℂ) (mollifierRadius n) + UpperHalfPlane.coe '' K := by
  exact (support_convolution_subset scalarAction).trans
    (add_subset_add (mollifierBump n).support_normed_eq.subset
      (localizedComplex_support N hbound f))

end
end ImbalancedChen.Part3.Gamma0CompactDefectMollifier20261026a
