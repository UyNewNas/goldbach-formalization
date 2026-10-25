import ImbalancedChen.Part3Gamma0NormalizedCompactSeed
import ImbalancedChen.Part3Gamma0SmoothTensorSpanRendering

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Every actual compact subset of H has a genuine nonnegative smooth separated
compact bump equal to one there. Coordinate bounds and a positive minimum
height are derived from compactness. Existing one-dimensional bump functions
supply the tensor; no bump-existence or normalizing-denominator premise is
introduced. Combined with the actual compact-seed normalization theorem this
constructs a compact seed reconstructing an invariant function with an actual
compact carrier cover. This is not finite-tensor core membership.
-/

namespace ImbalancedChen.Part3.Gamma0CompactCarrierBump20261025a

noncomputable section
open Set
open scoped UpperHalfPlane
open Gamma0NormalizedCompactSeed20261025a
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a
open PositiveRectangleSmoothTensorDensity20261025a
open Gamma0SmoothTensorSpanRendering20261025a

/-- Compactness inside H supplies an attained, strictly positive height floor. -/
theorem compact_height_rectangle {C : Set UpperHalfPlane} (hC : IsCompact C) :
    ∃ A a b : ℝ, 0 ≤ A ∧ 0 < a ∧ a ≤ b ∧
      ∀ z ∈ C, z.re ∈ Icc (-A) A ∧ z.im ∈ Icc a b := by
  rcases C.eq_empty_or_nonempty with hzero | hne
  · refine ⟨1, 1, 2, by norm_num, by norm_num, by norm_num, ?_⟩
    intro z hz
    simp [hzero] at hz
  · obtain ⟨z0, hz0, hmin⟩ := hC.exists_isMinOn hne UpperHalfPlane.continuous_im.continuousOn
    obtain ⟨A0, hA0⟩ := hC.bddAbove_image
      (continuous_abs.comp UpperHalfPlane.continuous_re).continuousOn
    obtain ⟨B0, hB0⟩ := hC.bddAbove_image UpperHalfPlane.continuous_im.continuousOn
    refine ⟨max 0 A0, z0.im, max z0.im B0, le_max_left _ _, z0.im_pos,
      le_max_left _ _, ?_⟩
    intro z hz
    have hx : |z.re| ≤ max 0 A0 := (hA0 ⟨z, hz, rfl⟩).trans (le_max_right _ _)
    exact ⟨abs_le.mp hx, hmin hz, (hB0 ⟨z, hz, rfl⟩).trans (le_max_right _ _)⟩

def rectangleBump (A a b : ℝ) (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b)
    (z : UpperHalfPlane) : ℝ :=
  horizontalBump A hA z.re * verticalBump a b ha hab z.im

theorem rectangleBump_nonneg (A a b : ℝ) (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b)
    (z : UpperHalfPlane) : 0 ≤ rectangleBump A a b hA ha hab z :=
  mul_nonneg (horizontalBump A hA).nonneg (verticalBump a b ha hab).nonneg

theorem rectangleBump_eq_one (A a b : ℝ) (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b)
    (z : UpperHalfPlane) (hz : z.re ∈ Icc (-A) A ∧ z.im ∈ Icc a b) :
    rectangleBump A a b hA ha hab z = 1 := by
  simp only [rectangleBump, horizontalBump_eq_one A hA hz.1,
    verticalBump_eq_one a b ha hab hz.2, one_mul]

theorem rectangleBump_continuous (A a b : ℝ) (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b) :
    Continuous (rectangleBump A a b hA ha hab) := by
  exact ((horizontalBump A hA).contDiff.continuous.comp UpperHalfPlane.continuous_re).mul
    ((verticalBump a b ha hab).contDiff.continuous.comp UpperHalfPlane.continuous_im)

/-- A compact H support container, constructed from the actual smooth tensor. -/
theorem rectangleBump_compact_container (A a b : ℝ)
    (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b) :
    ∃ K : Set UpperHalfPlane, IsCompact K ∧
      Function.support (rectangleBump A a b hA ha hab) ⊆ K := by
  let T := promotePositiveTensor (cutoffTensor A a b hA ha hab)
  refine ⟨compactTensorSupportK T.toCompactTensor, compactTensorSupportK_isCompact _, ?_⟩
  intro z hz
  have hprod : horizontalBump A hA z.re * verticalBump a b ha hab z.im ≠ 0 := hz
  have hx : ((horizontalBump A hA z.re : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero_iff.mp hprod).1
  have hy : ((verticalBump a b ha hab z.im : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero_iff.mp hprod).2
  exact ⟨subset_tsupport _ hx, subset_tsupport _ hy⟩

theorem rectangleBump_chart_cinfty (A a b : ℝ)
    (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b) :
    ContDiffOn ℝ ∞ (fun p => rectangleBump A a b hA ha hab (chartLift p)) positiveChart := by
  have hs : ContDiff ℝ ∞ (fun p : ℝ × ℝ =>
      horizontalBump A hA p.1 * verticalBump a b ha hab p.2) :=
    ((horizontalBump A hA).contDiff.comp contDiff_fst).mul
      ((verticalBump a b ha hab).contDiff.comp contDiff_snd)
  apply hs.contDiffOn.congr
  intro p hp
  rw [chartLift_of_positive hp]
  rfl

/-- Constructed smooth compact real bump, not an assumed cutoff supplier. -/
theorem exists_smooth_compact_bump_one {C : Set UpperHalfPlane} (hC : IsCompact C) :
    ∃ (b : UpperHalfPlane → ℝ) (K : Set UpperHalfPlane),
      IsCompact K ∧ Function.support b ⊆ K ∧ Continuous b ∧
      ContDiffOn ℝ ∞ (fun p => b (chartLift p)) positiveChart ∧
      (∀ z, 0 ≤ b z) ∧ ∀ z ∈ C, b z = 1 := by
  obtain ⟨A, a, B, hA, ha, haB, hrect⟩ := compact_height_rectangle hC
  obtain ⟨K, hK, hsupp⟩ := rectangleBump_compact_container A a B hA ha haB
  exact ⟨rectangleBump A a B hA ha haB, K, hK, hsupp,
    rectangleBump_continuous A a B hA ha haB,
    rectangleBump_chart_cinfty A a B hA ha haB,
    rectangleBump_nonneg A a B hA ha haB,
    fun z hz => rectangleBump_eq_one A a B hA ha haB z (hrect z hz)⟩

/-- Exact compact-seed reconstruction with the bump genuinely constructed.
The only cover input is the actual orbit meeting the given compact carrier. -/
theorem exists_compact_seed_reconstructing (N : ℕ) (F : UpperHalfPlane → ℂ)
    {C : Set UpperHalfPlane} (hC : IsCompact C)
    (hF : ∀ g : CongruenceSubgroup.Gamma0 N, ∀ z, F (g • z) = F z)
    (hcover : ∀ z, F z ≠ 0 →
      ∃ q : Gamma0EffectiveActionKernel20261024z.effectiveGamma0 N,
        Gamma0EffectiveFiniteUnfolding20261025a.effectiveMatrixAction N q z ∈ C) :
    ∃ f : UpperHalfPlane → ℂ, HasCompactSupport f ∧
      ∀ z, complexSeedTrace N f z = F z := by
  obtain ⟨b, K, hK, hbK, hbc, hbs, hb, hbC⟩ := exists_smooth_compact_bump_one hC
  refine ⟨normalizedSeed N b F, normalizedSeed_hasCompactSupport N b F hK hbK, ?_⟩
  intro z
  exact normalizedSeed_trace_eq N b F hK hbK hb
    (fun w hw => by rw [hbC w hw]; norm_num) hF hcover z

end
end ImbalancedChen.Part3.Gamma0CompactCarrierBump20261025a
