import ImbalancedChen.Part3Gamma0ActualHighCuspTail
import ImbalancedChen.Part3Gamma0CompactTensorPoincareLocalFinite
import ImbalancedChen.Part3ActualCuspStripCutoff

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Actual parabolic local finiteness for seeds which vanish BELOW a positive
height but may be nonzero at arbitrarily high heights. The actual integer
matrix denominator bound gives Im(gz) <= max(Im(z),1/Im(z)). Thus the
image height is uniformly bounded on every compact source. An actual
left integral translation puts the real coordinate in [0,1), without
changing the parabolic coset. Properness of the actual integer action
then proves finite parabolic-coset hits into the DERIVED compact strip.
No upper support or local-finiteness assumption is imposed on the seed.
-/

namespace ImbalancedChen.Part3.ActualParabolicHighSeedLocalFinite20261025a

noncomputable section
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane Pointwise
open Gamma0ParabolicBottomRow20261025a Gamma0ParabolicCosetRows20261025a
open Gamma0ParabolicEffectiveDecomposition20261025a GammaInfinityTranslationStrip20261025a
open Gamma0ActualHighCuspTail20261025a
open Gamma0CompactTensorPoincareLocalFinite20261025a
open ActualCuspStripCutoff20261025a

theorem translate_im (k : ℤ) (z : UpperHalfPlane) : (translate k z).im = z.im := by
  rw [translate_eq_vadd, UpperHalfPlane.vadd_im]

/-- The actual matrix denominator bounds image height, including the
parabolic c=0 case, where the height is unchanged. -/
theorem integral_smul_im_le (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    (g • z).im ≤ max z.im (1 / z.im) := by
  by_cases hc : g 1 0 = 0
  · have him : (g • z).im = z.im := by
      obtain ⟨k, hk | hk⟩ := (lowerLeft_zero_iff_signed_translation g).mp hc
      · rw [hk]
        exact translate_im k z
      · rw [hk, UpperHalfPlane.SL_neg_smul]
        exact translate_im k z
    rw [him]
    exact le_max_left _ _
  · exact ((le_div_iff₀ z.im_pos).mpr (im_smul_mul_im_le_one g hc z)).trans
      (le_max_right _ _)

def closedHeightStrip (Y B : ℝ) : Set UpperHalfPlane :=
  {z | z.re ∈ Icc (0 : ℝ) 1 ∧ z.im ∈ Icc Y B}

theorem closedHeightStrip_isCompact (Y B : ℝ) (hY : 0 < Y) :
    IsCompact (closedHeightStrip Y B) := by
  apply UpperHalfPlane.isEmbedding_coe.isCompact_iff.mpr
  have heq : UpperHalfPlane.coe '' closedHeightStrip Y B =
      (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) ''
        (Icc (0 : ℝ) 1 ×ˢ Icc Y B) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(z.re, z.im), hz, by ext <;> rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨⟨p.1, p.2⟩, hY.trans_le hp.2.1⟩, hp, rfl⟩
  rw [heq]
  apply (isCompact_Icc.prod isCompact_Icc).image
  have heqf : (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) =
      fun p => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
    funext p
    ext <;> simp
  rw [heqf]
  fun_prop

/-- A common upper bound on ALL actual integral-matrix image heights of
a compact source, produced from the actual positive coordinate height. -/
theorem compact_image_height_bounded {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ B : ℝ, ∀ z ∈ K, ∀ g : SL(2, ℤ), (g • z).im ≤ B := by
  have hc : Continuous (fun z : UpperHalfPlane => max z.im (1 / z.im)) :=
    UpperHalfPlane.continuous_im.max
      (continuous_const.div UpperHalfPlane.continuous_im (fun z => z.im_ne_zero))
  obtain ⟨B, hB⟩ := hK.bddAbove_image hc.continuousOn
  exact ⟨B, fun z hz g => (integral_smul_im_le g z).trans (hB ⟨z, hz, rfl⟩)⟩

/-- Finitely many actual GammaInfinity-left-cosets reach a high region
from a compact source. The high region itself is NOT compact. -/
theorem finite_parabolic_high_hits (N : ℕ) (Y : ℝ) (hY : 0 < Y)
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    {q : GammaInfinityCosets N |
      ∃ z ∈ K, Y ≤ (parabolicRepresentative N q • z).im}.Finite := by
  obtain ⟨B, hB⟩ := compact_image_height_bounded hK
  have hfinite := finite_gamma0_compact_hits N hK (closedHeightStrip_isCompact Y B hY)
  apply (hfinite.image
    (fun g : CongruenceSubgroup.Gamma0 N => (Quotient.mk'' g : GammaInfinityCosets N))).subset
  rintro q ⟨z, hz, hhigh⟩
  let g := parabolicRepresentative N q
  obtain ⟨k, hk, _⟩ := unique_translate_mem_strip (g • z)
  let g' : CongruenceSubgroup.Gamma0 N := translationGamma N k * g
  have haction : g' • z = translate k (g • z) := by
    simp only [g', mul_smul, translationGamma_smul]
  have hcoset : (Quotient.mk'' g' : GammaInfinityCosets N) = q := by
    rw [← parabolicRepresentative_class N q]
    apply Quotient.sound
    apply (parabolic_orbit_iff_relative N g' g).mpr
    have hrel : g' * g⁻¹ = translationGamma N k := by dsimp [g']; group
    rw [hrel]
    exact (infinityTranslation N k).property
  refine ⟨g', ?_, hcoset⟩
  refine ⟨g' • z, ⟨z, hz, rfl⟩, ?_⟩
  change (g' • z).re ∈ Icc (0 : ℝ) 1 ∧ (g' • z).im ∈ Icc Y B
  rw [haction]
  refine ⟨⟨hk.1, hk.2.le⟩, ?_⟩
  rw [translate_im]
  exact ⟨hhigh, hB z hz (g : SL(2, ℤ))⟩

/-- The conclusion is uniform throughout a genuine neighborhood and
there is no compact-support-above hypothesis on f. -/
theorem high_seed_locally_finite {A : Type*} [Zero A]
    (N : ℕ) (Y : ℝ) (hY : 0 < Y) (f : UpperHalfPlane → A)
    (hbelow : ∀ z, z.im ≤ Y → f z = 0) (z : UpperHalfPlane) :
    ∃ U ∈ 𝓝 z, ∃ S : Finset (GammaInfinityCosets N),
      ∀ w ∈ U, ∀ q ∉ S, f (parabolicRepresentative N q • w) = 0 := by
  obtain ⟨U, hUc, hUn⟩ := exists_compact_mem_nhds z
  have hfinite := finite_parabolic_high_hits N Y hY hUc
  refine ⟨U, hUn, hfinite.toFinset, ?_⟩
  intro w hw q hq
  apply hbelow
  by_contra h
  apply hq
  exact hfinite.mem_toFinset.mpr ⟨w, hw, (lt_of_not_ge h).le⟩

/-- The actual fixed smooth high-tail profile rho=1-chi, zero below Y
and one above 2Y. It is deliberately not upper-compactly supported. -/
def highProfile (Y : ℝ) (y : ℝ) : ℝ := 1 - heightCutoff Y y

theorem highProfile_cinfty (Y : ℝ) : ContDiff ℝ ∞ (highProfile Y) :=
  contDiff_const.sub (heightCutoff_cinfty Y)

theorem highProfile_nonneg (Y y : ℝ) : 0 ≤ highProfile Y y := by
  dsimp [highProfile, heightCutoff]
  linarith [chi_le_one (y / Y)]

theorem highProfile_le_one (Y y : ℝ) : highProfile Y y ≤ 1 := by
  dsimp [highProfile, heightCutoff]
  linarith [chi_nonneg (y / Y)]

theorem highProfile_eq_zero (Y : ℝ) (hY : 0 < Y) (y : ℝ)
    (hy : 0 ≤ y) (hbelow : y ≤ Y) : highProfile Y y = 0 := by
  rw [highProfile, heightCutoff_eq_one hY hy hbelow, sub_self]

theorem highProfile_eq_one (Y : ℝ) (hY : 0 < Y) (y : ℝ)
    (habove : 2 * Y ≤ y) : highProfile Y y = 1 := by
  rw [highProfile, heightCutoff_eq_zero hY habove, sub_zero]

theorem highProfile_seed_locally_finite (N : ℕ) (Y : ℝ) (hY : 0 < Y)
    (z : UpperHalfPlane) :
    ∃ U ∈ 𝓝 z, ∃ S : Finset (GammaInfinityCosets N), ∀ w ∈ U, ∀ q ∉ S,
      highProfile Y (parabolicRepresentative N q • w).im = 0 :=
  high_seed_locally_finite N Y hY (fun w => highProfile Y w.im)
    (fun w hw => highProfile_eq_zero Y hY w.im w.im_pos.le hw) z

end
end ImbalancedChen.Part3.ActualParabolicHighSeedLocalFinite20261025a
