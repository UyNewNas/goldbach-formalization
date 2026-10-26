import ImbalancedChen.Part3PrimeCanonicalCoreTwoTailIdentity
import ImbalancedChen.Part3ActualStrictZeroTailMeasure

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Convert the ORIGINAL canonical quotientCore(pY) to common normalized cusp
height Y by removing the ACTUAL infinity annulus Y<height<=pY. Canonical
annulus measure and complex L1/integral transport come from the proved
strict-tail pushforward and actual high-chart uniqueness. -/

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane ENNReal
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0QuotientChartReconstruction20261026b
open ImbalancedChen.Part3.PrimeHighCuspQuotientSeparation20261026b
open ImbalancedChen.Part3.PrimeEmbeddedHighCuspStrips20261026b
open ImbalancedChen.Part3.StrictInfinityHighIndicator20261026b
open ImbalancedChen.Part3.StrictHighStripCanonicalMeasure20261026b
open ImbalancedChen.Part3.ActualStrictInfinityTailMeasure20261026b
open ImbalancedChen.Part3.PrimeTwoCuspCompactCover20261026b
open ImbalancedChen.Part3.PrimeUnequalCuspCoreSaturation20261026b
open ImbalancedChen.Part3.PrimeCanonicalCoreTwoTailIdentity20261026b
open ImbalancedChen.Part3.GammaInfinityTranslationStrip20261025a
open ImbalancedChen.Part3.ActualParabolicHighSeedLocalFinite20261025a
open ImbalancedChen.Part3.CanonicalPlanarL2UnitarySourceOnly
open ImbalancedChen.Part3.MaassWeightedCoordinateL220261024zz
open ImbalancedChen.Part3.RationalCuspHoroballDisks20261026b

namespace ImbalancedChen.Part3.PrimeCommonHeightAnnulusConversion20261026b

def infinityAnnulus (N : ℕ) (Y Z : ℝ) : Set (Gamma0OrbitSpace N) :=
  infinityHighNeighborhood N Y \ infinityHighNeighborhood N Z

def infinityAnnulusStrip (Y Z : ℝ) : Set UpperHalfPlane :=
  strictHighStrip Y ∩ {z | z.im ≤ Z}

theorem infinityHighNeighborhood_antitone (N : ℕ) :
    Antitone (infinityHighNeighborhood N) := by
  intro Y Z hYZ
  rintro q ⟨w, hw, he⟩
  exact ⟨w, hYZ.trans_lt hw, he⟩

theorem infinityAnnulus_measurable (N : ℕ) (Y Z : ℝ)
    (hY : 1 ≤ Y) (hYZ : Y ≤ Z) : MeasurableSet (infinityAnnulus N Y Z) :=
  (infinityHighNeighborhood_measurable N Y hY).diff
    (infinityHighNeighborhood_measurable N Z (hY.trans hYZ))

/-- Uniqueness of the actual parabolic deck gives the true height
dictionary inside a high strip; a quotient height function is not input. -/
theorem projection_mem_higher_infinity_iff (N : ℕ) (Y Z : ℝ)
    (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (z : UpperHalfPlane) (hz : z ∈ strictHighStrip Y) :
    orbitProjection N z ∈ infinityHighNeighborhood N Z ↔ Z < z.im := by
  constructor
  · rintro ⟨w, hw, he⟩
    obtain ⟨k, hk⟩ := (high_projection_eq_iff_translation N Y hY z w hz.2
      (hYZ.trans_lt hw)).mp he.symm
    rw [hk, translate_im]
    exact hw
  · intro hzZ
    exact ⟨z, hzZ, rfl⟩

/-- Restrict the ACTUAL tail pushforward using the proved height
dictionary. This is genuine canonical annulus measure transport. -/
theorem infinityAnnulus_strip_map_measure (N : ℕ) [NeZero N]
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) :
    ((volume : Measure UpperHalfPlane).restrict (infinityAnnulusStrip Y Z)).map
        (orbitProjection N) = (carrierPushforward N).restrict (infinityAnnulus N Y Z) := by
  have hA := infinityAnnulus_measurable N Y Z hY hYZ
  have hpre : orbitProjection N ⁻¹' infinityAnnulus N Y Z ∩ strictHighStrip Y =
      infinityAnnulusStrip Y Z := by
    ext z
    by_cases hz : z ∈ strictHighStrip Y
    · have hlow : orbitProjection N z ∈ infinityHighNeighborhood N Y := ⟨z, hz.2, rfl⟩
      have hhigh := projection_mem_higher_infinity_iff N Y Z hY hYZ z hz
      simp only [mem_inter_iff, mem_preimage, infinityAnnulus, mem_sdiff,
        infinityAnnulusStrip, mem_setOf_eq, hz, and_true, hlow, true_and, hhigh, not_lt]
    · simp only [mem_inter_iff, hz, and_false, infinityAnnulusStrip]
  calc
    _ = (((volume : Measure UpperHalfPlane).restrict (strictHighStrip Y)).restrict
        (orbitProjection N ⁻¹' infinityAnnulus N Y Z)).map (orbitProjection N) := by
      rw [Measure.restrict_restrict ((orbitProjection_measurable N) hA), hpre]
    _ = (((volume : Measure UpperHalfPlane).restrict (strictHighStrip Y)).map
        (orbitProjection N)).restrict (infinityAnnulus N Y Z) :=
      (Measure.restrict_map (orbitProjection_measurable N) hA).symm
    _ = _ := by
      rw [strict_infinity_strip_map_measure N Y hY, Measure.restrict_restrict hA,
        inter_eq_self_of_subset_left (sdiff_subset : infinityAnnulus N Y Z ⊆
          infinityHighNeighborhood N Y)]

theorem infinityAnnulus_volume (N : ℕ) [NeZero N] (Y Z : ℝ)
    (hY : 1 ≤ Y) (hYZ : Y ≤ Z) :
    carrierPushforward N (infinityAnnulus N Y Z) =
      ENNReal.ofReal (1 / Y) - ENNReal.ofReal (1 / Z) := by
  rw [infinityAnnulus, measure_sdiff (infinityHighNeighborhood_antitone N hYZ)
    (infinityHighNeighborhood_measurable N Z (hY.trans hYZ)).nullMeasurableSet
    (by rw [strict_infinity_tail_volume N Z (hY.trans hYZ)]; exact ENNReal.ofReal_ne_top),
    strict_infinity_tail_volume N Y hY, strict_infinity_tail_volume N Z (hY.trans hYZ)]

theorem infinityAnnulus_integrable_iff (N : ℕ) [NeZero N]
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z)
    (F : Gamma0OrbitSpace N → ℂ) (hF : Measurable F) :
    IntegrableOn F (infinityAnnulus N Y Z) (carrierPushforward N) ↔
      IntegrableOn (fun z => F (orbitProjection N z)) (infinityAnnulusStrip Y Z) := by
  have h := integrable_map_measure hF.aestronglyMeasurable
    (orbitProjection_measurable N).aemeasurable
    (μ := (volume : Measure UpperHalfPlane).restrict (infinityAnnulusStrip Y Z))
  rwa [infinityAnnulus_strip_map_measure N Y Z hY hYZ] at h

theorem infinityAnnulus_integral (N : ℕ) [NeZero N]
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z)
    (F : Gamma0OrbitSpace N → ℂ) (hF : Measurable F) :
    (∫ q in infinityAnnulus N Y Z, F q ∂carrierPushforward N) =
      ∫ z in infinityAnnulusStrip Y Z, F (orbitProjection N z) := by
  have h := integral_map (orbitProjection_measurable N).aemeasurable hF.aestronglyMeasurable
    (μ := (volume : Measure UpperHalfPlane).restrict (infinityAnnulusStrip Y Z))
  rwa [infinityAnnulus_strip_map_measure N Y Z hY hYZ] at h

theorem infinityAnnulusStrip_chart_map_measure (Y Z : ℝ) :
    ((volume : Measure UpperHalfPlane).restrict (infinityAnnulusStrip Y Z)).map chartMap =
      ((volume : Measure ℝ).restrict (Ico (0 : ℝ) 1)).prod
        (verticalWeightedMeasure.restrict (Ioc Y Z)) := by
  have hpre : chartMap ⁻¹' (Ico (0 : ℝ) 1 ×ˢ Ioc Y Z) = infinityAnnulusStrip Y Z := by
    ext z
    change (z.re ∈ Ico (0 : ℝ) 1 ∧ Y < z.im ∧ z.im ≤ Z) ↔
      ((z.re ∈ Ico (0 : ℝ) 1 ∧ Y < z.im) ∧ z.im ≤ Z)
    tauto
  rw [← hpre, ← Measure.restrict_map chartMap_measurableEmbedding.measurable
    (measurableSet_Ico.prod measurableSet_Ioc),
    ActualHighStripCircleMeasure20261026b.canonical_chart_map_measure,
    chartMeasure_eq_product, ← Measure.prod_restrict]

theorem infinityAnnulus_coordinate_integral (N : ℕ) [NeZero N]
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z)
    (F : Gamma0OrbitSpace N → ℂ) (hF : Measurable F) :
    (∫ q in infinityAnnulus N Y Z, F q ∂carrierPushforward N) =
      ∫ a : ℝ × ℝ, chartPullback (fun z => F (orbitProjection N z)) a
        ∂(((volume : Measure ℝ).restrict (Ico (0 : ℝ) 1)).prod
          (verticalWeightedMeasure.restrict (Ioc Y Z))) := by
  rw [infinityAnnulus_integral N Y Z hY hYZ F hF]
  have h := chartMap_measurableEmbedding.integral_map
    (μ := (volume : Measure UpperHalfPlane).restrict (infinityAnnulusStrip Y Z))
    (g := chartPullback (fun z => F (orbitProjection N z)))
  rw [infinityAnnulusStrip_chart_map_measure Y Z] at h
  simpa only [chartMap, chartPullback_at_upper] using h.symm

private theorem prime_mul_height_ge (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y) :
    Y ≤ (p : ℝ) * Y ∧ (p : ℝ) ≤ (p : ℝ) * Y := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hY0 : (0 : ℝ) ≤ Y := (by norm_num : (0 : ℝ) ≤ 1).trans hY
  constructor
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hp1 hY0
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hY
      ((by norm_num : (0 : ℝ) ≤ 1).trans hp1)

/-- Exact full-set conversion. The annulus is in the infinity cusp only;
the normalized zero cusp already has common height Y when T=pY. -/
theorem unequal_truncation_eq_common_union_annulus (p : ℕ) (hp : p.Prime)
    (Y : ℝ) (hY : 1 ≤ Y) :
    unequalCuspTruncation p hp ((p : ℝ) * Y) =
      twoCuspTruncation p hp Y ∪ infinityAnnulus p Y ((p : ℝ) * Y) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hquot : ((p : ℝ) * Y) / (p : ℝ) = Y := by field_simp [hpR]
  have hsub := infinityHighNeighborhood_antitone p (prime_mul_height_ge p hp Y hY).1
  have hdis := Set.disjoint_left.mp (prime_high_neighborhoods_disjoint hp Y hY)
  ext q
  simp only [unequalCuspTruncation, hquot, twoCuspTruncation, infinityAnnulus,
    mem_compl_iff, mem_union, mem_sdiff]
  have hinc : q ∈ infinityHighNeighborhood p ((p : ℝ) * Y) →
      q ∈ infinityHighNeighborhood p Y := fun h => hsub h
  have hsep : ¬ (q ∈ infinityHighNeighborhood p Y ∧ q ∈ zeroHighNeighborhood p hp Y) :=
    fun h => hdis h.1 h.2
  tauto

theorem common_truncation_disjoint_annulus (p : ℕ) (hp : p.Prime) (Y Z : ℝ) :
    Disjoint (twoCuspTruncation p hp Y) (infinityAnnulus p Y Z) := by
  apply Set.disjoint_left.mpr
  intro q hq ha
  exact hq (Or.inl ha.1)

theorem quotientCore_prime_height_ae_eq_common_union_annulus (p : ℕ) [NeZero p]
    (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y) :
    quotientCore p ((p : ℝ) * Y) =ᵐ[carrierPushforward p]
      twoCuspTruncation p hp Y ∪ infinityAnnulus p Y ((p : ℝ) * Y) := by
  have h := quotientCore_ae_eq_unequal_truncation p hp ((p : ℝ) * Y)
    (prime_mul_height_ge p hp Y hY).2
  rwa [unequal_truncation_eq_common_union_annulus p hp Y hY] at h

/-- Literal removal of the actual infinity annulus converts the original
canonical core to common height, with precisely the same canonical a.e.
qualification required by the reduced carrier. -/
theorem quotientCore_sdiff_annulus_ae_eq_common (p : ℕ) [NeZero p]
    (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y) :
    quotientCore p ((p : ℝ) * Y) \ infinityAnnulus p Y ((p : ℝ) * Y)
      =ᵐ[carrierPushforward p] twoCuspTruncation p hp Y := by
  filter_upwards [quotientCore_prime_height_ae_eq_common_union_annulus p hp Y hY] with q hq
  apply propext
  change (q ∈ quotientCore p ((p : ℝ) * Y) ∧
    q ∉ infinityAnnulus p Y ((p : ℝ) * Y)) ↔ q ∈ twoCuspTruncation p hp Y
  rw [hq]
  have hd := Set.disjoint_left.mp
    (common_truncation_disjoint_annulus p hp Y ((p : ℝ) * Y))
  simp only [mem_union]
  constructor
  · exact fun h => h.1.resolve_right h.2
  · exact fun h => ⟨Or.inl h, fun ha => hd h ha⟩

/-- Honest canonical integral conversion for an ACTUALLY integrable
original quotientCore observable. The removed piece is paid by the true
annulus pushforward, and its finite top boundary remains included. -/
theorem common_height_integral_eq_core_sub_annulus (p : ℕ) [NeZero p]
    (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y)
    (F : Gamma0OrbitSpace p → ℂ) (hF : Measurable F)
    (hL1 : IntegrableOn F (quotientCore p ((p : ℝ) * Y)) (carrierPushforward p)) :
    (∫ q in twoCuspTruncation p hp Y, F q ∂carrierPushforward p) =
      (∫ q in quotientCore p ((p : ℝ) * Y), F q ∂carrierPushforward p) -
        ∫ z in infinityAnnulusStrip Y ((p : ℝ) * Y), F (orbitProjection p z) := by
  have he := quotientCore_prime_height_ae_eq_common_union_annulus p hp Y hY
  have hu := (integrableOn_congr_set_ae he).mp hL1
  have hi := setIntegral_congr_set (f := F) he
  rw [setIntegral_union (common_truncation_disjoint_annulus p hp Y ((p : ℝ) * Y))
    (infinityAnnulus_measurable p Y ((p : ℝ) * Y) hY (prime_mul_height_ge p hp Y hY).1)
    (hu.mono_set subset_union_left) (hu.mono_set subset_union_right),
    infinityAnnulus_integral p Y ((p : ℝ) * Y) hY (prime_mul_height_ge p hp Y hY).1 F hF] at hi
  rw [hi]
  abel

theorem core_volume_eq_common_add_annulus (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y : ℝ) (hY : 1 ≤ Y) :
    carrierPushforward p (quotientCore p ((p : ℝ) * Y)) =
      carrierPushforward p (twoCuspTruncation p hp Y) +
        (ENNReal.ofReal (1 / Y) - ENNReal.ofReal (1 / ((p : ℝ) * Y))) := by
  rw [measure_congr (quotientCore_prime_height_ae_eq_common_union_annulus p hp Y hY),
    measure_union (common_truncation_disjoint_annulus p hp Y ((p : ℝ) * Y))
      (infinityAnnulus_measurable p Y ((p : ℝ) * Y) hY (prime_mul_height_ge p hp Y hY).1),
    infinityAnnulus_volume p Y ((p : ℝ) * Y) hY (prime_mul_height_ge p hp Y hY).1]

end ImbalancedChen.Part3.PrimeCommonHeightAnnulusConversion20261026b
