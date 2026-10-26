import ImbalancedChen.Part3StrictHighStripCanonicalMeasure
import ImbalancedChen.Part3Gamma0CarrierMeasurableInverse

/-! Actual measurable high-cusp coordinates and literal radial lifts.
The half-open high charts are proved measurable embeddings using the
countable Gamma0 saturation, not an assumed measurable inverse. Their
extensions vanish exactly off their genuine quotient neighborhoods.
Every high representative has the same radial value by the actual
parabolic deck theorem. SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.GammaInfinityTranslationStrip20261025a
open ImbalancedChen.Part3.Gamma0ParabolicEffectiveDecomposition20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.ActualFrickeQuotientMeasure20261026b
open ImbalancedChen.Part3.PrimeHighCuspQuotientSeparation20261026b
open ImbalancedChen.Part3.PrimeEmbeddedHighCuspStrips20261026b
open ImbalancedChen.Part3.StrictHighStripCanonicalMeasure20261026b

namespace ImbalancedChen.Part3.ActualHighCuspRadialLifts20261026b

theorem infinity_chart_measurableEmbedding (N : ℕ) (Y : ℝ) (hY : 1 ≤ Y) :
    MeasurableEmbedding (infinityHighStripEmbedding N Y hY) where
  injective := (infinityHighStripEmbedding N Y hY).injective
  measurable := (orbitProjection_measurable N).comp measurable_subtype_coe
  measurableSet_image' := by
    intro s hs
    change MeasurableSet ((orbitProjection N ∘
      (Subtype.val : {z : UpperHalfPlane // z ∈ strictHighStrip Y} → UpperHalfPlane)) '' s)
    rw [Set.image_comp]
    apply orbitProjection_image_measurable N
    exact (MeasurableEmbedding.subtype_coe
      (strictHighStrip_measurable Y)).measurableSet_image.mpr hs

theorem zero_chart_measurableEmbedding (p : ℕ) (hp : p.Prime)
    (Y : ℝ) (hY : 1 ≤ Y) :
    MeasurableEmbedding (zeroHighStripEmbedding p hp Y hY) where
  injective := (zeroHighStripEmbedding p hp Y hY).injective
  measurable := (orbitProjection_measurable p).comp
    ((continuous_const_smul (frickeSL p hp.pos)).measurable.comp measurable_subtype_coe)
  measurableSet_image' := by
    intro s hs
    change MeasurableSet ((orbitProjection p ∘ (fun z : UpperHalfPlane =>
      frickeSL p hp.pos • z) ∘ (Subtype.val :
        {z : UpperHalfPlane // z ∈ strictHighStrip Y} → UpperHalfPlane)) '' s)
    rw [Set.image_comp, Set.image_comp]
    apply orbitProjection_image_measurable p
    apply (frickeAction_embedding p hp.pos).measurableSet_image.mpr
    exact (MeasurableEmbedding.subtype_coe
      (strictHighStrip_measurable Y)).measurableSet_image.mpr hs

theorem infinity_chart_range (N : ℕ) (Y : ℝ) (hY : 1 ≤ Y) :
    range (infinityHighStripEmbedding N Y hY) = infinityHighNeighborhood N Y := by
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.1, z.property.2, rfl⟩
  · intro hq
    obtain ⟨z, hz, he⟩ := infinity_high_strip_surjective N Y q hq
    exact ⟨⟨z, hz⟩, he⟩

theorem zero_chart_range (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y) :
    range (zeroHighStripEmbedding p hp Y hY) = zeroHighNeighborhood p hp Y := by
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.1, z.property.2, rfl⟩
  · intro hq
    obtain ⟨z, hz, he⟩ := zero_high_strip_surjective hp Y q hq
    exact ⟨⟨z, hz⟩, he⟩

/-- Genuine radial extension along the actual infinity chart. The
profile is evaluated at native positive height, with zero elsewhere. -/
def infinityRadialLift (N : ℕ) (Y : ℝ) (hY : 1 ≤ Y) (k : ℝ → ℂ) :
    Gamma0OrbitSpace N → ℂ :=
  Function.extend (infinityHighStripEmbedding N Y hY) (fun z => k z.1.im) (fun _ => 0)

/-- Genuine radial extension along the normalized Fricke-zero chart. -/
def zeroRadialLift (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y) (k : ℝ → ℂ) :
    Gamma0OrbitSpace p → ℂ :=
  Function.extend (zeroHighStripEmbedding p hp Y hY) (fun z => k z.1.im) (fun _ => 0)

theorem infinityRadialLift_measurable (N : ℕ) (Y : ℝ) (hY : 1 ≤ Y)
    (k : ℝ → ℂ) (hk : Measurable k) : Measurable (infinityRadialLift N Y hY k) :=
  (infinity_chart_measurableEmbedding N Y hY).measurable_extend
    (hk.comp (UpperHalfPlane.continuous_im.measurable.comp measurable_subtype_coe))
    measurable_const

theorem zeroRadialLift_measurable (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y)
    (k : ℝ → ℂ) (hk : Measurable k) : Measurable (zeroRadialLift p hp Y hY k) :=
  (zero_chart_measurableEmbedding p hp Y hY).measurable_extend
    (hk.comp (UpperHalfPlane.continuous_im.measurable.comp measurable_subtype_coe))
    measurable_const

theorem infinityRadialLift_chart (N : ℕ) (Y : ℝ) (hY : 1 ≤ Y)
    (k : ℝ → ℂ) (z : {z : UpperHalfPlane // z ∈ strictHighStrip Y}) :
    infinityRadialLift N Y hY k (orbitProjection N z.1) = k z.1.im :=
  (infinityHighStripEmbedding N Y hY).injective.extend_apply _ _ z

theorem zeroRadialLift_chart (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y)
    (k : ℝ → ℂ) (z : {z : UpperHalfPlane // z ∈ strictHighStrip Y}) :
    zeroRadialLift p hp Y hY k (orbitProjection p (frickeSL p hp.pos • z.1)) = k z.1.im :=
  (zeroHighStripEmbedding p hp Y hY).injective.extend_apply _ _ z

theorem infinityRadialLift_off (N : ℕ) (Y : ℝ) (hY : 1 ≤ Y) (k : ℝ → ℂ)
    (q : Gamma0OrbitSpace N) (hq : q ∉ infinityHighNeighborhood N Y) :
    infinityRadialLift N Y hY k q = 0 := by
  apply Function.extend_apply'
  change q ∉ range (infinityHighStripEmbedding N Y hY)
  rwa [infinity_chart_range]

theorem zeroRadialLift_off (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y) (k : ℝ → ℂ)
    (q : Gamma0OrbitSpace p) (hq : q ∉ zeroHighNeighborhood p hp Y) :
    zeroRadialLift p hp Y hY k q = 0 := by
  apply Function.extend_apply'
  change q ∉ range (zeroHighStripEmbedding p hp Y hY)
  rwa [zero_chart_range]

/-- All high representatives, without a horizontal interval restriction,
give the literal same height profile. This is pointwise, not merely a.e. -/
theorem infinityRadialLift_high (N : ℕ) (Y : ℝ) (hY : 1 ≤ Y) (k : ℝ → ℂ)
    (z : UpperHalfPlane) (hz : Y < z.im) :
    infinityRadialLift N Y hY k (orbitProjection N z) = k z.im := by
  obtain ⟨n, hn, _⟩ := unique_translate_mem_strip z
  have hh : translate n z ∈ strictHighStrip Y := ⟨hn, by simpa only [translate_im] using hz⟩
  have he : orbitProjection N (translate n z) = orbitProjection N z :=
    orbitProjection_smul N (translationGamma N n) z
  have hv := infinityRadialLift_chart N Y hY k ⟨translate n z, hh⟩
  simpa only [he, translate_im] using hv

theorem zeroRadialLift_high (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y) (k : ℝ → ℂ)
    (z : UpperHalfPlane) (hz : Y < z.im) :
    zeroRadialLift p hp Y hY k (orbitProjection p (frickeSL p hp.pos • z)) = k z.im := by
  obtain ⟨n, hn, _⟩ := unique_translate_mem_strip z
  have hh : translate n z ∈ strictHighStrip Y := ⟨hn, by simpa only [translate_im] using hz⟩
  have he := congrArg (quotientFricke p hp.pos)
    (orbitProjection_smul p (translationGamma p n) z)
  simp only [translationGamma_smul, quotientFricke_projection] at he
  have hv := zeroRadialLift_chart p hp Y hY k ⟨translate n z, hh⟩
  simpa only [he, translate_im] using hv

theorem zeroRadialLift_at_infinity (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y)
    (k : ℝ → ℂ) (z : UpperHalfPlane) (hz : Y < z.im) :
    zeroRadialLift p hp Y hY k (orbitProjection p z) = 0 := by
  apply zeroRadialLift_off
  exact fun hq => (Set.disjoint_left.mp (prime_high_neighborhoods_disjoint hp Y hY))
    ⟨z, hz, rfl⟩ hq

theorem infinityRadialLift_at_zero (p : ℕ) (hp : p.Prime) (Y : ℝ) (hY : 1 ≤ Y)
    (k : ℝ → ℂ) (z : UpperHalfPlane) (hz : Y < z.im) :
    infinityRadialLift p Y hY k (orbitProjection p (frickeSL p hp.pos • z)) = 0 := by
  apply infinityRadialLift_off
  exact fun hq => (Set.disjoint_left.mp (prime_high_neighborhoods_disjoint hp Y hY))
    hq ⟨z, hz, rfl⟩

end ImbalancedChen.Part3.ActualHighCuspRadialLifts20261026b
